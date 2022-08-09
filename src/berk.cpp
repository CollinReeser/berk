// Copyright (c) 2014-2022 Dr. Colin Hirsch and Daniel Frey
// Distributed under the Boost Software License, Version 1.0.
// (See accompanying file LICENSE_1_0.txt or copy at https://www.boost.org/LICENSE_1_0.txt)

#include <charconv>
#include <iostream>
#include <string>

#include <tao/pegtl.hpp>
#include <tao/pegtl/contrib/analyze.hpp>
#include <tao/pegtl/contrib/parse_tree.hpp>
#include <tao/pegtl/contrib/parse_tree_to_dot.hpp>
#include <tao/pegtl/contrib/trace.hpp>

#include "llvm/ADT/APFloat.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/Verifier.h"

#include "config.h"

// fn main(): i32 {
//     return 2;
// }

/*
   file := func_def*
   func_def := func_sig ws* "{" func_body ws* "}"

   func_sig := "fn" ws+ ident ws* "(" ws* args* ws* ")" ret_sect?

   func_body := stmt*

   stmt := "return" ws+ [0-9]+ ws* ";"
*/

namespace pegtl = tao::pegtl;

using namespace tao::pegtl;

namespace hello {
   // clang-format off
   struct prefix : pegtl::string<'H', 'e', 'l', 'l', 'o', ',', ' '> {};
   struct name : pegtl::plus<pegtl::alpha> {};
   struct grammar : pegtl::seq<prefix, name, pegtl::one<'!'>, pegtl::eof> {};
   // clang-format on

   template<typename Rule>
   struct action : nothing<Rule> {};

   template<>
   struct action<name>
   {
      template<typename ActionInput>
      static void apply(const ActionInput &in, std::string &v) {
         v = in.string();
      }
   };

   struct ws_opt :
      star<space>
      {};

   struct ws_req :
      plus<space>
      {};

   struct boundary :
      sor<
         ws_req,
         not_at<
            identifier_other
         >
      >
      {};

   struct hex_num_abs :
      seq<
         one<'0'>,
         one<'x', 'X'>,
         plus<xdigit>
      >
      {};

   struct bin_num_abs :
      seq<
         one<'b'>,
         plus<one<'0', '1'>>
      >
      {};

   struct oct_num_abs :
      seq<
         one<'0'>,
         plus<range<'0', '7'>>
      >
      {};

   struct dec_num_abs :
      seq<
         range<'1', '9'>,
         star<digit>
      >
      {};

   struct integer :
      seq<
         opt<one<'+', '-'>>,
         sor<hex_num_abs, bin_num_abs, oct_num_abs, dec_num_abs>
      >
      {};

   struct ident :
      seq<
         identifier_first,
         star<identifier_other>
      >
      {};

   struct expr :
      sor<
         integer
      >
      {};

   struct stmt_terminal :
      seq<
         one<';'>,
         ws_opt
      >
      {};

   struct return_stmt :
      seq<
         keyword<'r', 'e', 't', 'u', 'r', 'n'>,
         boundary,
         expr,
         boundary,
         stmt_terminal
      >
      {};

   struct stmt :
      sor<
         return_stmt
      >
      {};

   struct type :
      sor<
         string<'i', '3', '2'>,
         string<'u', '3', '2'>,
         string<'i', '6', '4'>,
         string<'u', '6', '4'>
      >
      {};

   struct ident_type_decl :
      seq<
         ident,
         boundary,
         one<':'>,
         ws_opt,
         type
      >
      {};

   struct func_args :
      opt<
         sor<
            seq<
               ident_type_decl,
               boundary,
               star<
                  one<','>,
                  ws_opt,
                  ident_type_decl,
                  boundary
               >
            >,
            seq<
               ident_type_decl,
               boundary
            >
         >
      >
      {};

   struct func_sig :
      seq<
         string<'f', 'n'>,
         ws_req,
         ident,
         boundary,
         one<'('>,
         ws_opt,
         func_args,
         boundary,
         one<')'>,
         ws_opt,
         opt<
            one<':'>,
            ws_opt,
            type,
            boundary
         >
      >
      {};

   struct func_body :
      star<stmt>
      {};

   struct func_def :
      seq<
         func_sig,
         one<'{'>,
         ws_opt,
         func_body,
         boundary,
         one<'}'>,
         ws_opt
      >
      {};

   struct file :
      seq<
         ws_opt,
         star<
            func_def,
            ws_opt
         >,
         ws_opt,
         eof
      >
      {};

   // Code to execute just after the named rule succeeds.
   template<>
   struct action<bin_num_abs>
   {
      template<typename ActionInput>
      static void apply(const ActionInput& in, std::string& v) {
         v = "bin: " + in.string();
      }
   };

   template<>
   struct action<hex_num_abs>
   {
      template<typename ActionInput>
      static void apply(const ActionInput& in, std::string& v) {
         v = "hex: " + in.string();
      }
   };

   template<>
   struct action<oct_num_abs>
   {
      template<typename ActionInput>
      static void apply(const ActionInput& in, std::string& v) {
         v = "oct: " + in.string();
      }
   };

   template<>
   struct action<dec_num_abs>
   {
      template<typename ActionInput>
      static void apply(const ActionInput& in, std::string& v) {
         v = "dec: " + in.string();
      }
   };

   template<>
   struct action<ident>
   {
      template<typename ActionInput>
      static void apply(const ActionInput& in, std::string& v) {
         v = "ident: " + in.string();
      }
   };

   // All rules other than these will be dropped from the AST.
   template<typename Rule>
   using selector = tao::pegtl::parse_tree::selector<
      Rule,
      tao::pegtl::parse_tree::store_content::on<
         hex_num_abs,
         bin_num_abs,
         oct_num_abs,
         dec_num_abs,
         expr,
         return_stmt,
         ident_type_decl,
         ident,
         func_args,
         type,
         func_sig,
         func_body,
         file,
         func_def
      >
   >;
}

constexpr uint32_t type_hash(const std::string_view &data) noexcept {
   uint32_t hash = 5381;

   for(const auto c : data) {
      hash = ((hash << 5) + hash) + c;
   }

   return hash;
}

template<typename Node>
void generate_llvm(const Node &node) {
   if (node->is_root()) {
      std::cout << "Root is root!" << std::endl;

      for (const auto &node : node->children) {
         generate_llvm(node);
      }

      return;
   }

   std::cout << "Node: [" << node->type << "]" << std::endl;

   switch (type_hash(node->type)) {
   case type_hash("hello::file"): {
      for (const auto &func_def : node->children) {
         generate_llvm(func_def);
      }

      break;
   }
   case type_hash("hello::func_def"): {
      const auto &func_sig {node->children[0]};

      const std::string_view func_name {
         func_sig->children[0]->string_view()
      };

      const auto &func_body {node->children[1]};

      generate_llvm(func_body);

      break;
   }
   case type_hash("hello::func_body"): {
      for (const auto &stmt : node->children) {
         generate_llvm(stmt);
      }

      break;
   }
   case type_hash("hello::return_stmt"): {
      const auto &expr {node->children[0]};

      generate_llvm(expr);

      break;
   }
   case type_hash("hello::expr"): {
      const auto &sub_expr {node->children[0]};

      generate_llvm(sub_expr);

      break;
   }
   case type_hash("hello::dec_num_abs"): {
      const std::string_view int_str {node->string_view()};

      int result {0};

      const auto [ptr, ec] {
         std::from_chars(
            int_str.data(),
            int_str.data() + int_str.size(),
            result
         )
      };

      if (ec == std::errc()) {
         std::cout << "  Conversion: [" << result << "]" << std::endl;
      }
      else if (ec == std::errc::invalid_argument) {
         std::cout
            << "  Conversion failed, NaN [" << int_str << "]" << std::endl;
      }
      else if (ec == std::errc::result_out_of_range) {
         std::cout
            << "  Conversion failed, out-of-range [" << int_str << "]"
            << std::endl;
      }

      break;
   }
   default:
      std::cout << "Unknown case!" << std::endl;
      break;
   }

   return;
}

int main(int argc, char** argv) {
   if(argc > 1) {
      std::string capture;

      if(
         pegtl::argv_input in(argv, 1);
         pegtl::parse<hello::grammar, hello::action>(in, capture)
      ) {
         std::cout << "Good bye, " << capture << "!" << std::endl;
      }
      // Detect issues with the grammar definition itself.
      else if (pegtl::analyze<hello::file>(1) != 0) {
         std::cout << "Grammar issues encountered, see above." << std::endl;
      }
      // Attempt to parse the input.
      else if(
         pegtl::argv_input in(argv, 1);
         pegtl::parse<hello::file, hello::action>(in, capture)
      ) {
         std::cout << "hello::file: " << capture << std::endl;
      }
      else if(
         pegtl::argv_input in(argv, 1);
         pegtl::parse<hello::func_def, hello::action>(in, capture)
      ) {
         std::cout << "hello::func_def: " << capture << std::endl;
      }
      else if(
         pegtl::argv_input in(argv, 1);
         pegtl::parse<hello::func_sig, hello::action>(in, capture)
      ) {
         std::cout << "hello::func_sig: " << capture << std::endl;
      }
      else if(
         pegtl::argv_input in(argv, 1);
         pegtl::parse<hello::stmt, hello::action>(in, capture)
      ) {
         std::cout << "hello::stmt: " << capture << std::endl;
      }
      else if(
         pegtl::argv_input in(argv, 1);
         pegtl::parse<hello::integer, hello::action>(in, capture)
      ) {
         std::cout << "hello::integer: " << capture << std::endl;
      }
      else {
         std::cerr << "I dont understand." << std::endl;
      }

      // Trace parse.
      if (
         pegtl::argv_input in(argv, 1);
         pegtl::standard_trace<hello::file, hello::action>(in, capture)
      ) {
         std::cout << "traced hello::file: " << capture << std::endl;
      }
      else {
         std::cerr << "I dont understand." << std::endl;
      }

      // Pretty-print parse tree with given filter.
      {
         pegtl::argv_input in(argv, 1);
         const auto root {parse_tree::parse<hello::file, hello::selector>(in)};

         if (root) {
            parse_tree::print_dot(std::cout, *root);

            generate_llvm(root);
         }
      }
   }
   else {
      std::cout
         << "v" << berk_VERSION_MAJOR
         << "." << berk_VERSION_MINOR
         << "." << berk_VERSION_PATCH
         << std::endl;
   }
}
