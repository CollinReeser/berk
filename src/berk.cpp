// Copyright (c) 2014-2022 Dr. Colin Hirsch and Daniel Frey
// Distributed under the Boost Software License, Version 1.0.
// (See accompanying file LICENSE_1_0.txt or copy at https://www.boost.org/LICENSE_1_0.txt)

#include <iostream>
#include <string>

#include <tao/pegtl.hpp>
#include <tao/pegtl/contrib/analyze.hpp>
#include <tao/pegtl/contrib/parse_tree.hpp>
#include <tao/pegtl/contrib/parse_tree_to_dot.hpp>
#include <tao/pegtl/contrib/trace.hpp>

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
