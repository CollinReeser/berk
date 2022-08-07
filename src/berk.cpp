// Copyright (c) 2014-2022 Dr. Colin Hirsch and Daniel Frey
// Distributed under the Boost Software License, Version 1.0.
// (See accompanying file LICENSE_1_0.txt or copy at https://www.boost.org/LICENSE_1_0.txt)

#include <iostream>
#include <string>

#include <tao/pegtl.hpp>

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

   struct hex_num_abs :
      seq<
         one<'0'>,
         one<'x', 'X'>,
         plus<
            one<
               '0', '1', '2', '3', '4', '5', '6', '7', '8', '9',
               'a', 'b', 'c', 'd', 'e', 'f',
               'A', 'B', 'C', 'D', 'E', 'F'
            >
         >
      > {};

   struct bin_num_abs :
      seq<
         one<'b'>,
         plus<one<'0', '1'>>
      > {};

   struct oct_num_abs :
      seq<
         one<'0'>,
         plus<one<'0', '1', '2', '3', '4', '5', '6', '7'>>
      > {};

   struct dec_num_abs :
      seq<
         one<'1', '2', '3', '4', '5', '6', '7', '8', '9'>,
         star<digit>
      > {};

   struct integer :
      seq<
         opt<one<'+', '-'>>,
         sor<hex_num_abs, bin_num_abs, oct_num_abs, dec_num_abs>
      >
      {};

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
      else if(
         pegtl::argv_input in(argv, 1);
         pegtl::parse<hello::integer, hello::action>(in, capture)
      ) {
         std::cout << capture << std::endl;
      }
      else {
         std::cerr << "I dont understand." << std::endl;
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
