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

namespace hello {
   // clang-format off
   struct prefix : pegtl::string<'H', 'e', 'l', 'l', 'o', ',', ' '> {};
   struct name : pegtl::plus<pegtl::alpha> {};
   struct grammar : pegtl::seq<prefix, name, pegtl::one<'!'>, pegtl::eof> {};
   // clang-format on

   template<typename Rule>
   struct action {};

   template<>
   struct action<name>
   {
      template<typename ActionInput>
      static void apply(const ActionInput& in, std::string& v) {
         v = in.string();
      }
   };
}

int main(int argc, char** argv) {
   if(argc > 1) {
      std::string name;

      pegtl::argv_input in(argv, 1);
      if(pegtl::parse<hello::grammar, hello::action>(in, name)) {
         std::cout << "Good bye, " << name << "!" << std::endl;
      }
      else {
         std::cerr << "I don't understand." << std::endl;
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
