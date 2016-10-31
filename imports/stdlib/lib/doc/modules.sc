/*
 * Copyright (C) 2015 Cybernetica
 *
 * Research/Commercial License Usage
 * Licensees holding a valid Research License or Commercial License
 * for the Software may use this file according to the written 
 * agreement between you and Cybernetica.
 *
 * GNU Lesser General Public License Usage
 * Alternatively, this file may be used under the terms of the GNU Lesser
 * General Public License version 3 as published by the Free Software
 * Foundation and appearing in the file LICENSE.LGPLv3 included in the
 * packaging of this file.  Please review the following information to
 * ensure the GNU Lesser General Public License version 3 requirements
 * will be met: http://www.gnu.org/licenses/lgpl-3.0.html.
 *
 * For further information, please contact us at sharemind@cyber.ee.
 */

/**
@page ref_modules Modules
@brief Modules in SecreC

@section ref_modules Modules

SecreC supports very simple module system. A module name can be declared with **module** keyword, and module can be imported using a **import** keyword. Filename of the module must match with the modules name. Imported modules are searched within paths specified to the compiler. Importing a module will make all of the global symbols defined within the imported module visible. Modules can not be separately compiled and linked, they simply offer a way to break code into components.

Listing 6.33: Module syntax
\code
module shared3p;
import common;
...
\endcode

Imported symbols will not be exported by a module. If an imported symbol is redefined, a type error is raised. Procedures and templates with the same name but different parameters are considered to be different symbols.

*/
