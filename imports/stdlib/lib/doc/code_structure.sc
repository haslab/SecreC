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
@page code_stucture Code structure
@brief code structure in SecreC

A SecreC program starts with a series of global value definitions which are followed by a series of function definitions. Other kinds of statements are not allowed in the global program scope. A SecreC program has to define a function called “main” taking no arguments and returning no value. This function is
called when the program is executed by the Sharemind machine. There are two types of comments which are treated as white-space. The single line comments start
with two consecutive forwards slashes `//` and continue until a new line. Multi line comments start with a consecutive forward slash and asterisk and continue up until and including a consecutive asterisk and forward slash. New comments are not started if the starting characters are found within string literals or other comments. Comments count as a white-space, and can be used to separate tokens.

Listing 6.1: Trivial program
\code

	void main () {
		return ;
	}

\endcode
*/
