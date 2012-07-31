// This file is a script that can be executed with the F# Interactive.  
// It can be used to explore and test the library project.
// Note that script files will not be part of the project build.

#load "Chip8.fs"

open System
open Emulators

let rom = IO.File.ReadAllBytes(@"c:\appdev\Emulators\Chip8\tetris.c8")

Chip8.start rom

