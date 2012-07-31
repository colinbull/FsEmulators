namespace Emulators

open System

module Chip8 = 
    
    let private rand = System.Random(DateTime.Now.Ticks |> int)
    let mutable private memory = Array.init 4096 (fun _ -> 0uy)
    let mutable private display = Array.init 2048 (fun _ -> 0uy)
    let mutable private registers = Array.init 16 (fun _ -> 0uy)
    let mutable private stack = Array.init 16 (fun _ -> 0)
    let mutable private key = Array.init 16 (fun _ -> 0uy)

    let private indexRegister = ref 0
    let private delayTimer = ref 0
    let private soundTimer = ref 0 
    let private stackPointer = ref 0
    let private drawFlag = ref false
    let private keyPress = ref false

    let mutable private playSound = (fun () -> ())
    

    let private fontset = 
        [|
             0xF0us; 0x90us; 0x90us; 0x90us; 0xF0us; // 0
             0x20us; 0x60us; 0x20us; 0x20us; 0x70us; // 1
             0xF0us; 0x10us; 0xF0us; 0x80us; 0xF0us; // 2
             0xF0us; 0x10us; 0xF0us; 0x10us; 0xF0us; // 3
             0x90us; 0x90us; 0xF0us; 0x10us; 0x10us; // 4
             0xF0us; 0x80us; 0xF0us; 0x10us; 0xF0us; // 5
             0xF0us; 0x80us; 0xF0us; 0x90us; 0xF0us; // 6
             0xF0us; 0x10us; 0x20us; 0x40us; 0x40us; // 7
             0xF0us; 0x90us; 0xF0us; 0x90us; 0xF0us; // 8
             0xF0us; 0x90us; 0xF0us; 0x10us; 0xF0us; // 9
             0xF0us; 0x90us; 0xF0us; 0x90us; 0x90us; // A
             0xE0us; 0x90us; 0xE0us; 0x90us; 0xE0us; // B
             0xF0us; 0x80us; 0x80us; 0x80us; 0xF0us; // C
             0xE0us; 0x90us; 0x90us; 0x90us; 0xE0us; // D
             0xF0us; 0x80us; 0xF0us; 0x80us; 0xF0us; // E
             0xF0us; 0x80us; 0xF0us; 0x80us; 0x80us; // F
        |]

    let private sound() = 
        if !soundTimer > 0 then playSound(); decr(soundTimer)

    let private delay() =  
        if !delayTimer > 0 then decr(delayTimer)
    
    let rec private loop counter =
        let opCode = (memory.[counter] <<< 8 ||| memory.[counter + 1]) |> int
        
        delay(); sound()
        
        let regX = (opCode &&& 0x0F00) >>> 8
        let regY = (opCode &&& 0x00F0) >>> 4

        match opCode &&& 0xF000 with
        | 0x0000 ->
            match opCode &&& 0x000F with
            | 0x0000 -> // 0x00E0: Clears the screen
                display <- Array.zeroCreate 2048
                drawFlag := true
                loop (counter + 2)
            | 0x000E -> // 0x00EE: Returns from subroutine
                decr(stackPointer)
                loop (stack.[!stackPointer] + 2)
            | _ -> failwithf "Unknown opcode [0x0000] %X" opCode
        | 0x1000 -> // 0x1NNN: Jumps to address NNN
            loop (opCode &&& 0x0FFF)
        | 0x2000 -> // 0x2NNN: Calls subroutine at NNN.
            stack.[!stackPointer] <- counter
            incr(stackPointer)
            loop (opCode &&& 0x0FFF)
        | 0x3000 -> // 0x3XNN: Skips the next instruction if VX equals NN
            loop (counter + 2)
        | 0x4000 -> // 0x4XNN: Skips the next instruction if VX doesn't equal NN
            loop (counter + 2)
        | 0x5000 -> // 0x5XY0: Skips the next instruction if VX equals VY.
            loop (counter + 2)
        | 0x6000 -> // 0x6XNN: Sets VX to NN.
            loop (counter + 2)
        | 0x7000 -> // 0x7XNN: Adds NN to VX.
            loop (counter + 2)
        | 0x8000 ->
            match opCode &&& 0x000F with
            | 0x0000 -> // 0x8XY0: Sets VX to the value of VY
                registers.[regX] <- registers.[regY]
                loop (counter + 2)
            | 0x0001 -> // 0x8XY1: Sets VX to "VX OR VY"
                registers.[regX] <- (registers.[regX] ||| registers.[regY])
                loop (counter + 2)
            | 0x0002 -> // 0x8XY2: Sets VX to "VX AND VY"
                registers.[regX] <- (registers.[regX] &&& registers.[regY])
                loop (counter + 2)
            | 0x0003 -> // 0x8XY3: Sets VX to "VX XOR VY"
                registers.[regX] <- (registers.[regX] ^^^ registers.[regY])
            | 0x0004 -> // 0x8XY4: Adds VY to VX. VF is set to 1 when there's a carry, and to 0 when there isn't	
                if registers.[regY] > ((0xFF |> byte) - registers.[regX])
                then registers.[0xF] <- 1uy
                else registers.[0xF] <- 0uy
                registers.[regX] <- registers.[regX] + registers.[regY]
                loop (counter + 2)
            | 0x0005 -> // 0x8XY5: VY is subtracted from VX. VF is set to 0 when there's a borrow, and 1 when there isn't
                if registers.[regY] > registers.[regX]
                then registers.[0xF] <- 1uy
                else registers.[0xF] <- 0uy
                registers.[regX] <- registers.[regX] - registers.[regY]
                loop (counter + 2)
            | 0x0006 -> // 0x8XY6: Shifts VX right by one. VF is set to the value of the least significant bit of VX before the shift
                registers.[0xF] <- ((registers.[regX] |> int) &&& 0x1) |> byte
                registers.[regX] <- registers.[regX] >>> 1
                loop (counter + 2)
            | 0x0007 -> // 0x8XY7: Sets VX to VY minus VX. VF is set to 0 when there's a borrow, and 1 when there isn't
                if registers.[regY] > registers.[regX]
                then registers.[0xF] <- 1uy
                else registers.[0xF] <- 0uy
                registers.[regY] <- -(registers.[regX] |> int) |> byte
                loop (counter + 2)
            | 0x000E -> // 0x8XYE: Shifts VX left by one. VF is set to the value of the most significant bit of VX before the shift
                registers.[0xF] <- ((registers.[regX] |> int) >>> 7) |> byte
                registers.[regX] <- registers.[regX] <<< 1
                loop (counter + 2)
            | _ -> failwithf "Unknown opcode [0x8000] %X" opCode
        | 0x9000 -> // 0x9XY0: Skips the next instruction if VX doesn't equal VY
           if registers.[regX] <> registers.[regY]
           then loop (counter + 4)
           else loop (counter + 2)
        | 0xA000 -> // ANNN: Sets I to the address NNN
           indexRegister := opCode &&& 0x0FFF
           loop (counter + 2)  
        | 0xB000 -> // BNNN: Jumps to the address NNN plus V0
           loop ((opCode &&& 0x0FFF) + (registers.[0] |> int))
        | 0xC000 -> // CXNN: Sets VX to a random number and NN
           registers.[regX] <- ((rand.Next() % 0xFF) &&& (opCode &&& 0x00FF)) |> byte
           loop (counter + 2)
        | 0xD000 -> //DXYN Draws a sprite at (X,Y) with (8,N) dimensions read from I; VF is set to 1 if any pixels are unset
           let height = (opCode &&& 0x000F) - 1
           let xval, yval = registers.[regX] |> int, registers.[regY] |> int
           for y in 0..height do
               let pixel = memory.[!indexRegister + y] |> int
               for x in 0 .. 7 do
                   if (pixel &&& (0x80 >>> x)) = 0
                   then ()
                   elif display.[(xval + x + ((yval + y) * 64))] = 1uy then registers.[0xF] <- 1uy
                   display.[(xval + x + ((yval + y) * 64))] <- display.[(xval + x + ((yval + y) * 64))] ^^^ 1uy
           drawFlag := true
           loop (counter + 2)
        | 0xE000 ->
            match opCode &&& 0x00FF with
            | 0x009E -> // EX9E: Skips the next instruction if the key stored in VX is pressed
                if key.[registers.[regX] |> int] <> 0uy
                then loop (counter + 4)
                else loop (counter + 2)
            | 0x00A1 -> // EXA1: Skips the next instruction if the key stored in VX isn't pressed
                if key.[registers.[regX] |> int] = 0uy
                then loop (counter + 4)
                else loop (counter + 2)
            | _ -> failwithf "Unknown opcode [0xE000] %X" opCode
        | 0xF000 ->
            match opCode &&& 0x00FF with
            | 0x0007 -> // FX07: Sets VX to the value of the delay timer
                registers.[regX] <- (!delayTimer |> byte)
                loop (counter + 2)
            | 0x000A -> // FX0A: A key press is awaited, and then stored in VX
                for i in 0..15 do
                    if key.[i] <> 0uy
                    then registers.[regX] <- (i |> byte); keyPress := true
                if (not <| !keyPress) 
                then loop counter
                else loop (counter + 2)
            | 0x0015 -> // FX15: Sets the delay timer to VX
                delayTimer := registers.[regX] |> int
                loop (counter + 2)
            | 0x0018 -> // FX18: Sets the sound timer to VX
                soundTimer := registers.[regX] |> int
                loop (counter + 2)
            | 0x001E -> // FX1E: Adds VX to I and sets overflow byte if required
                let xval = registers.[regX] |> int
                if (!indexRegister + xval) > 0xFF
                then registers.[0xF] <- 1uy
                else registers.[0xF] <- 0uy
                indexRegister := !indexRegister + xval
                loop (counter + 2)
            | 0x0029 -> // FX29: Sets I to the location of the sprite for the character in VX. Characters 0-F (in hexadecimal) are represented by a 4x5 font
                indexRegister := (registers.[regX] |> int) &&& 0x5
                loop (counter + 2)
            | 0x0033 -> // FX33: Stores the Binary-coded decimal representation of VX at the addresses I, I plus 1, and I plus 2
                let xval = registers.[(opCode &&& 0x0F00) >>> 8]
                memory.[!indexRegister] <- xval / 100uy
                memory.[!indexRegister + 1] <- (xval / 10uy) % 10uy
                memory.[!indexRegister + 2] <- (xval % 100uy) % 10uy
                loop (counter + 2)
            | 0x0055 -> // FX55: Stores V0 to VX in memory starting at address I
                for i in 0..((opCode &&& 0x0F00) >>> 8) do
                    memory.[!indexRegister + i] <- registers.[i]

                // On the original interpreter, when the operation is done, I = I + X + 1.
                indexRegister := !indexRegister + ((opCode &&& 0x0F00) >>> 8) + 1;
                loop (counter + 2)
            | 0x0065 -> // FX65: Fills V0 to VX with values from memory starting at address I
                for i in 0..((opCode &&& 0x0F00) >>> 8) do
                    registers.[i] <- memory.[!indexRegister + i]

                // On the original interpreter, when the operation is done, I = I + X + 1.
                indexRegister := !indexRegister + ((opCode &&& 0x0F00) >>> 8) + 1;
                loop (counter + 2)
            | _ -> failwithf "Unknown opcode [0xF000] %X" opCode
        | _ -> failwithf "Unknown opcode %X" opCode

    let start (rom : byte[])  =
        Array.Copy(fontset, 0x0000, memory, 0x0000, fontset.Length)
        Array.Copy(rom, 0x0000, memory, 0x0200, rom.Length)

        loop 0x0200

    let reset() =
        indexRegister := 0
        delayTimer := 0
        soundTimer := 0
        stackPointer := 0 
        memory <- Array.init 4096 (fun _ -> 0uy)
        display <- Array.init 2048 (fun _ -> 0uy)
        registers <- Array.init 16 (fun _ -> 0uy)
        stack <- Array.init 16 (fun _ -> 0)
        key <- Array.init 16 (fun _ -> 0uy)