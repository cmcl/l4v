--
-- Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
--
-- SPDX-License-Identifier: GPL-2.0-only
--

{-# LANGUAGE CPP, GeneralizedNewtypeDeriving, EmptyDataDecls #-}

-- This module defines the low-level RISC-V hardware interface.

-- FIXME AARCH64: This file was copied *VERBATIM* from the RISCV64 version,
-- with minimal text substitution! Remove this comment after updating and
-- checking against C; update copyright as necessary.

module SEL4.Machine.Hardware.AARCH64 where

import Prelude hiding (Word)
import SEL4.Machine.RegisterSet

import Foreign.Ptr
import Control.Monad.Reader
import Data.Bits
import Data.Word(Word8, Word16, Word32, Word64)

-- The RISC-V 64bit-specific register set definitions are qualified with the
-- "RISCV" prefix, and the platform-specific hardware access functions are
-- qualified with the "Platform" prefix.

import qualified SEL4.Machine.RegisterSet.AARCH64 as AARCH64
import qualified SEL4.Machine.Hardware.AARCH64.PLATFORM as Platform

{- Data Types -}

-- The machine monad contains a platform-specific opaque pointer, used by the
-- external simulator interface.

type MachineMonad = ReaderT MachineData IO

type MachineData = Ptr Platform.CallbackData

type IRQ = Platform.IRQ

toPAddr = Platform.PAddr

{- Virtual Memory -}

-- these correspond to 4K, Mega and Giga pages in C

data VMPageSize
    = ARMSmallPage
    | ARMLargePage
    | ARMHugePage
    deriving (Show, Eq, Ord, Enum, Bounded)

data VMFaultType
    = ARMDataAbort
    | ARMPrefetchAbort
    deriving Show

data HypFaultType
    = ARMVCPUFault Word32 -- HSR
    deriving Show

{- Physical Memory -}

type PAddr = Platform.PAddr

fromPAddr :: PAddr -> Word
fromPAddr = Platform.fromPAddr

paddrBase :: PAddr
paddrBase = Platform.PAddr 0x0

pptrBase :: VPtr
pptrBase = VPtr 0xFFFFFFC000000000

pptrTop :: VPtr
pptrTop = VPtr 0xFFFFFFFF80000000

kernelELFPAddrBase :: PAddr
kernelELFPAddrBase = toPAddr $ (fromPAddr Platform.physBase) + 0x4000000

kernelELFBase :: VPtr
kernelELFBase = VPtr $ fromVPtr pptrTop + (fromPAddr kernelELFPAddrBase .&. (mask 30))

pptrUserTop :: VPtr
pptrUserTop = pptrBase

pptrBaseOffset = (fromVPtr pptrBase) - (fromPAddr paddrBase)

ptrFromPAddr :: PAddr -> PPtr a
ptrFromPAddr addr = PPtr $ fromPAddr addr + pptrBaseOffset

addrFromPPtr :: PPtr a -> PAddr
addrFromPPtr addr = toPAddr $ fromPPtr addr - pptrBaseOffset

kernelELFBaseOffset = (fromVPtr kernelELFBase) - (fromPAddr kernelELFPAddrBase)

addrFromKPPtr :: PPtr a -> PAddr
addrFromKPPtr (PPtr addr) = toPAddr $ addr - kernelELFBaseOffset

{- Hardware Access -}

pageBits :: Int
pageBits = 12

-- Each page table performs 9 bits of translation, with each entry occupying
-- 2^3 bytes, thus occupying one small page, apart from top-level tables which
-- contain twice as many entries if config_ARM_PA_SIZE_BITS_40 is set.

ptTranslationBits :: Bool -> Int
ptTranslationBits isToplevel =
    if isToplevel && config_ARM_PA_SIZE_BITS_40 then 10 else 9

pteBits :: Int
pteBits = 3

ptBits :: Bool -> Int
ptBits isTopLevel = ptTranslationBits isTopLevel + pteBits

-- The top-level table cannot contain frame PTEs, so isToplevel is False
pageBitsForSize :: VMPageSize -> Int
pageBitsForSize ARMSmallPage = pageBits
pageBitsForSize ARMLargePage = pageBits + ptTranslationBits False
pageBitsForSize ARMHugePage = pageBits + ptTranslationBits False + ptTranslationBits False

vcpuBits :: Int
vcpuBits = 12

configureTimer :: MachineMonad IRQ
configureTimer = do
    cbptr <- ask
    liftIO $ Platform.configureTimer cbptr

resetTimer :: MachineMonad ()
resetTimer = do
    cbptr <- ask
    liftIO $ Platform.resetTimer cbptr

initIRQController :: MachineMonad ()
initIRQController = error "Unimplemented - boot code"

setIRQTrigger :: IRQ -> Bool -> MachineMonad ()
setIRQTrigger irq trigger = error "Unimplemented - machine op"

getRestartPC = getRegister (Register AARCH64.FaultIP)
setNextPC = setRegister (Register AARCH64.NextIP)

{- Memory Management -}

-- There are several machine operations used by the memory management code to
-- access relevant hardware registers. They are relevant for simulator support
-- only in Haskell and are implemented separately in C and the proofs.

{- Cleaning Memory -}

-- This function is called before a region of user-memory is recycled.
-- It zeros every word to ensure that user tasks cannot access any private data
-- that might previously have been stored in the region.

clearMemory :: PPtr Word -> Int -> MachineMonad ()
clearMemory ptr byteLength = error "Unimplemented -- machine op"

-- This function is called before a region of memory is made user-accessible.
-- Though in Haskell, it is implemented as "clearMemory",
-- we draw the logical distinction to gain more freedom for its interpretation
-- in the Isabelle formalization.

initMemory :: PPtr Word -> Int -> MachineMonad ()
initMemory = clearMemory

-- This function is called to free a region of user-memory after use.
-- In Haskell, this operation does not do anything.
-- We just use it as a stub for the Isabelle formalization.

freeMemory :: PPtr Word -> Int -> MachineMonad ()
freeMemory _ _ = return ()

-- Same as "clearMemory", but uses storeWordVM to write to memory.
-- To be used when creating mapping objects (page tables and -dirs)
-- Flushing the kernel's mapping from TLBindexed
-- caches must be done separately.

clearMemoryVM :: PPtr Word -> Int -> MachineMonad ()
clearMemoryVM ptr bits = error "Unimplemented -- machine op"

{- Address Space Setup -}

setVSpaceRoot :: PAddr -> Word64 -> MachineMonad ()
setVSpaceRoot addr asid = error "Unimplemented - machine op"

{- Memory Barriers -}

isb :: MachineMonad ()
isb = error "Unimplemented - machine op"

dsb :: MachineMonad ()
dsb = error "Unimplemented - machine op"

dmb :: MachineMonad ()
dmb = error "Unimplemented - machine op"

-- FIXME AARCH64: no sfence on Arm
sfence :: MachineMonad ()
sfence = error "Unimplemented - machine op"

{- Cache Cleaning and TLB Flushes -}

invalidateTranslationASID :: Word -> MachineMonad ()
invalidateTranslationASID vmID = error "unimplemented - machine op"

cleanInvalidateCacheRange_RAM :: VPtr -> VPtr -> PAddr -> MachineMonad ()
cleanInvalidateCacheRange_RAM vstart vend pstart = error "Unimplemented - machine op"

cleanCacheRange_RAM :: VPtr -> VPtr -> PAddr -> MachineMonad ()
cleanCacheRange_RAM vstart vend pstart = error "Unimplemented - machine op"

cleanCacheRange_PoU :: VPtr -> VPtr -> PAddr -> MachineMonad ()
cleanCacheRange_PoU vstart vend pstart = error "Unimplemented - machine op"

invalidateCacheRange_RAM :: VPtr -> VPtr -> PAddr -> MachineMonad ()
invalidateCacheRange_RAM vstart vend pstart = error "Unimplemented - machine op"

invalidateCacheRange_I :: VPtr -> VPtr -> PAddr -> MachineMonad ()
invalidateCacheRange_I vstart vend pstart = error "Unimplemented - machine op"

branchFlushRange :: VPtr -> VPtr -> PAddr -> MachineMonad ()
branchFlushRange vstart vend pstart = error "Unimplemented - machine op"


{- FPU status/control registers -}

enableFpuEL01 :: MachineMonad ()
enableFpuEL01 = error "Unimplemented - machine op"

{- Fault registers -}

getFAR :: MachineMonad VPtr
getFAR = error "Unimplemented - machine op"

getDFSR :: MachineMonad Word
getDFSR =  error "Unimplemented - machine op"

getIFSR :: MachineMonad Word
getIFSR =  error "Unimplemented - machine op"


{- Hypervisor-specific status/control registers -}

-- FIXME AARCH64: unused due to using asm intrinsics, but this should be fixed in C
getHSR :: MachineMonad Word
getHSR = error "Unimplemented - machine op"

-- FIXME AARCH64: unused due to using asm intrinsics, but this should be fixed in C
setHCR :: Word -> MachineMonad ()
setHCR _hcr = error "Unimplemented - machine op"

getESR :: MachineMonad Word
getESR = error "Unimplemented - machine op"

addressTranslateS1 :: VPtr -> MachineMonad VPtr
addressTranslateS1 = error "Unimplemented - machine op"

getSCTLR :: MachineMonad Word
getSCTLR = error "Unimplemented - machine op"

setSCTLR :: Word -> MachineMonad ()
setSCTLR _sctlr = error "Unimplemented - machine op"

{- Hypervisor banked registers -}

-- Rather than a line-for-line copy of every hypervisor register storage and
-- retrieval function from the C code, we abstract the concept into one function
-- each. Some special registers, like SCTLR, still get their own load/store
-- functions due to being operated on separately.

readVCPUHardwareReg :: AARCH64.VCPUReg -> MachineMonad Word
readVCPUHardwareReg reg = error "Unimplemented - machine op"

writeVCPUHardwareReg :: AARCH64.VCPUReg -> Word -> MachineMonad ()
writeVCPUHardwareReg reg val = error "Unimplemented - machine op"

{- Page Table Structure -}

data VMAttributes
    = VMAttributes { riscvExecuteNever :: Bool }

-- The C code also defines VMWriteOnly.
-- Leaving it out here will show that it is unused.
data VMRights
    = VMKernelOnly
    | VMReadOnly
    | VMReadWrite
    deriving (Show, Eq)

vmRightsToBits :: VMRights -> Word
vmRightsToBits VMKernelOnly = 1
vmRightsToBits VMReadOnly = 2
vmRightsToBits VMReadWrite = 3

allowWrite :: VMRights -> Bool
allowWrite VMKernelOnly = False
allowWrite VMReadOnly = False
allowWrite VMReadWrite = True

allowRead :: VMRights -> Bool
allowRead VMKernelOnly = False
allowRead VMReadOnly = True
allowRead VMReadWrite = True

getVMRights :: Bool -> Bool -> VMRights
getVMRights True True = VMReadWrite
getVMRights False True = VMReadOnly
getVMRights _ _ = VMKernelOnly

vmRightsFromBits ::  Word -> VMRights
vmRightsFromBits rw = getVMRights (testBit rw 1) (testBit rw 0)

-- Page Table entries

--  Encoding notes:
--  - dirty and accessed bits are always 1 for valid PTEs
--   - SW bits always 0
--   - valid = 1 and read/write/execute = 0 => table PTE
--   - valid = 0 => invalid PTE
--   - otherwise => page PTE

data PTE
    = InvalidPTE
    | PagePTE {
        ptePPN :: PAddr,
        pteGlobal :: Bool,
        pteUser :: Bool,
        pteExecute :: Bool,
        pteRights :: VMRights }
    | PageTablePTE {
        ptePPN :: PAddr,
        pteGlobal :: Bool,
        pteUser :: Bool }
    deriving (Show, Eq)

{- Simulator callbacks -}

pageColourBits :: Int
pageColourBits = Platform.pageColourBits

getMemoryRegions :: MachineMonad [(PAddr, PAddr)]
getMemoryRegions = do
    cpbtr <- ask
    liftIO $ Platform.getMemoryRegions cpbtr

getDeviceRegions :: MachineMonad [(PAddr, PAddr)]
getDeviceRegions = do
    cbptr <- ask
    liftIO $ Platform.getDeviceRegions cbptr

getKernelDevices :: MachineMonad [(PAddr, PPtr Word)]
getKernelDevices = do
    cbptr <- ask
    liftIO $ Platform.getKernelDevices cbptr

storeWord :: PPtr Word -> Word -> MachineMonad ()
storeWord ptr val = do
    cbptr <- ask
    liftIO $ Platform.storeWordCallback cbptr (addrFromPPtr ptr) val

storeWordVM :: PPtr Word -> Word -> MachineMonad ()
storeWordVM ptr val = storeWord ptr val

loadWord :: PPtr Word -> MachineMonad Word
loadWord ptr = do
    cbptr <- ask
    liftIO $ Platform.loadWordCallback cbptr $ addrFromPPtr ptr

getActiveIRQ :: Bool -> MachineMonad (Maybe IRQ)
getActiveIRQ _ = do
    cbptr <- ask
    liftIO $ Platform.getActiveIRQ cbptr

ackInterrupt :: IRQ -> MachineMonad ()
ackInterrupt irq = do
    cbptr <- ask
    liftIO $ Platform.ackInterrupt cbptr irq

maskInterrupt :: Bool -> IRQ -> MachineMonad ()
maskInterrupt maskI irq = do
    cbptr <- ask
    liftIO $ Platform.maskInterrupt cbptr maskI irq

debugPrint :: String -> MachineMonad ()
debugPrint str = liftIO $ putStrLn str

read_stval :: MachineMonad Word
read_stval = error "Unimplemented - machine op"

plic_complete_claim :: IRQ -> MachineMonad ()
plic_complete_claim = error "Unimplemented - machine op"

{- FPU Operations -}

fpuThreadDeleteOp :: Word -> MachineMonad ()
fpuThreadDeleteOp tcbPtr = error "Unimplemented callback"

{- GIC VCPU interface -}

get_gic_vcpu_ctrl_hcr :: MachineMonad Word32
get_gic_vcpu_ctrl_hcr = error "Unimplemented - machine op"

set_gic_vcpu_ctrl_hcr :: Word32 -> MachineMonad ()
set_gic_vcpu_ctrl_hcr = error "Unimplemented - machine op"

get_gic_vcpu_ctrl_vmcr :: MachineMonad Word32
get_gic_vcpu_ctrl_vmcr = error "Unimplemented - machine op"

set_gic_vcpu_ctrl_vmcr :: Word32 -> MachineMonad ()
set_gic_vcpu_ctrl_vmcr = error "Unimplemented - machine op"

get_gic_vcpu_ctrl_apr :: MachineMonad Word32
get_gic_vcpu_ctrl_apr = error "Unimplemented - machine op"

set_gic_vcpu_ctrl_apr :: Word32 -> MachineMonad ()
set_gic_vcpu_ctrl_apr = error "Unimplemented - machine op"

get_gic_vcpu_ctrl_vtr :: MachineMonad Word32
get_gic_vcpu_ctrl_vtr = error "Unimplemented - machine op"

get_gic_vcpu_ctrl_eisr0 :: MachineMonad Word32
get_gic_vcpu_ctrl_eisr0 = error "Unimplemented - machine op"

get_gic_vcpu_ctrl_eisr1 :: MachineMonad Word32
get_gic_vcpu_ctrl_eisr1 = error "Unimplemented - machine op"

get_gic_vcpu_ctrl_misr :: MachineMonad Word32
get_gic_vcpu_ctrl_misr = error "Unimplemented - machine op"

get_gic_vcpu_ctrl_lr :: Word -> MachineMonad Word
get_gic_vcpu_ctrl_lr = error "Unimplemented - machine op"

set_gic_vcpu_ctrl_lr :: Word -> Word -> MachineMonad ()
set_gic_vcpu_ctrl_lr = error "Unimplemented - machine op"

{- Virtual timer interface -}

read_cntpct :: MachineMonad Word64
read_cntpct = error "Unimplemented - machine op"

check_export_arch_timer :: MachineMonad ()
check_export_arch_timer = error "Unimplemented - machine op"


{- Constants -}

hcrVCPU =  (0x80086039 :: Word) -- HCR_VCPU
hcrNative = (0x8e28703b :: Word) -- HCR_NATIVE
sctlrEL1VM = (0x34d58820 :: Word) -- SCTLR_EL1_VM
sctlrDefault  = (0x34d59824 :: Word) -- SCTLR_DEFAULT
vgicHCREN = (0x1 :: Word32) -- VGIC_HCR_EN
gicVCPUMaxNumLR = (64 :: Int)


{- Config parameter -}

-- The size of the physical address space in hyp mode can be configured on some platforms.
config_ARM_PA_SIZE_BITS_40 :: Bool
config_ARM_PA_SIZE_BITS_40 = error "generated from CMake config"