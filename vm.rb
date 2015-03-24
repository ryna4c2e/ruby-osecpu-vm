# -*- coding: utf-8 -*-

# http://osecpu.osask.jp/wiki/?page0091
M32_SIGNATURE = [0x05_E2_00_CF, 0xEE_7F_F1_88]

M32   = 0x76_00_00_00
BIT   = 0x76_00_00_20

NOP   = 0x00
LB    = 0x01
LIMM  = 0x02
PLIMM = 0x03
CND   = 0x04
LMEM  = 0x08
SMEM  = 0x09
PADD  = 0x0E

OR    = 0x10
XOR   = 0x11
AND   = 0x12
SBX   = 0x13
ADD   = 0x14
SUB   = 0x15
MUL   = 0x16
SHL   = 0x18
SAR   = 0x19
DIV   = 0x1A
MOD   = 0x1B

PCP   = 0x1E

CMPE  = 0x20
CMPNE = 0x21
CMPL  = 0x22
CMPGE = 0x23
CMPLE = 0x24
CMPG  = 0x25
TSTZ  = 0x26
TSTNZ = 0x27

DATA  = 0x2E
LIDR  = 0xFD
REM   = 0xFE

class String
  def to_be32
    unpack("N*")
  end
end


class VM
  attr_reader :pc, :r, :p, :d
  ARITH = OR..MOD
  COMP  = CMPE..TSTNZ
  
  def initialize(input)
    @labelTable, @memory = compile(input.read.to_be32)
    @r  = Array.new(0x40, 0)
    @p  = Array.new(0x40, 0)
    @d  = Array.new(4,  0)
  end

  def scope
    yield
  end
  
  def compile(input)
    labelTable = {}
    memory = []
    
    @input = input
    @i = 0

    def word
      a = @input[@i]
      @i += 1
      a
    end

    def imm;  word; end
    def uimm; word - M32; end
    def typ;  word - M32; end
    def len;  word - M32; end
    def opt;  word - M32; end
    def reg;  word - M32; end
    def preg; word - M32; end
    def bit;  word - M32; end


    if input[@i, 2] === M32_SIGNATURE
      @i += 2
    else
      "bad signature. only accepts m32 insts."
    end

    while @i < input.size
      inst = word ^ M32

      case inst
      when NOP # nop
      when LB; scope {        
          lb  = uimm
          o   = opt
          
          labelTable[lb] = memory.size
        }
      when LIMM; scope {
          sign = word
          val  = imm
          r    = reg
          b    = bit
          memory << lambda { @r[r] = val }
        }
      when PLIMM; scope {
          val  = uimm
          p    = preg
          memory << lambda { @p[p] = @labelTable[val] }
        }
      when CND; scope {
          r    = reg
          memory << lambda { if @r[r] % 2 == 0 then nextInst end }
        }
      when LMEM; scope {
          p    = preg
          t    = typ
          sig  = imm
          r    = reg
          b    = bit
          memory << lambda { @r[r] = @memory[@p[p]] }
        }
      when SMEM; scope {
          r    = reg
          b    = bit
          p    = preg
          t    = typ
          sig  = imm
          memory << lambda { @memory[@p[p]] =  @r[r] }
        }
      when PADD; scope {
          p1   = preg
          t    = typ
          r    = reg
          b    = bit
          p0   = preg
          memory << lambda { @p[p0] = @p[p1] + @r[r] }
        }
      when ARITH; scope {
          r1  = reg
          r2  = reg
          r0  = reg
          b   = bit
          memory << case inst
                    when OR
                      lambda { @r[r0] = @r[r1] | @r[r2] }
                    when XOR
                      lambda { @r[r0] = @r[r1] ^ @r[r2] }
                    when AND
                      lambda { @r[r0] = @r[r1] & @r[r2] }
                    when SBX
                      lambda { raise "unimplemented. SBX" }
                    when ADD
                      lambda { @r[r0] = @r[r1] + @r[r2] }
                    when SUB
                      lambda { @r[r0] = (@r[r1] - @r[r2])  & 0xFFFFFFFF }
                    when MUL
                      lambda { @r[r0] = (@r[r1]  * @r[r2]) & 0xFFFFFFFF }
                    when SHL
                      lambda { @r[r0] = (@r[r1] << @r[r2]) & 0xFFFFFFFF }
                    when SAR
                      lambda { @r[r0] = (@r[r1] >> @r[r2]) & 0xFFFFFFFF }
                    when DIV
                      lambda { @r[r0] = @r[r1] / @r[r2] }
                    when MOD
                      lambda { @r[r0] = @r[r1] % @r[r2] }
                    end
        }
      when PCP; scope {
          p1  = preg
          p0  = preg
          if p1 == 0x2F && p0 == 0x3F then
            memory << lambda {
              system_call
            }
          else
            memory << lambda {
              @p[p0] = @p[p1]
            }
          end
        }
      when COMP; scope {
          r1  = reg
          r2  = reg
          bit1= bit
          r0  = reg
          bit2= bit
          memory << case inst
                    when CMPE;  lambda { @r[r0] = @r[r1] == @r[r2] ? 0xFFFFFFFF : 0 }
                    when CMPNE; lambda { @r[r0] = @r[r1] != @r[r2] ? 0xFFFFFFFF : 0 }
                    when CMPL;  lambda { @r[r0] = @r[r1] < @r[r2]  ? 0xFFFFFFFF : 0 }
                    when CMPGE; lambda { @r[r0] = @r[r1] >= @r[r2] ? 0xFFFFFFFF : 0 }
                    when CMPLE; lambda { @r[r0] = @r[r1] <= @r[r2] ? 0xFFFFFFFF : 0 }
                    when CMPG;  lambda { @r[r0] = @r[r1] > @r[r2]  ? 0xFFFFFFFF : 0 }
                    when TSTZ;  lambda { @r[r0] = @r[r1] & @r[r2] == 0 ? 0xFFFFFFFF : 0 }
                    when TSTNZ; lambda { @r[r0] = @r[r1] & @r[r2] != 0 ? 0xFFFFFFFF : 0 }
                    end
        }
      when DATA; scope {
          t   = typ
          l   = len

#          memory << lambda { @p[0x3F] += l }
          
          l.times do
            memory << word
          end
        }
      when LIDR; scope {
          sig = word
          val = imm
          dr  = reg
          memory << lambda { @d[dr] = val }
        }
      when REM; scope {
          val = imm
          len = word
        }
      else
        puts "unknown opcode: #{inst.to_s(16)}, number = #{@i}"
      end
    end

    return [labelTable, memory]
  end

  def system_call
#    puts "system call"
    @p[0x3F] = @p[0x30]
    case @r[0x30]
    when 0x02 # drawPoint
      puts "drawPoint #{@r[0x31, 4].join(' ')}"
    when 0x10 # openWin
      puts "openWin #{@r[0x31, 4].join(' ')}"
    end
  end
  
  def pc
    @p[0x3F]
  end

  def nextInst
    inst = @memory[pc]
    @p[0x3F] += 1
    inst
  end
  
  def execute
    puts(@memory.inspect)
    puts(@labelTable.inspect)
    while pc < @memory.size
      inst = nextInst
      begin
        inst.call if inst.is_a?(Proc)
      rescue => e
        puts e
      end
    end
    puts(@r.inspect)
    puts(@p.inspect)

  end
end


byteFile = ARGV[0]
raise "no input code specified" if byteFile == nil
inputCode = File.open(ARGV[0], "rb")

vm = VM.new(inputCode)
vm.execute
