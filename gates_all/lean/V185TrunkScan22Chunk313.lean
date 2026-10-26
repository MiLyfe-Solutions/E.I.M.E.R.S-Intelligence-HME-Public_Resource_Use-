import V185TrunkScan22Chunk312

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_2791738 : List Nat := [3, 1, 1, 1, 4, 2, 1, 3, 2, 4]
def baseStart_2791738 : Nat := 118140960795 + 2791738 * 2 ^ 59
def prefixEnd_2791738 : Nat := 4983230072969 + 3 ^ 40 * 2791738 * 2
def baseEnd_2791738 : Nat := 955668970281135697290691

theorem tailTrace_2791738 : CollatzResearch.WordTrace tailWord_2791738 prefixEnd_2791738 955668970281135697290691 := by
  unfold tailWord_2791738
  simp only [CollatzResearch.WordTrace]
  refine ⟨25455762490004372934061967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67882033306678327824165245 25455762490004372934061967)
  ·
    refine ⟨38183643735006559401092951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25455762490004372934061967 38183643735006559401092951)
    ·
      refine ⟨57275465602509839101639427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38183643735006559401092951 57275465602509839101639427)
      ·
        refine ⟨85913198403764758652459141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57275465602509839101639427 85913198403764758652459141)
        ·
          refine ⟨16108724700705892247336089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 85913198403764758652459141 16108724700705892247336089)
          ·
            refine ⟨12081543525529419185502067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16108724700705892247336089 12081543525529419185502067)
            ·
              refine ⟨18122315288294128778253101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12081543525529419185502067 18122315288294128778253101)
              ·
                refine ⟨6795868233110298291844913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18122315288294128778253101 6795868233110298291844913)
                ·
                  refine ⟨5096901174832723718883685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6795868233110298291844913 5096901174832723718883685)
                  ·
                    refine ⟨955668970281135697290691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5096901174832723718883685 955668970281135697290691)
                    ·
                      rfl

theorem cell22_2791738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 3, 2, 4].length) (baseStart_2791738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2791738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2791738 prefixEnd_2791738 := by exact prefixLift 2791738
  have htrace : WordTrace (prefixWord ++ tailWord_2791738) baseStart_2791738 baseEnd_2791738 := by
    simpa [prefixWord, tailWord_2791738, baseEnd_2791738] using wordTrace_append hprefix tailTrace_2791738
  have hstable : (prefixWord ++ tailWord_2791738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2791738).length < 2 ^ (prefixWord ++ tailWord_2791738).sum := by decide
  have hdescent : baseEnd_2791738 < baseStart_2791738 := by decide
  rcases family_descends (prefixWord ++ tailWord_2791738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2791832 : List Nat := [2, 1, 2, 5, 1, 2, 3, 1, 5]
def baseStart_2791832 : Nat := 118140960795 + 2791832 * 2 ^ 59
def prefixEnd_2791832 : Nat := 4983230072969 + 3 ^ 40 * 2791832 * 2
def baseEnd_2791832 : Nat := 318567049467383595146801

theorem tailTrace_2791832 : CollatzResearch.WordTrace tailWord_2791832 prefixEnd_2791832 318567049467383595146801 := by
  unfold tailWord_2791832
  simp only [CollatzResearch.WordTrace]
  refine ⟨50913239210838472895084875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67884318947784630526779833 50913239210838472895084875)
  ·
    refine ⟨76369858816257709342627313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50913239210838472895084875 76369858816257709342627313)
    ·
      refine ⟨57277394112193282006970485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76369858816257709342627313 57277394112193282006970485)
      ·
        refine ⟨5369755698018120188153483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 57277394112193282006970485 5369755698018120188153483)
        ·
          refine ⟨8054633547027180282230225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5369755698018120188153483 8054633547027180282230225)
          ·
            refine ⟨6040975160270385211672669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8054633547027180282230225 6040975160270385211672669)
            ·
              refine ⟨2265365685101394454377251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6040975160270385211672669 2265365685101394454377251)
              ·
                refine ⟨3398048527652091681565877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2265365685101394454377251 3398048527652091681565877)
                ·
                  refine ⟨318567049467383595146801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3398048527652091681565877 318567049467383595146801)
                  ·
                    rfl

theorem cell22_2791832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 3, 1, 5].length) (baseStart_2791832 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2791832 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2791832 prefixEnd_2791832 := by exact prefixLift 2791832
  have htrace : WordTrace (prefixWord ++ tailWord_2791832) baseStart_2791832 baseEnd_2791832 := by
    simpa [prefixWord, tailWord_2791832, baseEnd_2791832] using wordTrace_append hprefix tailTrace_2791832
  have hstable : (prefixWord ++ tailWord_2791832).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2791832).length < 2 ^ (prefixWord ++ tailWord_2791832).sum := by decide
  have hdescent : baseEnd_2791832 < baseStart_2791832 := by decide
  rcases family_descends (prefixWord ++ tailWord_2791832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2791843 : List Nat := [1, 1, 1, 4, 1, 4, 2, 2, 6]
def baseStart_2791843 : Nat := 118140960795 + 2791843 * 2 ^ 59
def prefixEnd_2791843 : Nat := 4983230072969 + 3 ^ 40 * 2791843 * 2
def baseEnd_2791843 : Nat := 318568304642316807805123

theorem tailTrace_2791843 : CollatzResearch.WordTrace tailWord_2791843 prefixEnd_2791843 318568304642316807805123 := by
  unfold tailWord_2791843
  simp only [CollatzResearch.WordTrace]
  refine ⟨101826879624637094668820183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67884586416424729779213455 101826879624637094668820183)
  ·
    refine ⟨152740319436955642003230275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101826879624637094668820183 152740319436955642003230275)
    ·
      refine ⟨229110479155433463004845413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152740319436955642003230275 229110479155433463004845413)
      ·
        refine ⟨42958214841643774313408515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 229110479155433463004845413 42958214841643774313408515)
        ·
          refine ⟨64437322262465661470112773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42958214841643774313408515 64437322262465661470112773)
          ·
            refine ⟨12081997924212311525646145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64437322262465661470112773 12081997924212311525646145)
            ·
              refine ⟨9061498443159233644234609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12081997924212311525646145 9061498443159233644234609)
              ·
                refine ⟨6796123832369425233175957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9061498443159233644234609 6796123832369425233175957)
                ·
                  refine ⟨318568304642316807805123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6796123832369425233175957 318568304642316807805123)
                  ·
                    rfl

theorem cell22_2791843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 2, 6].length) (baseStart_2791843 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2791843 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2791843 prefixEnd_2791843 := by exact prefixLift 2791843
  have htrace : WordTrace (prefixWord ++ tailWord_2791843) baseStart_2791843 baseEnd_2791843 := by
    simpa [prefixWord, tailWord_2791843, baseEnd_2791843] using wordTrace_append hprefix tailTrace_2791843
  have hstable : (prefixWord ++ tailWord_2791843).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2791843).length < 2 ^ (prefixWord ++ tailWord_2791843).sum := by decide
  have hdescent : baseEnd_2791843 < baseStart_2791843 := by decide
  rcases family_descends (prefixWord ++ tailWord_2791843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2791845 : List Nat := [1, 3, 1, 2, 1, 1, 6, 2, 1, 4]
def baseStart_2791845 : Nat := 118140960795 + 2791845 * 2 ^ 59
def prefixEnd_2791845 : Nat := 4983230072969 + 3 ^ 40 * 2791845 * 2
def baseEnd_2791845 : Nat := 955705598567823084865363

theorem tailTrace_2791845 : CollatzResearch.WordTrace tailWord_2791845 prefixEnd_2791845 955705598567823084865363 := by
  unfold tailWord_2791845
  simp only [CollatzResearch.WordTrace]
  refine ⟨101826952570629849010392989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67884635047086566006928659 101826952570629849010392989)
  ·
    refine ⟨38185107213986193378897371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101826952570629849010392989 38185107213986193378897371)
    ·
      refine ⟨57277660820979290068346057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38185107213986193378897371 57277660820979290068346057)
      ·
        refine ⟨42958245615734467551259543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57277660820979290068346057 42958245615734467551259543)
        ·
          refine ⟨64437368423601701326889315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42958245615734467551259543 64437368423601701326889315)
          ·
            refine ⟨96656052635402551990333973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64437368423601701326889315 96656052635402551990333973)
            ·
              refine ⟨4530752467284494624546905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 96656052635402551990333973 4530752467284494624546905)
              ·
                refine ⟨3398064350463370968410179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4530752467284494624546905 3398064350463370968410179)
                ·
                  refine ⟨5097096525695056452615269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3398064350463370968410179 5097096525695056452615269)
                  ·
                    refine ⟨955705598567823084865363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5097096525695056452615269 955705598567823084865363)
                    ·
                      rfl

theorem cell22_2791845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 6, 2, 1, 4].length) (baseStart_2791845 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2791845 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2791845 prefixEnd_2791845 := by exact prefixLift 2791845
  have htrace : WordTrace (prefixWord ++ tailWord_2791845) baseStart_2791845 baseEnd_2791845 := by
    simpa [prefixWord, tailWord_2791845, baseEnd_2791845] using wordTrace_append hprefix tailTrace_2791845
  have hstable : (prefixWord ++ tailWord_2791845).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2791845).length < 2 ^ (prefixWord ++ tailWord_2791845).sum := by decide
  have hdescent : baseEnd_2791845 < baseStart_2791845 := by decide
  rcases family_descends (prefixWord ++ tailWord_2791845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2791853 : List Nat := [1, 5, 2, 2, 3, 1, 1, 3, 1, 3]
def baseStart_2791853 : Nat := 118140960795 + 2791853 * 2 ^ 59
def prefixEnd_2791853 : Nat := 4983230072969 + 3 ^ 40 * 2791853 * 2
def baseEnd_2791853 : Nat := 955708337131313730665339

theorem tailTrace_2791853 : CollatzResearch.WordTrace tailWord_2791853 prefixEnd_2791853 955708337131313730665339 := by
  unfold tailWord_2791853
  simp only [CollatzResearch.WordTrace]
  refine ⟨101827244354600866376684213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67884829569733910917789475 101827244354600866376684213)
  ·
    refine ⟨9546304158243831222814145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 101827244354600866376684213 9546304158243831222814145)
    ·
      refine ⟨7159728118682873417110609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9546304158243831222814145 7159728118682873417110609)
      ·
        refine ⟨5369796089012155062832957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7159728118682873417110609 5369796089012155062832957)
        ·
          refine ⟨2013673533379558148562359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5369796089012155062832957 2013673533379558148562359)
          ·
            refine ⟨3020510300069337222843539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2013673533379558148562359 3020510300069337222843539)
            ·
              refine ⟨4530765450104005834265309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3020510300069337222843539 4530765450104005834265309)
              ·
                refine ⟨1699037043789002187849491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4530765450104005834265309 1699037043789002187849491)
                ·
                  refine ⟨2548555565683503281774237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1699037043789002187849491 2548555565683503281774237)
                  ·
                    refine ⟨955708337131313730665339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2548555565683503281774237 955708337131313730665339)
                    ·
                      rfl

theorem cell22_2791853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 1, 3, 1, 3].length) (baseStart_2791853 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2791853 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2791853 prefixEnd_2791853 := by exact prefixLift 2791853
  have htrace : WordTrace (prefixWord ++ tailWord_2791853) baseStart_2791853 baseEnd_2791853 := by
    simpa [prefixWord, tailWord_2791853, baseEnd_2791853] using wordTrace_append hprefix tailTrace_2791853
  have hstable : (prefixWord ++ tailWord_2791853).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2791853).length < 2 ^ (prefixWord ++ tailWord_2791853).sum := by decide
  have hdescent : baseEnd_2791853 < baseStart_2791853 := by decide
  rcases family_descends (prefixWord ++ tailWord_2791853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2791858 : List Nat := [3, 2, 1, 1, 1, 1, 4, 1, 3, 5]
def baseStart_2791858 : Nat := 118140960795 + 2791858 * 2 ^ 59
def prefixEnd_2791858 : Nat := 4983230072969 + 3 ^ 40 * 2791858 * 2
def baseEnd_2791858 : Nat := 955710048733495384290323

theorem tailTrace_2791858 : CollatzResearch.WordTrace tailWord_2791858 prefixEnd_2791858 955710048733495384290323 := by
  unfold tailWord_2791858
  simp only [CollatzResearch.WordTrace]
  refine ⟨25456856679895688057654057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67884951146388501487077485 25456856679895688057654057)
  ·
    refine ⟨19092642509921766043240543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25456856679895688057654057 19092642509921766043240543)
    ·
      refine ⟨28638963764882649064860815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19092642509921766043240543 28638963764882649064860815)
      ·
        refine ⟨42958445647323973597291223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28638963764882649064860815 42958445647323973597291223)
        ·
          refine ⟨64437668470985960395936835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42958445647323973597291223 64437668470985960395936835)
          ·
            refine ⟨96656502706478940593905253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64437668470985960395936835 96656502706478940593905253)
            ·
              refine ⟨18123094257464801361357235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 96656502706478940593905253 18123094257464801361357235)
              ·
                refine ⟨27184641386197202042035853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18123094257464801361357235 27184641386197202042035853)
                ·
                  refine ⟨10194240519823950765763445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27184641386197202042035853 10194240519823950765763445)
                  ·
                    refine ⟨955710048733495384290323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10194240519823950765763445 955710048733495384290323)
                    ·
                      rfl

theorem cell22_2791858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 1, 3, 5].length) (baseStart_2791858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2791858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2791858 prefixEnd_2791858 := by exact prefixLift 2791858
  have htrace : WordTrace (prefixWord ++ tailWord_2791858) baseStart_2791858 baseEnd_2791858 := by
    simpa [prefixWord, tailWord_2791858, baseEnd_2791858] using wordTrace_append hprefix tailTrace_2791858
  have hstable : (prefixWord ++ tailWord_2791858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2791858).length < 2 ^ (prefixWord ++ tailWord_2791858).sum := by decide
  have hdescent : baseEnd_2791858 < baseStart_2791858 := by decide
  rcases family_descends (prefixWord ++ tailWord_2791858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2791875 : List Nat := [1, 1, 1, 3, 1, 1, 3, 6, 2, 3]
def baseStart_2791875 : Nat := 118140960795 + 2791875 * 2 ^ 59
def prefixEnd_2791875 : Nat := 4983230072969 + 3 ^ 40 * 2791875 * 2
def baseEnd_2791875 : Nat := 955715868180913006615271

theorem tailTrace_2791875 : CollatzResearch.WordTrace tailWord_2791875 prefixEnd_2791875 955715868180913006615271 := by
  unfold tailWord_2791875
  simp only [CollatzResearch.WordTrace]
  refine ⟨101828046760521164133985079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67885364507014109422656719 101828046760521164133985079)
  ·
    refine ⟨152742070140781746200977619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101828046760521164133985079 152742070140781746200977619)
    ·
      refine ⟨229113105211172619301466429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152742070140781746200977619 229113105211172619301466429)
      ·
        refine ⟨85917414454189732238049911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 229113105211172619301466429 85917414454189732238049911)
        ·
          refine ⟨128876121681284598357074867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85917414454189732238049911 128876121681284598357074867)
          ·
            refine ⟨193314182521926897535612301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128876121681284598357074867 193314182521926897535612301)
            ·
              refine ⟨72492818445722586575854613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 193314182521926897535612301 72492818445722586575854613)
              ·
                refine ⟨3398100864643246245743185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 72492818445722586575854613 3398100864643246245743185)
                ·
                  refine ⟨2548575648482434684307389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3398100864643246245743185 2548575648482434684307389)
                  ·
                    refine ⟨955715868180913006615271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2548575648482434684307389 955715868180913006615271)
                    ·
                      rfl

theorem cell22_2791875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 6, 2, 3].length) (baseStart_2791875 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2791875 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2791875 prefixEnd_2791875 := by exact prefixLift 2791875
  have htrace : WordTrace (prefixWord ++ tailWord_2791875) baseStart_2791875 baseEnd_2791875 := by
    simpa [prefixWord, tailWord_2791875, baseEnd_2791875] using wordTrace_append hprefix tailTrace_2791875
  have hstable : (prefixWord ++ tailWord_2791875).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2791875).length < 2 ^ (prefixWord ++ tailWord_2791875).sum := by decide
  have hdescent : baseEnd_2791875 < baseStart_2791875 := by decide
  rcases family_descends (prefixWord ++ tailWord_2791875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2791907 : List Nat := [1, 1, 1, 6, 3, 1, 2, 1, 2, 4]
def baseStart_2791907 : Nat := 118140960795 + 2791907 * 2 ^ 59
def prefixEnd_2791907 : Nat := 4983230072969 + 3 ^ 40 * 2791907 * 2
def baseEnd_2791907 : Nat := 955726822434875589815173

theorem tailTrace_2791907 : CollatzResearch.WordTrace tailWord_2791907 prefixEnd_2791907 955726822434875589815173 := by
  unfold tailWord_2791907
  simp only [CollatzResearch.WordTrace]
  refine ⟨101829213896405233599149975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67886142597603489066099983 101829213896405233599149975)
  ·
    refine ⟨152743820844607850398724963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101829213896405233599149975 152743820844607850398724963)
    ·
      refine ⟨229115731266911775598087445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152743820844607850398724963 229115731266911775598087445)
      ·
        refine ⟨10739799903136489481160349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 229115731266911775598087445 10739799903136489481160349)
        ·
          refine ⟨4027424963676183555435131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10739799903136489481160349 4027424963676183555435131)
          ·
            refine ⟨6041137445514275333152697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4027424963676183555435131 6041137445514275333152697)
            ·
              refine ⟨4530853084135706499864523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6041137445514275333152697 4530853084135706499864523)
              ·
                refine ⟨6796279626203559749796785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4530853084135706499864523 6796279626203559749796785)
                ·
                  refine ⟨5097209719652669812347589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6796279626203559749796785 5097209719652669812347589)
                  ·
                    refine ⟨955726822434875589815173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5097209719652669812347589 955726822434875589815173)
                    ·
                      rfl

theorem cell22_2791907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 2, 1, 2, 4].length) (baseStart_2791907 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2791907 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2791907 prefixEnd_2791907 := by exact prefixLift 2791907
  have htrace : WordTrace (prefixWord ++ tailWord_2791907) baseStart_2791907 baseEnd_2791907 := by
    simpa [prefixWord, tailWord_2791907, baseEnd_2791907] using wordTrace_append hprefix tailTrace_2791907
  have hstable : (prefixWord ++ tailWord_2791907).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2791907).length < 2 ^ (prefixWord ++ tailWord_2791907).sum := by decide
  have hdescent : baseEnd_2791907 < baseStart_2791907 := by decide
  rcases family_descends (prefixWord ++ tailWord_2791907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2792042 : List Nat := [3, 1, 3, 2, 1, 1, 3, 2, 2, 4]
def baseStart_2792042 : Nat := 118140960795 + 2792042 * 2 ^ 59
def prefixEnd_2792042 : Nat := 4983230072969 + 3 ^ 40 * 2792042 * 2
def baseEnd_2792042 : Nat := 955773035693780237689759

theorem tailTrace_2792042 : CollatzResearch.WordTrace tailWord_2792042 prefixEnd_2792042 955773035693780237689759 := by
  unfold tailWord_2792042
  simp only [CollatzResearch.WordTrace]
  refine ⟨25458534437729037913828595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67889425167277434436876253 25458534437729037913828595)
  ·
    refine ⟨38187801656593556870742893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25458534437729037913828595 38187801656593556870742893)
    ·
      refine ⟨14320425621222583826528585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38187801656593556870742893 14320425621222583826528585)
      ·
        refine ⟨10740319215916937869896439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14320425621222583826528585 10740319215916937869896439)
        ·
          refine ⟨16110478823875406804844659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10740319215916937869896439 16110478823875406804844659)
          ·
            refine ⟨24165718235813110207266989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16110478823875406804844659 24165718235813110207266989)
            ·
              refine ⟨9062144338429916327725121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24165718235813110207266989 9062144338429916327725121)
              ·
                refine ⟨6796608253822437245793841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9062144338429916327725121 6796608253822437245793841)
                ·
                  refine ⟨5097456190366827934345381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6796608253822437245793841 5097456190366827934345381)
                  ·
                    refine ⟨955773035693780237689759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5097456190366827934345381 955773035693780237689759)
                    ·
                      rfl

theorem cell22_2792042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 2, 2, 4].length) (baseStart_2792042 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2792042 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2792042 prefixEnd_2792042 := by exact prefixLift 2792042
  have htrace : WordTrace (prefixWord ++ tailWord_2792042) baseStart_2792042 baseEnd_2792042 := by
    simpa [prefixWord, tailWord_2792042, baseEnd_2792042] using wordTrace_append hprefix tailTrace_2792042
  have hstable : (prefixWord ++ tailWord_2792042).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2792042).length < 2 ^ (prefixWord ++ tailWord_2792042).sum := by decide
  have hdescent : baseEnd_2792042 < baseStart_2792042 := by decide
  rcases family_descends (prefixWord ++ tailWord_2792042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2792046 : List Nat := [4, 1, 2, 2, 2, 2, 3, 2, 4]
def baseStart_2792046 : Nat := 118140960795 + 2792046 * 2 ^ 59
def prefixEnd_2792046 : Nat := 4983230072969 + 3 ^ 40 * 2792046 * 2
def baseEnd_2792046 : Nat := 318591468325175186863249

theorem tailTrace_2792046 : CollatzResearch.WordTrace tailWord_2792046 prefixEnd_2792046 318591468325175186863249 := by
  unfold tailWord_2792046
  simp only [CollatzResearch.WordTrace]
  refine ⟨12729285455362707542307499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67889522428601106892306661 12729285455362707542307499)
  ·
    refine ⟨19093928183044061313461249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12729285455362707542307499 19093928183044061313461249)
    ·
      refine ⟨14320446137283045985095937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19093928183044061313461249 14320446137283045985095937)
      ·
        refine ⟨10740334602962284488821953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14320446137283045985095937 10740334602962284488821953)
        ·
          refine ⟨8055250952221713366616465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10740334602962284488821953 8055250952221713366616465)
          ·
            refine ⟨6041438214166285024962349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8055250952221713366616465 6041438214166285024962349)
            ·
              refine ⟨2265539330312356884360881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6041438214166285024962349 2265539330312356884360881)
              ·
                refine ⟨1699154497734267663270661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2265539330312356884360881 1699154497734267663270661)
                ·
                  refine ⟨318591468325175186863249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1699154497734267663270661 318591468325175186863249)
                  ·
                    rfl

theorem cell22_2792046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 3, 2, 4].length) (baseStart_2792046 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2792046 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2792046 prefixEnd_2792046 := by exact prefixLift 2792046
  have htrace : WordTrace (prefixWord ++ tailWord_2792046) baseStart_2792046 baseEnd_2792046 := by
    simpa [prefixWord, tailWord_2792046, baseEnd_2792046] using wordTrace_append hprefix tailTrace_2792046
  have hstable : (prefixWord ++ tailWord_2792046).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2792046).length < 2 ^ (prefixWord ++ tailWord_2792046).sum := by decide
  have hdescent : baseEnd_2792046 < baseStart_2792046 := by decide
  rcases family_descends (prefixWord ++ tailWord_2792046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2792089 : List Nat := [1, 2, 1, 2, 1, 2, 4, 5, 1, 3]
def baseStart_2792089 : Nat := 118140960795 + 2792089 * 2 ^ 59
def prefixEnd_2792089 : Nat := 4983230072969 + 3 ^ 40 * 2792089 * 2
def baseEnd_2792089 : Nat := 955789124754287781764615

theorem tailTrace_2792089 : CollatzResearch.WordTrace tailWord_2792089 prefixEnd_2792089 955789124754287781764615 := by
  unfold tailWord_2792089
  simp only [CollatzResearch.WordTrace]
  refine ⟨101835851981745878682275321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67890567987830585788183547 101835851981745878682275321)
  ·
    refine ⟨76376888986309409011706491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101835851981745878682275321 76376888986309409011706491)
    ·
      refine ⟨114565333479464113517559737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76376888986309409011706491 114565333479464113517559737)
      ·
        refine ⟨85924000109598085138169803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114565333479464113517559737 85924000109598085138169803)
        ·
          refine ⟨128886000164397127707254705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85924000109598085138169803 128886000164397127707254705)
          ·
            refine ⟨96664500123297845780441029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 128886000164397127707254705 96664500123297845780441029)
            ·
              refine ⟨18124593773118346083832693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 96664500123297845780441029 18124593773118346083832693)
              ·
                refine ⟨1699180666229844945359315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18124593773118346083832693 1699180666229844945359315)
                ·
                  refine ⟨2548770999344767418038973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1699180666229844945359315 2548770999344767418038973)
                  ·
                    refine ⟨955789124754287781764615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2548770999344767418038973 955789124754287781764615)
                    ·
                      rfl

theorem cell22_2792089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 5, 1, 3].length) (baseStart_2792089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2792089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2792089 prefixEnd_2792089 := by exact prefixLift 2792089
  have htrace : WordTrace (prefixWord ++ tailWord_2792089) baseStart_2792089 baseEnd_2792089 := by
    simpa [prefixWord, tailWord_2792089, baseEnd_2792089] using wordTrace_append hprefix tailTrace_2792089
  have hstable : (prefixWord ++ tailWord_2792089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2792089).length < 2 ^ (prefixWord ++ tailWord_2792089).sum := by decide
  have hdescent : baseEnd_2792089 < baseStart_2792089 := by decide
  rcases family_descends (prefixWord ++ tailWord_2792089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2792117 : List Nat := [1, 3, 3, 3, 1, 1, 1, 1, 1, 7]
def baseStart_2792117 : Nat := 118140960795 + 2792117 * 2 ^ 59
def prefixEnd_2792117 : Nat := 4983230072969 + 3 ^ 40 * 2792117 * 2
def baseEnd_2792117 : Nat := 955798709726505042064529

theorem tailTrace_2792117 : CollatzResearch.WordTrace tailWord_2792117 prefixEnd_2792117 955798709726505042064529 := by
  unfold tailWord_2792117
  simp only [CollatzResearch.WordTrace]
  refine ⟨101836873225644439464294605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67891248817096292976196403 101836873225644439464294605)
  ·
    refine ⟨38188827459616664799110477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101836873225644439464294605 38188827459616664799110477)
    ·
      refine ⟨14320810297356249299666429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38188827459616664799110477 14320810297356249299666429)
      ·
        refine ⟨5370303861508593487374911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14320810297356249299666429 5370303861508593487374911)
        ·
          refine ⟨8055455792262890231062367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5370303861508593487374911 8055455792262890231062367)
          ·
            refine ⟨12083183688394335346593551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8055455792262890231062367 12083183688394335346593551)
            ·
              refine ⟨18124775532591503019890327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12083183688394335346593551 18124775532591503019890327)
              ·
                refine ⟨27187163298887254529835491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18124775532591503019890327 27187163298887254529835491)
                ·
                  refine ⟨40780744948330881794753237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27187163298887254529835491 40780744948330881794753237)
                  ·
                    refine ⟨955798709726505042064529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40780744948330881794753237 955798709726505042064529)
                    ·
                      rfl

theorem cell22_2792117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 1, 1, 7].length) (baseStart_2792117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2792117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2792117 prefixEnd_2792117 := by exact prefixLift 2792117
  have htrace : WordTrace (prefixWord ++ tailWord_2792117) baseStart_2792117 baseEnd_2792117 := by
    simpa [prefixWord, tailWord_2792117, baseEnd_2792117] using wordTrace_append hprefix tailTrace_2792117
  have hstable : (prefixWord ++ tailWord_2792117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2792117).length < 2 ^ (prefixWord ++ tailWord_2792117).sum := by decide
  have hdescent : baseEnd_2792117 < baseStart_2792117 := by decide
  rcases family_descends (prefixWord ++ tailWord_2792117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2792164 : List Nat := [2, 3, 1, 1, 1, 4, 2, 4, 4]
def baseStart_2792164 : Nat := 118140960795 + 2792164 * 2 ^ 59
def prefixEnd_2792164 : Nat := 4983230072969 + 3 ^ 40 * 2792164 * 2
def baseEnd_2792164 : Nat := 318604932929004195379795

theorem tailTrace_2792164 : CollatzResearch.WordTrace tailWord_2792164 prefixEnd_2792164 318604932929004195379795 := by
  unfold tailWord_2792164
  simp only [CollatzResearch.WordTrace]
  refine ⟨50919293728237083245627773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67892391637649444327503697 50919293728237083245627773)
  ·
    refine ⟨19094735148088906217110415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50919293728237083245627773 19094735148088906217110415)
    ·
      refine ⟨28642102722133359325665623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19094735148088906217110415 28642102722133359325665623)
      ·
        refine ⟨42963154083200038988498435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28642102722133359325665623 42963154083200038988498435)
        ·
          refine ⟨64444731124800058482747653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42963154083200038988498435 64444731124800058482747653)
          ·
            refine ⟨12083387085900010965515185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64444731124800058482747653 12083387085900010965515185)
            ·
              refine ⟨9062540314425008224136389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12083387085900010965515185 9062540314425008224136389)
              ·
                refine ⟨1699226308954689042025573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9062540314425008224136389 1699226308954689042025573)
                ·
                  refine ⟨318604932929004195379795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1699226308954689042025573 318604932929004195379795)
                  ·
                    rfl

theorem cell22_2792164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 4, 4].length) (baseStart_2792164 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2792164 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2792164 prefixEnd_2792164 := by exact prefixLift 2792164
  have htrace : WordTrace (prefixWord ++ tailWord_2792164) baseStart_2792164 baseEnd_2792164 := by
    simpa [prefixWord, tailWord_2792164, baseEnd_2792164] using wordTrace_append hprefix tailTrace_2792164
  have hstable : (prefixWord ++ tailWord_2792164).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2792164).length < 2 ^ (prefixWord ++ tailWord_2792164).sum := by decide
  have hdescent : baseEnd_2792164 < baseStart_2792164 := by decide
  rcases family_descends (prefixWord ++ tailWord_2792164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2792194 : List Nat := [3, 4, 1, 1, 1, 2, 2, 1, 1, 6]
def baseStart_2792194 : Nat := 118140960795 + 2792194 * 2 ^ 59
def prefixEnd_2792194 : Nat := 4983230072969 + 3 ^ 40 * 2792194 * 2
def baseEnd_2792194 : Nat := 955825068400102507889293

theorem tailTrace_2792194 : CollatzResearch.WordTrace tailWord_2792194 prefixEnd_2792194 955825068400102507889293 := by
  unfold tailWord_2792194
  simp only [CollatzResearch.WordTrace]
  refine ⟨25459920411591370403711909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67893121097576987743231757 25459920411591370403711909)
  ·
    refine ⟨4773735077173381950695983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25459920411591370403711909 4773735077173381950695983)
    ·
      refine ⟨7160602615760072926043975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4773735077173381950695983 7160602615760072926043975)
      ·
        refine ⟨10740903923640109389065963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7160602615760072926043975 10740903923640109389065963)
        ·
          refine ⟨16111355885460164083598945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10740903923640109389065963 16111355885460164083598945)
          ·
            refine ⟨12083516914095123062699209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16111355885460164083598945 12083516914095123062699209)
            ·
              refine ⟨9062637685571342297024407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12083516914095123062699209 9062637685571342297024407)
              ·
                refine ⟨13593956528357013445536611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9062637685571342297024407 13593956528357013445536611)
                ·
                  refine ⟨20390934792535520168304917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13593956528357013445536611 20390934792535520168304917)
                  ·
                    refine ⟨955825068400102507889293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20390934792535520168304917 955825068400102507889293)
                    ·
                      rfl

theorem cell22_2792194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 1, 1, 6].length) (baseStart_2792194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2792194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2792194 prefixEnd_2792194 := by exact prefixLift 2792194
  have htrace : WordTrace (prefixWord ++ tailWord_2792194) baseStart_2792194 baseEnd_2792194 := by
    simpa [prefixWord, tailWord_2792194, baseEnd_2792194] using wordTrace_append hprefix tailTrace_2792194
  have hstable : (prefixWord ++ tailWord_2792194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2792194).length < 2 ^ (prefixWord ++ tailWord_2792194).sum := by decide
  have hdescent : baseEnd_2792194 < baseStart_2792194 := by decide
  rcases family_descends (prefixWord ++ tailWord_2792194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2792252 : List Nat := [2, 2, 2, 2, 1, 1, 1, 2, 4, 5]
def baseStart_2792252 : Nat := 118140960795 + 2792252 * 2 ^ 59
def prefixEnd_2792252 : Nat := 4983230072969 + 3 ^ 40 * 2792252 * 2
def baseEnd_2792252 : Nat := 955844922985409689939115

theorem tailTrace_2792252 : CollatzResearch.WordTrace tailWord_2792252 prefixEnd_2792252 955844922985409689939115 := by
  unfold tailWord_2792252
  simp only [CollatzResearch.WordTrace]
  refine ⟨50920898540077678760229505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67894531386770238346972673 50920898540077678760229505)
  ·
    refine ⟨38190673905058259070172129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50920898540077678760229505 38190673905058259070172129)
    ·
      refine ⟨28643005428793694302629097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38190673905058259070172129 28643005428793694302629097)
      ·
        refine ⟨21482254071595270726971823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28643005428793694302629097 21482254071595270726971823)
        ·
          refine ⟨32223381107392906090457735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21482254071595270726971823 32223381107392906090457735)
          ·
            refine ⟨48335071661089359135686603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32223381107392906090457735 48335071661089359135686603)
            ·
              refine ⟨72502607491634038703529905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48335071661089359135686603 72502607491634038703529905)
              ·
                refine ⟨54376955618725529027647429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72502607491634038703529905 54376955618725529027647429)
                ·
                  refine ⟨10195679178511036692683893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 54376955618725529027647429 10195679178511036692683893)
                  ·
                    refine ⟨955844922985409689939115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10195679178511036692683893 955844922985409689939115)
                    ·
                      rfl

theorem cell22_2792252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 2, 4, 5].length) (baseStart_2792252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2792252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2792252 prefixEnd_2792252 := by exact prefixLift 2792252
  have htrace : WordTrace (prefixWord ++ tailWord_2792252) baseStart_2792252 baseEnd_2792252 := by
    simpa [prefixWord, tailWord_2792252, baseEnd_2792252] using wordTrace_append hprefix tailTrace_2792252
  have hstable : (prefixWord ++ tailWord_2792252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2792252).length < 2 ^ (prefixWord ++ tailWord_2792252).sum := by decide
  have hdescent : baseEnd_2792252 < baseStart_2792252 := by decide
  rcases family_descends (prefixWord ++ tailWord_2792252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2792314 : List Nat := [3, 1, 1, 1, 1, 1, 3, 4, 4, 3]
def baseStart_2792314 : Nat := 118140960795 + 2792314 * 2 ^ 59
def prefixEnd_2792314 : Nat := 4983230072969 + 3 ^ 40 * 2792314 * 2
def baseEnd_2792314 : Nat := 955866146852462194888925

theorem tailTrace_2792314 : CollatzResearch.WordTrace tailWord_2792314 prefixEnd_2792314 955866146852462194888925 := by
  unfold tailWord_2792314
  simp only [CollatzResearch.WordTrace]
  refine ⟨25461014601482685527303999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67896038937287161406143997 25461014601482685527303999)
  ·
    refine ⟨38191521902224028290955999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25461014601482685527303999 38191521902224028290955999)
    ·
      refine ⟨57287282853336042436433999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38191521902224028290955999 57287282853336042436433999)
      ·
        refine ⟨85930924280004063654650999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57287282853336042436433999 85930924280004063654650999)
        ·
          refine ⟨128896386420006095481976499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85930924280004063654650999 128896386420006095481976499)
          ·
            refine ⟨193344579630009143222964749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128896386420006095481976499 193344579630009143222964749)
            ·
              refine ⟨72504217361253428708611781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 193344579630009143222964749 72504217361253428708611781)
              ·
                refine ⟨13594540755235017882864709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 72504217361253428708611781 13594540755235017882864709)
                ·
                  refine ⟨2548976391606565853037133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13594540755235017882864709 2548976391606565853037133)
                  ·
                    refine ⟨955866146852462194888925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2548976391606565853037133 955866146852462194888925)
                    ·
                      rfl

theorem cell22_2792314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 4, 4, 3].length) (baseStart_2792314 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2792314 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2792314 prefixEnd_2792314 := by exact prefixLift 2792314
  have htrace : WordTrace (prefixWord ++ tailWord_2792314) baseStart_2792314 baseEnd_2792314 := by
    simpa [prefixWord, tailWord_2792314, baseEnd_2792314] using wordTrace_append hprefix tailTrace_2792314
  have hstable : (prefixWord ++ tailWord_2792314).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2792314).length < 2 ^ (prefixWord ++ tailWord_2792314).sum := by decide
  have hdescent : baseEnd_2792314 < baseStart_2792314 := by decide
  rcases family_descends (prefixWord ++ tailWord_2792314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2792322 : List Nat := [3, 4, 2, 2, 2, 1, 1, 2, 5]
def baseStart_2792322 : Nat := 118140960795 + 2792322 * 2 ^ 59
def prefixEnd_2792322 : Nat := 4983230072969 + 3 ^ 40 * 2792322 * 2
def baseEnd_2792322 : Nat := 318622961805317613562967

theorem tailTrace_2792322 : CollatzResearch.WordTrace tailWord_2792322 prefixEnd_2792322 318622961805317613562967 := by
  unfold tailWord_2792322
  simp only [CollatzResearch.WordTrace]
  refine ⟨25461087547475439868876805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67896233459934506317004813 25461087547475439868876805)
  ·
    refine ⟨4773953915151644975414401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25461087547475439868876805 4773953915151644975414401)
    ·
      refine ⟨3580465436363733731560801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4773953915151644975414401 3580465436363733731560801)
      ·
        refine ⟨2685349077272800298670601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3580465436363733731560801 2685349077272800298670601)
        ·
          refine ⟨2014011807954600224002951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2685349077272800298670601 2014011807954600224002951)
          ·
            refine ⟨3021017711931900336004427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2014011807954600224002951 3021017711931900336004427)
            ·
              refine ⟨4531526567897850504006641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3021017711931900336004427 4531526567897850504006641)
              ·
                refine ⟨3398644925923387878004981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4531526567897850504006641 3398644925923387878004981)
                ·
                  refine ⟨318622961805317613562967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3398644925923387878004981 318622961805317613562967)
                  ·
                    rfl

theorem cell22_2792322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 1, 2, 5].length) (baseStart_2792322 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2792322 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2792322 prefixEnd_2792322 := by exact prefixLift 2792322
  have htrace : WordTrace (prefixWord ++ tailWord_2792322) baseStart_2792322 baseEnd_2792322 := by
    simpa [prefixWord, tailWord_2792322, baseEnd_2792322] using wordTrace_append hprefix tailTrace_2792322
  have hstable : (prefixWord ++ tailWord_2792322).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2792322).length < 2 ^ (prefixWord ++ tailWord_2792322).sum := by decide
  have hdescent : baseEnd_2792322 < baseStart_2792322 := by decide
  rcases family_descends (prefixWord ++ tailWord_2792322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2792331 : List Nat := [1, 1, 1, 1, 4, 2, 5, 2, 2, 3]
def baseStart_2792331 : Nat := 118140960795 + 2792331 * 2 ^ 59
def prefixEnd_2792331 : Nat := 4983230072969 + 3 ^ 40 * 2792331 * 2
def baseEnd_2792331 : Nat := 955871966299879817213873

theorem tailTrace_2792331 : CollatzResearch.WordTrace tailWord_2792331 prefixEnd_2792331 955871966299879817213873 := by
  unfold tailWord_2792331
  simp only [CollatzResearch.WordTrace]
  refine ⟨101844678446869154012584847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67896452297912769341723231 101844678446869154012584847)
  ·
    refine ⟨152767017670303731018877271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101844678446869154012584847 152767017670303731018877271)
    ·
      refine ⟨229150526505455596528315907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152767017670303731018877271 229150526505455596528315907)
      ·
        refine ⟨343725789758183394792473861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 229150526505455596528315907 343725789758183394792473861)
        ·
          refine ⟨64448585579659386523588849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 343725789758183394792473861 64448585579659386523588849)
          ·
            refine ⟨48336439184744539892691637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64448585579659386523588849 48336439184744539892691637)
            ·
              refine ⟨4531541173569800614939841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 48336439184744539892691637 4531541173569800614939841)
              ·
                refine ⟨3398655880177350461204881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4531541173569800614939841 3398655880177350461204881)
                ·
                  refine ⟨2548991910133012845903661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3398655880177350461204881 2548991910133012845903661)
                  ·
                    refine ⟨955871966299879817213873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2548991910133012845903661 955871966299879817213873)
                    ·
                      rfl

theorem cell22_2792331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 5, 2, 2, 3].length) (baseStart_2792331 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2792331 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2792331 prefixEnd_2792331 := by exact prefixLift 2792331
  have htrace : WordTrace (prefixWord ++ tailWord_2792331) baseStart_2792331 baseEnd_2792331 := by
    simpa [prefixWord, tailWord_2792331, baseEnd_2792331] using wordTrace_append hprefix tailTrace_2792331
  have hstable : (prefixWord ++ tailWord_2792331).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2792331).length < 2 ^ (prefixWord ++ tailWord_2792331).sum := by decide
  have hdescent : baseEnd_2792331 < baseStart_2792331 := by decide
  rcases family_descends (prefixWord ++ tailWord_2792331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2792348 : List Nat := [2, 2, 3, 3, 2, 2, 1, 1, 1, 5]
def baseStart_2792348 : Nat := 118140960795 + 2792348 * 2 ^ 59
def prefixEnd_2792348 : Nat := 4983230072969 + 3 ^ 40 * 2792348 * 2
def baseEnd_2792348 : Nat := 955877785747297439538821

theorem tailTrace_2792348 : CollatzResearch.WordTrace tailWord_2792348 prefixEnd_2792348 955877785747297439538821 := by
  unfold tailWord_2792348
  simp only [CollatzResearch.WordTrace]
  refine ⟨50922649243903782957976849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67896865658538377277302465 50922649243903782957976849)
  ·
    refine ⟨38191986932927837218482637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50922649243903782957976849 38191986932927837218482637)
    ·
      refine ⟨14321995099847938956930989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38191986932927837218482637 14321995099847938956930989)
      ·
        refine ⟨5370748162442977108849121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14321995099847938956930989 5370748162442977108849121)
        ·
          refine ⟨4028061121832232831636841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5370748162442977108849121 4028061121832232831636841)
          ·
            refine ⟨3021045841374174623727631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4028061121832232831636841 3021045841374174623727631)
            ·
              refine ⟨4531568762061261935591447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3021045841374174623727631 4531568762061261935591447)
              ·
                refine ⟨6797353143091892903387171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4531568762061261935591447 6797353143091892903387171)
                ·
                  refine ⟨10196029714637839355080757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6797353143091892903387171 10196029714637839355080757)
                  ·
                    refine ⟨955877785747297439538821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10196029714637839355080757 955877785747297439538821)
                    ·
                      rfl

theorem cell22_2792348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 1, 1, 1, 5].length) (baseStart_2792348 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2792348 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2792348 prefixEnd_2792348 := by exact prefixLift 2792348
  have htrace : WordTrace (prefixWord ++ tailWord_2792348) baseStart_2792348 baseEnd_2792348 := by
    simpa [prefixWord, tailWord_2792348, baseEnd_2792348] using wordTrace_append hprefix tailTrace_2792348
  have hstable : (prefixWord ++ tailWord_2792348).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2792348).length < 2 ^ (prefixWord ++ tailWord_2792348).sum := by decide
  have hdescent : baseEnd_2792348 < baseStart_2792348 := by decide
  rcases family_descends (prefixWord ++ tailWord_2792348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2792481 : List Nat := [1, 2, 3, 2, 3, 2, 1, 1, 1, 6]
def baseStart_2792481 : Nat := 118140960795 + 2792481 * 2 ^ 59
def prefixEnd_2792481 : Nat := 4983230072969 + 3 ^ 40 * 2792481 * 2
def baseEnd_2792481 : Nat := 955923314365329425963413

theorem tailTrace_2792481 : CollatzResearch.WordTrace tailWord_2792481 prefixEnd_2792481 955923314365329425963413 := by
  unfold tailWord_2792481
  simp only [CollatzResearch.WordTrace]
  refine ⟨101850149396325729630545297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67900099597550486420363531 101850149396325729630545297)
  ·
    refine ⟨76387612047244297222908973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101850149396325729630545297 76387612047244297222908973)
    ·
      refine ⟨28645354517716611458590865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76387612047244297222908973 28645354517716611458590865)
      ·
        refine ⟨21484015888287458593943149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28645354517716611458590865 21484015888287458593943149)
        ·
          refine ⟨8056505958107796972728681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21484015888287458593943149 8056505958107796972728681)
          ·
            refine ⟨6042379468580847729546511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8056505958107796972728681 6042379468580847729546511)
            ·
              refine ⟨9063569202871271594319767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6042379468580847729546511 9063569202871271594319767)
              ·
                refine ⟨13595353804306907391479651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9063569202871271594319767 13595353804306907391479651)
                ·
                  refine ⟨20393030706460361087219477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13595353804306907391479651 20393030706460361087219477)
                  ·
                    refine ⟨955923314365329425963413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20393030706460361087219477 955923314365329425963413)
                    ·
                      rfl

theorem cell22_2792481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 1, 1, 6].length) (baseStart_2792481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2792481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2792481 prefixEnd_2792481 := by exact prefixLift 2792481
  have htrace : WordTrace (prefixWord ++ tailWord_2792481) baseStart_2792481 baseEnd_2792481 := by
    simpa [prefixWord, tailWord_2792481, baseEnd_2792481] using wordTrace_append hprefix tailTrace_2792481
  have hstable : (prefixWord ++ tailWord_2792481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2792481).length < 2 ^ (prefixWord ++ tailWord_2792481).sum := by decide
  have hdescent : baseEnd_2792481 < baseStart_2792481 := by decide
  rcases family_descends (prefixWord ++ tailWord_2792481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2792487 : List Nat := [1, 1, 7, 1, 1, 3, 2, 1, 1, 4]
def baseStart_2792487 : Nat := 118140960795 + 2792487 * 2 ^ 59
def prefixEnd_2792487 : Nat := 4983230072969 + 3 ^ 40 * 2792487 * 2
def baseEnd_2792487 : Nat := 955925368287947410313395

theorem tailTrace_2792487 : CollatzResearch.WordTrace tailWord_2792487 prefixEnd_2792487 955925368287947410313395 := by
  unfold tailWord_2792487
  simp only [CollatzResearch.WordTrace]
  refine ⟨101850368234303992655263715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67900245489535995103509143 101850368234303992655263715)
  ·
    refine ⟨152775552351455988982895573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101850368234303992655263715 152775552351455988982895573)
    ·
      refine ⟨3580677008237249741786615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 152775552351455988982895573 3580677008237249741786615)
      ·
        refine ⟨5371015512355874612679923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3580677008237249741786615 5371015512355874612679923)
        ·
          refine ⟨8056523268533811919019885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5371015512355874612679923 8056523268533811919019885)
          ·
            refine ⟨3021196225700179469632457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8056523268533811919019885 3021196225700179469632457)
            ·
              refine ⟨2265897169275134602224343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3021196225700179469632457 2265897169275134602224343)
              ·
                refine ⟨3398845753912701903336515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2265897169275134602224343 3398845753912701903336515)
                ·
                  refine ⟨5098268630869052855004773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3398845753912701903336515 5098268630869052855004773)
                  ·
                    refine ⟨955925368287947410313395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5098268630869052855004773 955925368287947410313395)
                    ·
                      rfl

theorem cell22_2792487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 2, 1, 1, 4].length) (baseStart_2792487 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2792487 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2792487 prefixEnd_2792487 := by exact prefixLift 2792487
  have htrace : WordTrace (prefixWord ++ tailWord_2792487) baseStart_2792487 baseEnd_2792487 := by
    simpa [prefixWord, tailWord_2792487, baseEnd_2792487] using wordTrace_append hprefix tailTrace_2792487
  have hstable : (prefixWord ++ tailWord_2792487).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2792487).length < 2 ^ (prefixWord ++ tailWord_2792487).sum := by decide
  have hdescent : baseEnd_2792487 < baseStart_2792487 := by decide
  rcases family_descends (prefixWord ++ tailWord_2792487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2792500 : List Nat := [2, 5, 1, 2, 1, 2, 1, 1, 4, 3]
def baseStart_2792500 : Nat := 118140960795 + 2792500 * 2 ^ 59
def prefixEnd_2792500 : Nat := 4983230072969 + 3 ^ 40 * 2792500 * 2
def baseEnd_2792500 : Nat := 955929818453619709738355

theorem tailTrace_2792500 : CollatzResearch.WordTrace tailWord_2792500 prefixEnd_2792500 955929818453619709738355 := by
  unfold tailWord_2792500
  simp only [CollatzResearch.WordTrace]
  refine ⟨50925421191628447937743477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67900561588837930583657969 50925421191628447937743477)
  ·
    refine ⟨4774258236715166994163451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 50925421191628447937743477 4774258236715166994163451)
    ·
      refine ⟨7161387355072750491245177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4774258236715166994163451 7161387355072750491245177)
      ·
        refine ⟨5371040516304562868433883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7161387355072750491245177 5371040516304562868433883)
        ·
          refine ⟨8056560774456844302650825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5371040516304562868433883 8056560774456844302650825)
          ·
            refine ⟨6042420580842633226988119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8056560774456844302650825 6042420580842633226988119)
            ·
              refine ⟨9063630871263949840482179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6042420580842633226988119 9063630871263949840482179)
              ·
                refine ⟨13595446306895924760723269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9063630871263949840482179 13595446306895924760723269)
                ·
                  refine ⟨2549146182542985892635613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13595446306895924760723269 2549146182542985892635613)
                  ·
                    refine ⟨955929818453619709738355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2549146182542985892635613 955929818453619709738355)
                    ·
                      rfl

theorem cell22_2792500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 1, 4, 3].length) (baseStart_2792500 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2792500 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2792500 prefixEnd_2792500 := by exact prefixLift 2792500
  have htrace : WordTrace (prefixWord ++ tailWord_2792500) baseStart_2792500 baseEnd_2792500 := by
    simpa [prefixWord, tailWord_2792500, baseEnd_2792500] using wordTrace_append hprefix tailTrace_2792500
  have hstable : (prefixWord ++ tailWord_2792500).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2792500).length < 2 ^ (prefixWord ++ tailWord_2792500).sum := by decide
  have hdescent : baseEnd_2792500 < baseStart_2792500 := by decide
  rcases family_descends (prefixWord ++ tailWord_2792500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2792545 : List Nat := [1, 2, 3, 1, 1, 2, 5, 3, 1, 3]
def baseStart_2792545 : Nat := 118140960795 + 2792545 * 2 ^ 59
def prefixEnd_2792545 : Nat := 4983230072969 + 3 ^ 40 * 2792545 * 2
def baseEnd_2792545 : Nat := 955945222873254592363217

theorem tailTrace_2792545 : CollatzResearch.WordTrace tailWord_2792545 prefixEnd_2792545 955945222873254592363217 := by
  unfold tailWord_2792545
  simp only [CollatzResearch.WordTrace]
  refine ⟨101852483668093868560875089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67901655778729245707250059 101852483668093868560875089)
  ·
    refine ⟨76389362751070401420656317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101852483668093868560875089 76389362751070401420656317)
    ·
      refine ⟨28646011031651400532746119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76389362751070401420656317 28646011031651400532746119)
      ·
        refine ⟨42969016547477100799119179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28646011031651400532746119 42969016547477100799119179)
        ·
          refine ⟨64453524821215651198678769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42969016547477100799119179 64453524821215651198678769)
          ·
            refine ⟨48340143615911738399009077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64453524821215651198678769 48340143615911738399009077)
            ·
              refine ⟨4531888463991725474907101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 48340143615911738399009077 4531888463991725474907101)
              ·
                refine ⟨1699458173996897053090163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4531888463991725474907101 1699458173996897053090163)
                ·
                  refine ⟨2549187260995345579635245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1699458173996897053090163 2549187260995345579635245)
                  ·
                    refine ⟨955945222873254592363217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2549187260995345579635245 955945222873254592363217)
                    ·
                      rfl

theorem cell22_2792545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 5, 3, 1, 3].length) (baseStart_2792545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2792545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2792545 prefixEnd_2792545 := by exact prefixLift 2792545
  have htrace : WordTrace (prefixWord ++ tailWord_2792545) baseStart_2792545 baseEnd_2792545 := by
    simpa [prefixWord, tailWord_2792545, baseEnd_2792545] using wordTrace_append hprefix tailTrace_2792545
  have hstable : (prefixWord ++ tailWord_2792545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2792545).length < 2 ^ (prefixWord ++ tailWord_2792545).sum := by decide
  have hdescent : baseEnd_2792545 < baseStart_2792545 := by decide
  rcases family_descends (prefixWord ++ tailWord_2792545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2792562 : List Nat := [3, 2, 1, 2, 2, 1, 5, 2, 1, 3]
def baseStart_2792562 : Nat := 118140960795 + 2792562 * 2 ^ 59
def prefixEnd_2792562 : Nat := 4983230072969 + 3 ^ 40 * 2792562 * 2
def baseEnd_2792562 : Nat := 955951042320672214688165

theorem tailTrace_2792562 : CollatzResearch.WordTrace tailWord_2792562 prefixEnd_2792562 955951042320672214688165 := by
  unfold tailWord_2792562
  simp only [CollatzResearch.WordTrace]
  refine ⟨25463275927258070116060985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67902069139354853642829293 25463275927258070116060985)
  ·
    refine ⟨19097456945443552587045739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25463275927258070116060985 19097456945443552587045739)
    ·
      refine ⟨28646185418165328880568609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19097456945443552587045739 28646185418165328880568609)
      ·
        refine ⟨21484639063623996660426457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28646185418165328880568609 21484639063623996660426457)
        ·
          refine ⟨16113479297717997495319843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21484639063623996660426457 16113479297717997495319843)
          ·
            refine ⟨24170218946576996242979765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16113479297717997495319843 24170218946576996242979765)
            ·
              refine ⟨2265958026241593397779353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24170218946576996242979765 2265958026241593397779353)
              ·
                refine ⟨1699468519681195048334515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2265958026241593397779353 1699468519681195048334515)
                ·
                  refine ⟨2549202779521792572501773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1699468519681195048334515 2549202779521792572501773)
                  ·
                    refine ⟨955951042320672214688165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2549202779521792572501773 955951042320672214688165)
                    ·
                      rfl

theorem cell22_2792562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 5, 2, 1, 3].length) (baseStart_2792562 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2792562 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2792562 prefixEnd_2792562 := by exact prefixLift 2792562
  have htrace : WordTrace (prefixWord ++ tailWord_2792562) baseStart_2792562 baseEnd_2792562 := by
    simpa [prefixWord, tailWord_2792562, baseEnd_2792562] using wordTrace_append hprefix tailTrace_2792562
  have hstable : (prefixWord ++ tailWord_2792562).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2792562).length < 2 ^ (prefixWord ++ tailWord_2792562).sum := by decide
  have hdescent : baseEnd_2792562 < baseStart_2792562 := by decide
  rcases family_descends (prefixWord ++ tailWord_2792562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2792586 : List Nat := [3, 1, 2, 3, 1, 1, 2, 1, 8]
def baseStart_2792586 : Nat := 118140960795 + 2792586 * 2 ^ 59
def prefixEnd_2792586 : Nat := 4983230072969 + 3 ^ 40 * 2792586 * 2
def baseEnd_2792586 : Nat := 318653086003714717362697

theorem tailTrace_2792586 : CollatzResearch.WordTrace tailWord_2792586 prefixEnd_2792586 318653086003714717362697 := by
  unfold tailWord_2792586
  simp only [CollatzResearch.WordTrace]
  refine ⟨25463494765236333140779403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67902652707296888375411741 25463494765236333140779403)
  ·
    refine ⟨38195242147854499711169105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25463494765236333140779403 38195242147854499711169105)
    ·
      refine ⟨28646431610890874783376829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38195242147854499711169105 28646431610890874783376829)
      ·
        refine ⟨10742411854084078043766311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28646431610890874783376829 10742411854084078043766311)
        ·
          refine ⟨16113617781126117065649467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10742411854084078043766311 16113617781126117065649467)
          ·
            refine ⟨24170426671689175598474201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16113617781126117065649467 24170426671689175598474201)
            ·
              refine ⟨18127820003766881698855651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24170426671689175598474201 18127820003766881698855651)
              ·
                refine ⟨27191730005650322548283477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18127820003766881698855651 27191730005650322548283477)
                ·
                  refine ⟨318653086003714717362697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27191730005650322548283477 318653086003714717362697)
                  ·
                    rfl

theorem cell22_2792586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 1, 8].length) (baseStart_2792586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2792586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2792586 prefixEnd_2792586 := by exact prefixLift 2792586
  have htrace : WordTrace (prefixWord ++ tailWord_2792586) baseStart_2792586 baseEnd_2792586 := by
    simpa [prefixWord, tailWord_2792586, baseEnd_2792586] using wordTrace_append hprefix tailTrace_2792586
  have hstable : (prefixWord ++ tailWord_2792586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2792586).length < 2 ^ (prefixWord ++ tailWord_2792586).sum := by decide
  have hdescent : baseEnd_2792586 < baseStart_2792586 := by decide
  rcases family_descends (prefixWord ++ tailWord_2792586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2792605 : List Nat := [1, 4, 2, 1, 1, 2, 5, 1, 1, 4]
def baseStart_2792605 : Nat := 118140960795 + 2792605 * 2 ^ 59
def prefixEnd_2792605 : Nat := 4983230072969 + 3 ^ 40 * 2792605 * 2
def baseEnd_2792605 : Nat := 955965762099434435863033

theorem tailTrace_2792605 : CollatzResearch.WordTrace tailWord_2792605 prefixEnd_2792605 955965762099434435863033 := by
  unfold tailWord_2792605
  simp only [CollatzResearch.WordTrace]
  refine ⟨101854672047876498808059269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67903114698584332538706179 101854672047876498808059269)
  ·
    refine ⟨19097751008976843526511113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 101854672047876498808059269 19097751008976843526511113)
    ·
      refine ⟨14323313256732632644883335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19097751008976843526511113 14323313256732632644883335)
      ·
        refine ⟨21484969885098948967325003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14323313256732632644883335 21484969885098948967325003)
        ·
          refine ⟨32227454827648423450987505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21484969885098948967325003 32227454827648423450987505)
          ·
            refine ⟨24170591120736317588240629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32227454827648423450987505 24170591120736317588240629)
            ·
              refine ⟨2265992917569029773897559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24170591120736317588240629 2265992917569029773897559)
              ·
                refine ⟨3398989376353544660846339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2265992917569029773897559 3398989376353544660846339)
                ·
                  refine ⟨5098484064530316991269509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3398989376353544660846339 5098484064530316991269509)
                  ·
                    refine ⟨955965762099434435863033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5098484064530316991269509 955965762099434435863033)
                    ·
                      rfl

theorem cell22_2792605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 5, 1, 1, 4].length) (baseStart_2792605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2792605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2792605 prefixEnd_2792605 := by exact prefixLift 2792605
  have htrace : WordTrace (prefixWord ++ tailWord_2792605) baseStart_2792605 baseEnd_2792605 := by
    simpa [prefixWord, tailWord_2792605, baseEnd_2792605] using wordTrace_append hprefix tailTrace_2792605
  have hstable : (prefixWord ++ tailWord_2792605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2792605).length < 2 ^ (prefixWord ++ tailWord_2792605).sum := by decide
  have hdescent : baseEnd_2792605 < baseStart_2792605 := by decide
  rcases family_descends (prefixWord ++ tailWord_2792605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2792650 : List Nat := [3, 1, 2, 1, 3, 4, 1, 1, 2, 4]
def baseStart_2792650 : Nat := 118140960795 + 2792650 * 2 ^ 59
def prefixEnd_2792650 : Nat := 4983230072969 + 3 ^ 40 * 2792650 * 2
def baseEnd_2792650 : Nat := 955981166519069318487895

theorem tailTrace_2792650 : CollatzResearch.WordTrace tailWord_2792650 prefixEnd_2792650 955981166519069318487895 := by
  unfold tailWord_2792650
  simp only [CollatzResearch.WordTrace]
  refine ⟨25464078333178367873361851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67904208888475647662298269 25464078333178367873361851)
  ·
    refine ⟨38196117499767551810042777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25464078333178367873361851 38196117499767551810042777)
    ·
      refine ⟨28647088124825663857532083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38196117499767551810042777 28647088124825663857532083)
      ·
        refine ⟨42970632187238495786298125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28647088124825663857532083 42970632187238495786298125)
        ·
          refine ⟨16113987070214435919861797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42970632187238495786298125 16113987070214435919861797)
          ·
            refine ⟨3021372575665206734974087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16113987070214435919861797 3021372575665206734974087)
            ·
              refine ⟨4532058863497810102461131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3021372575665206734974087 4532058863497810102461131)
              ·
                refine ⟨6798088295246715153691697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4532058863497810102461131 6798088295246715153691697)
                ·
                  refine ⟨5098566221435036365268773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6798088295246715153691697 5098566221435036365268773)
                  ·
                    refine ⟨955981166519069318487895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5098566221435036365268773 955981166519069318487895)
                    ·
                      rfl

theorem cell22_2792650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 1, 1, 2, 4].length) (baseStart_2792650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2792650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2792650 prefixEnd_2792650 := by exact prefixLift 2792650
  have htrace : WordTrace (prefixWord ++ tailWord_2792650) baseStart_2792650 baseEnd_2792650 := by
    simpa [prefixWord, tailWord_2792650, baseEnd_2792650] using wordTrace_append hprefix tailTrace_2792650
  have hstable : (prefixWord ++ tailWord_2792650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2792650).length < 2 ^ (prefixWord ++ tailWord_2792650).sum := by decide
  have hdescent : baseEnd_2792650 < baseStart_2792650 := by decide
  rcases family_descends (prefixWord ++ tailWord_2792650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2792669 : List Nat := [1, 4, 3, 2, 2, 2, 1, 2, 2, 3]
def baseStart_2792669 : Nat := 118140960795 + 2792669 * 2 ^ 59
def prefixEnd_2792669 : Nat := 4983230072969 + 3 ^ 40 * 2792669 * 2
def baseEnd_2792669 : Nat := 955987670607359602262837

theorem tailTrace_2792669 : CollatzResearch.WordTrace tailWord_2792669 prefixEnd_2792669 955987670607359602262837 := by
  unfold tailWord_2792669
  simp only [CollatzResearch.WordTrace]
  refine ⟨101857006319644637738389061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67904670879763091825592707 101857006319644637738389061)
  ·
    refine ⟨19098188684933369575947949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 101857006319644637738389061 19098188684933369575947949)
    ·
      refine ⟨7161820756850013590980481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19098188684933369575947949 7161820756850013590980481)
      ·
        refine ⟨5371365567637510193235361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7161820756850013590980481 5371365567637510193235361)
        ·
          refine ⟨4028524175728132644926521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5371365567637510193235361 4028524175728132644926521)
          ·
            refine ⟨3021393131796099483694891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4028524175728132644926521 3021393131796099483694891)
            ·
              refine ⟨4532089697694149225542337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3021393131796099483694891 4532089697694149225542337)
              ·
                refine ⟨3399067273270611919156753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4532089697694149225542337 3399067273270611919156753)
                ·
                  refine ⟨2549300454952958939367565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3399067273270611919156753 2549300454952958939367565)
                  ·
                    refine ⟨955987670607359602262837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2549300454952958939367565 955987670607359602262837)
                    ·
                      rfl

theorem cell22_2792669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 1, 2, 2, 3].length) (baseStart_2792669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2792669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2792669 prefixEnd_2792669 := by exact prefixLift 2792669
  have htrace : WordTrace (prefixWord ++ tailWord_2792669) baseStart_2792669 baseEnd_2792669 := by
    simpa [prefixWord, tailWord_2792669, baseEnd_2792669] using wordTrace_append hprefix tailTrace_2792669
  have hstable : (prefixWord ++ tailWord_2792669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2792669).length < 2 ^ (prefixWord ++ tailWord_2792669).sum := by decide
  have hdescent : baseEnd_2792669 < baseStart_2792669 := by decide
  rcases family_descends (prefixWord ++ tailWord_2792669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2792680 : List Nat := [2, 1, 4, 1, 2, 1, 4, 1, 3, 3]
def baseStart_2792680 : Nat := 118140960795 + 2792680 * 2 ^ 59
def prefixEnd_2792680 : Nat := 4983230072969 + 3 ^ 40 * 2792680 * 2
def baseEnd_2792680 : Nat := 955991436132159240237803

theorem tailTrace_2792680 : CollatzResearch.WordTrace tailWord_2792680 prefixEnd_2792680 955991436132159240237803 := by
  unfold tailWord_2792680
  simp only [CollatzResearch.WordTrace]
  refine ⟨50928703761302393308519747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67904938348403191078026329 50928703761302393308519747)
  ·
    refine ⟨76393055641953589962779621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50928703761302393308519747 76393055641953589962779621)
    ·
      refine ⟨14323697932866298118021179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 76393055641953589962779621 14323697932866298118021179)
      ·
        refine ⟨21485546899299447177031769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14323697932866298118021179 21485546899299447177031769)
        ·
          refine ⟨16114160174474585382773827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21485546899299447177031769 16114160174474585382773827)
          ·
            refine ⟨24171240261711878074160741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16114160174474585382773827 24171240261711878074160741)
            ·
              refine ⟨4532107549070977138905139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24171240261711878074160741 4532107549070977138905139)
              ·
                refine ⟨6798161323606465708357709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4532107549070977138905139 6798161323606465708357709)
                ·
                  refine ⟨2549310496352424640634141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6798161323606465708357709 2549310496352424640634141)
                  ·
                    refine ⟨955991436132159240237803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2549310496352424640634141 955991436132159240237803)
                    ·
                      rfl

theorem cell22_2792680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 4, 1, 3, 3].length) (baseStart_2792680 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2792680 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2792680 prefixEnd_2792680 := by exact prefixLift 2792680
  have htrace : WordTrace (prefixWord ++ tailWord_2792680) baseStart_2792680 baseEnd_2792680 := by
    simpa [prefixWord, tailWord_2792680, baseEnd_2792680] using wordTrace_append hprefix tailTrace_2792680
  have hstable : (prefixWord ++ tailWord_2792680).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2792680).length < 2 ^ (prefixWord ++ tailWord_2792680).sum := by decide
  have hdescent : baseEnd_2792680 < baseStart_2792680 := by decide
  rcases family_descends (prefixWord ++ tailWord_2792680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2792757 : List Nat := [1, 3, 3, 1, 2, 4, 1, 2, 1, 4]
def baseStart_2792757 : Nat := 118140960795 + 2792757 * 2 ^ 59
def prefixEnd_2792757 : Nat := 4983230072969 + 3 ^ 40 * 2792757 * 2
def baseEnd_2792757 : Nat := 956017794805756706062567

theorem tailTrace_2792757 : CollatzResearch.WordTrace tailWord_2792757 prefixEnd_2792757 956017794805756706062567 := by
  unfold tailWord_2792757
  simp only [CollatzResearch.WordTrace]
  refine ⟨101860215943325828767592525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67906810628883885845061683 101860215943325828767592525)
  ·
    refine ⟨38197580978747185787847197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101860215943325828767592525 38197580978747185787847197)
    ·
      refine ⟨14324092867030194670442699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38197580978747185787847197 14324092867030194670442699)
      ·
        refine ⟨21486139300545292005664049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14324092867030194670442699 21486139300545292005664049)
        ·
          refine ⟨16114604475408969004248037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21486139300545292005664049 16114604475408969004248037)
          ·
            refine ⟨3021488339139181688296507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16114604475408969004248037 3021488339139181688296507)
            ·
              refine ⟨4532232508708772532444761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3021488339139181688296507 4532232508708772532444761)
              ·
                refine ⟨3399174381531579399333571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4532232508708772532444761 3399174381531579399333571)
                ·
                  refine ⟨5098761572297369099000357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3399174381531579399333571 5098761572297369099000357)
                  ·
                    refine ⟨956017794805756706062567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5098761572297369099000357 956017794805756706062567)
                    ·
                      rfl

theorem cell22_2792757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 1, 2, 1, 4].length) (baseStart_2792757 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2792757 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2792757 prefixEnd_2792757 := by exact prefixLift 2792757
  have htrace : WordTrace (prefixWord ++ tailWord_2792757) baseStart_2792757 baseEnd_2792757 := by
    simpa [prefixWord, tailWord_2792757, baseEnd_2792757] using wordTrace_append hprefix tailTrace_2792757
  have hstable : (prefixWord ++ tailWord_2792757).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2792757).length < 2 ^ (prefixWord ++ tailWord_2792757).sum := by decide
  have hdescent : baseEnd_2792757 < baseStart_2792757 := by decide
  rcases family_descends (prefixWord ++ tailWord_2792757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2792789 : List Nat := [1, 3, 2, 2, 3, 3, 2, 2, 4]
def baseStart_2792789 : Nat := 118140960795 + 2792789 * 2 ^ 59
def prefixEnd_2792789 : Nat := 4983230072969 + 3 ^ 40 * 2792789 * 2
def baseEnd_2792789 : Nat := 318676249686573096420823

theorem tailTrace_2792789 : CollatzResearch.WordTrace tailWord_2792789 prefixEnd_2792789 318676249686573096420823 := by
  unfold tailWord_2792789
  simp only [CollatzResearch.WordTrace]
  refine ⟨101861383079209898232757421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67907588719473265488504947 101861383079209898232757421)
  ·
    refine ⟨38198018654703711837284033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101861383079209898232757421 38198018654703711837284033)
    ·
      refine ⟨28648513991027783877963025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38198018654703711837284033 28648513991027783877963025)
      ·
        refine ⟨21486385493270837908472269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28648513991027783877963025 21486385493270837908472269)
        ·
          refine ⟨8057394559976564215677101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21486385493270837908472269 8057394559976564215677101)
          ·
            refine ⟨3021522959991211580878913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8057394559976564215677101 3021522959991211580878913)
            ·
              refine ⟨2266142219993408685659185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3021522959991211580878913 2266142219993408685659185)
              ·
                refine ⟨1699606664995056514244389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2266142219993408685659185 1699606664995056514244389)
                ·
                  refine ⟨318676249686573096420823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1699606664995056514244389 318676249686573096420823)
                  ·
                    rfl

theorem cell22_2792789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 2, 2, 4].length) (baseStart_2792789 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2792789 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2792789 prefixEnd_2792789 := by exact prefixLift 2792789
  have htrace : WordTrace (prefixWord ++ tailWord_2792789) baseStart_2792789 baseEnd_2792789 := by
    simpa [prefixWord, tailWord_2792789, baseEnd_2792789] using wordTrace_append hprefix tailTrace_2792789
  have hstable : (prefixWord ++ tailWord_2792789).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2792789).length < 2 ^ (prefixWord ++ tailWord_2792789).sum := by decide
  have hdescent : baseEnd_2792789 < baseStart_2792789 := by decide
  rcases family_descends (prefixWord ++ tailWord_2792789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2792800 : List Nat := [2, 1, 1, 3, 4, 3, 1, 7]
def baseStart_2792800 : Nat := 118140960795 + 2792800 * 2 ^ 59
def prefixEnd_2792800 : Nat := 4983230072969 + 3 ^ 40 * 2792800 * 2
def baseEnd_2792800 : Nat := 106225834953835436359715

theorem tailTrace_2792800 : CollatzResearch.WordTrace tailWord_2792800 prefixEnd_2792800 106225834953835436359715 := by
  unfold tailWord_2792800
  simp only [CollatzResearch.WordTrace]
  refine ⟨50930892141085023555703927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67907856188113364740938569 50930892141085023555703927)
  ·
    refine ⟨76396338211627535333555891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50930892141085023555703927 76396338211627535333555891)
    ·
      refine ⟨114594507317441303000333837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76396338211627535333555891 114594507317441303000333837)
      ·
        refine ⟨42972940244040488625125189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 114594507317441303000333837 42972940244040488625125189)
        ·
          refine ⟨8057426295757591617210973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42972940244040488625125189 8057426295757591617210973)
          ·
            refine ⟨3021534860909096856454115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8057426295757591617210973 3021534860909096856454115)
            ·
              refine ⟨4532302291363645284681173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3021534860909096856454115 4532302291363645284681173)
              ·
                refine ⟨106225834953835436359715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4532302291363645284681173 106225834953835436359715)
                ·
                  rfl

theorem cell22_2792800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 1, 7].length) (baseStart_2792800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2792800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2792800 prefixEnd_2792800 := by exact prefixLift 2792800
  have htrace : WordTrace (prefixWord ++ tailWord_2792800) baseStart_2792800 baseEnd_2792800 := by
    simpa [prefixWord, tailWord_2792800, baseEnd_2792800] using wordTrace_append hprefix tailTrace_2792800
  have hstable : (prefixWord ++ tailWord_2792800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2792800).length < 2 ^ (prefixWord ++ tailWord_2792800).sum := by decide
  have hdescent : baseEnd_2792800 < baseStart_2792800 := by decide
  rcases family_descends (prefixWord ++ tailWord_2792800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2792815 : List Nat := [1, 1, 2, 1, 3, 1, 5, 2, 3, 3]
def baseStart_2792815 : Nat := 118140960795 + 2792815 * 2 ^ 59
def prefixEnd_2792815 : Nat := 4983230072969 + 3 ^ 40 * 2792815 * 2
def baseEnd_2792815 : Nat := 956037649391063888112389

theorem tailTrace_2792815 : CollatzResearch.WordTrace tailWord_2792815 prefixEnd_2792815 956037649391063888112389 := by
  unfold tailWord_2792815
  simp only [CollatzResearch.WordTrace]
  refine ⟨101862331377115704673203899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67908220918077136448802599 101862331377115704673203899)
  ·
    refine ⟨152793497065673557009805849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101862331377115704673203899 152793497065673557009805849)
    ·
      refine ⟨114595122799255167757354387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152793497065673557009805849 114595122799255167757354387)
      ·
        refine ⟨171892684198882751636031581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114595122799255167757354387 171892684198882751636031581)
        ·
          refine ⟨64459756574581031863511843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 171892684198882751636031581 64459756574581031863511843)
          ·
            refine ⟨96689634861871547795267765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64459756574581031863511843 96689634861871547795267765)
            ·
              refine ⟨9064653268300457605806353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 96689634861871547795267765 9064653268300457605806353)
              ·
                refine ⟨6798489951225343204354765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9064653268300457605806353 6798489951225343204354765)
                ·
                  refine ⟨2549433731709503701633037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6798489951225343204354765 2549433731709503701633037)
                  ·
                    refine ⟨956037649391063888112389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2549433731709503701633037 956037649391063888112389)
                    ·
                      rfl

theorem cell22_2792815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 2, 3, 3].length) (baseStart_2792815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2792815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2792815 prefixEnd_2792815 := by exact prefixLift 2792815
  have htrace : WordTrace (prefixWord ++ tailWord_2792815) baseStart_2792815 baseEnd_2792815 := by
    simpa [prefixWord, tailWord_2792815, baseEnd_2792815] using wordTrace_append hprefix tailTrace_2792815
  have hstable : (prefixWord ++ tailWord_2792815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2792815).length < 2 ^ (prefixWord ++ tailWord_2792815).sum := by decide
  have hdescent : baseEnd_2792815 < baseStart_2792815 := by decide
  rcases family_descends (prefixWord ++ tailWord_2792815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2792828 : List Nat := [2, 2, 2, 1, 1, 1, 4, 2, 7]
def baseStart_2792828 : Nat := 118140960795 + 2792828 * 2 ^ 59
def prefixEnd_2792828 : Nat := 4983230072969 + 3 ^ 40 * 2792828 * 2
def baseEnd_2792828 : Nat := 318680699852245395845783

theorem tailTrace_2792828 : CollatzResearch.WordTrace tailWord_2792828 prefixEnd_2792828 318680699852245395845783 := by
  unfold tailWord_2792828
  simp only [CollatzResearch.WordTrace]
  refine ⟨50931402763034303946713569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67908537017379071928951425 50931402763034303946713569)
  ·
    refine ⟨38198552072275727960035177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50931402763034303946713569 38198552072275727960035177)
    ·
      refine ⟨28648914054206795970026383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38198552072275727960035177 28648914054206795970026383)
      ·
        refine ⟨42973371081310193955039575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28648914054206795970026383 42973371081310193955039575)
        ·
          refine ⟨64460056621965290932559363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42973371081310193955039575 64460056621965290932559363)
          ·
            refine ⟨96690084932947936398839045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64460056621965290932559363 96690084932947936398839045)
            ·
              refine ⟨18129390924927738074782321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 96690084932947936398839045 18129390924927738074782321)
              ·
                refine ⟨13597043193695803556086741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18129390924927738074782321 13597043193695803556086741)
                ·
                  refine ⟨318680699852245395845783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13597043193695803556086741 318680699852245395845783)
                  ·
                    rfl

theorem cell22_2792828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 2, 7].length) (baseStart_2792828 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2792828 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2792828 prefixEnd_2792828 := by exact prefixLift 2792828
  have htrace : WordTrace (prefixWord ++ tailWord_2792828) baseStart_2792828 baseEnd_2792828 := by
    simpa [prefixWord, tailWord_2792828, baseEnd_2792828] using wordTrace_append hprefix tailTrace_2792828
  have hstable : (prefixWord ++ tailWord_2792828).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2792828).length < 2 ^ (prefixWord ++ tailWord_2792828).sum := by decide
  have hdescent : baseEnd_2792828 < baseStart_2792828 := by decide
  rcases family_descends (prefixWord ++ tailWord_2792828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2792843 : List Nat := [1, 1, 1, 1, 4, 3, 1, 1, 4, 5]
def baseStart_2792843 : Nat := 118140960795 + 2792843 * 2 ^ 59
def prefixEnd_2792843 : Nat := 4983230072969 + 3 ^ 40 * 2792843 * 2
def baseEnd_2792843 : Nat := 956047234363281148412303

theorem tailTrace_2792843 : CollatzResearch.WordTrace tailWord_2792843 prefixEnd_2792843 956047234363281148412303 := by
  unfold tailWord_2792843
  simp only [CollatzResearch.WordTrace]
  refine ⟨101863352621014265455223183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67908901747342843636815455 101863352621014265455223183)
  ·
    refine ⟨152795028931521398182834775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101863352621014265455223183 152795028931521398182834775)
    ·
      refine ⟨229192543397282097274252163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152795028931521398182834775 229192543397282097274252163)
      ·
        refine ⟨343788815095923145911378245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 229192543397282097274252163 343788815095923145911378245)
        ·
          refine ⟨64460402830485589858383421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 343788815095923145911378245 64460402830485589858383421)
          ·
            refine ⟨24172651061432096196893783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64460402830485589858383421 24172651061432096196893783)
            ·
              refine ⟨36258976592148144295340675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24172651061432096196893783 36258976592148144295340675)
              ·
                refine ⟨54388464888222216443011013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36258976592148144295340675 54388464888222216443011013)
                ·
                  refine ⟨10197837166541665583064565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 54388464888222216443011013 10197837166541665583064565)
                  ·
                    refine ⟨956047234363281148412303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10197837166541665583064565 956047234363281148412303)
                    ·
                      rfl

theorem cell22_2792843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 1, 4, 5].length) (baseStart_2792843 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2792843 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2792843 prefixEnd_2792843 := by exact prefixLift 2792843
  have htrace : WordTrace (prefixWord ++ tailWord_2792843) baseStart_2792843 baseEnd_2792843 := by
    simpa [prefixWord, tailWord_2792843, baseEnd_2792843] using wordTrace_append hprefix tailTrace_2792843
  have hstable : (prefixWord ++ tailWord_2792843).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2792843).length < 2 ^ (prefixWord ++ tailWord_2792843).sum := by decide
  have hdescent : baseEnd_2792843 < baseStart_2792843 := by decide
  rcases family_descends (prefixWord ++ tailWord_2792843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2792935 : List Nat := [1, 1, 5, 2, 1, 2, 2, 8]
def baseStart_2792935 : Nat := 118140960795 + 2792935 * 2 ^ 59
def prefixEnd_2792935 : Nat := 4983230072969 + 3 ^ 40 * 2792935 * 2
def baseEnd_2792935 : Nat := 106230969760380397234669

theorem tailTrace_2792935 : CollatzResearch.WordTrace tailWord_2792935 prefixEnd_2792935 106230969760380397234669 := by
  unfold tailWord_2792935
  simp only [CollatzResearch.WordTrace]
  refine ⟨101866708136680965167572259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67911138757787310111714839 101866708136680965167572259)
  ·
    refine ⟨152800062205021447751358389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101866708136680965167572259 152800062205021447751358389)
    ·
      refine ⟨14325005831720760726689849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 152800062205021447751358389 14325005831720760726689849)
      ·
        refine ⟨10743754373790570545017387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14325005831720760726689849 10743754373790570545017387)
        ·
          refine ⟨16115631560685855817526081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10743754373790570545017387 16115631560685855817526081)
          ·
            refine ⟨12086723670514391863144561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16115631560685855817526081 12086723670514391863144561)
            ·
              refine ⟨9065042752885793897358421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12086723670514391863144561 9065042752885793897358421)
              ·
                refine ⟨106230969760380397234669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9065042752885793897358421 106230969760380397234669)
                ·
                  rfl

theorem cell22_2792935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 8].length) (baseStart_2792935 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2792935 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2792935 prefixEnd_2792935 := by exact prefixLift 2792935
  have htrace : WordTrace (prefixWord ++ tailWord_2792935) baseStart_2792935 baseEnd_2792935 := by
    simpa [prefixWord, tailWord_2792935, baseEnd_2792935] using wordTrace_append hprefix tailTrace_2792935
  have hstable : (prefixWord ++ tailWord_2792935).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2792935).length < 2 ^ (prefixWord ++ tailWord_2792935).sum := by decide
  have hdescent : baseEnd_2792935 < baseStart_2792935 := by decide
  rcases family_descends (prefixWord ++ tailWord_2792935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2792984 : List Nat := [2, 1, 2, 3, 4, 1, 1, 2, 3, 3]
def baseStart_2792984 : Nat := 118140960795 + 2792984 * 2 ^ 59
def prefixEnd_2792984 : Nat := 4983230072969 + 3 ^ 40 * 2792984 * 2
def baseEnd_2792984 : Nat := 956095501544803780636871

theorem tailTrace_2792984 : CollatzResearch.WordTrace tailWord_2792984 prefixEnd_2792984 956095501544803780636871 := by
  unfold tailWord_2792984
  simp only [CollatzResearch.WordTrace]
  refine ⟨50934247656751723268053003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67912330209002297690737337 50934247656751723268053003)
  ·
    refine ⟨76401371485127584902079505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50934247656751723268053003 76401371485127584902079505)
    ·
      refine ⟨57301028613845688676559629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76401371485127584902079505 57301028613845688676559629)
      ·
        refine ⟨21487885730192133253709861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57301028613845688676559629 21487885730192133253709861)
        ·
          refine ⟨4028978574411024985070599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21487885730192133253709861 4028978574411024985070599)
          ·
            refine ⟨6043467861616537477605899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4028978574411024985070599 6043467861616537477605899)
            ·
              refine ⟨9065201792424806216408849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6043467861616537477605899 9065201792424806216408849)
              ·
                refine ⟨6798901344318604662306637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9065201792424806216408849 6798901344318604662306637)
                ·
                  refine ⟨2549588004119476748364989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6798901344318604662306637 2549588004119476748364989)
                  ·
                    refine ⟨956095501544803780636871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2549588004119476748364989 956095501544803780636871)
                    ·
                      rfl

theorem cell22_2792984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 2, 3, 3].length) (baseStart_2792984 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2792984 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2792984 prefixEnd_2792984 := by exact prefixLift 2792984
  have htrace : WordTrace (prefixWord ++ tailWord_2792984) baseStart_2792984 baseEnd_2792984 := by
    simpa [prefixWord, tailWord_2792984, baseEnd_2792984] using wordTrace_append hprefix tailTrace_2792984
  have hstable : (prefixWord ++ tailWord_2792984).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2792984).length < 2 ^ (prefixWord ++ tailWord_2792984).sum := by decide
  have hdescent : baseEnd_2792984 < baseStart_2792984 := by decide
  rcases family_descends (prefixWord ++ tailWord_2792984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2793014 : List Nat := [5, 1, 2, 1, 3, 1, 1, 1, 7]
def baseStart_2793014 : Nat := 118140960795 + 2793014 * 2 ^ 59
def prefixEnd_2793014 : Nat := 4983230072969 + 3 ^ 40 * 2793014 * 2
def baseEnd_2793014 : Nat := 318701923719297900795593

theorem tailTrace_2793014 : CollatzResearch.WordTrace tailWord_2793014 prefixEnd_2793014 318701923719297900795593 := by
  unfold tailWord_2793014
  simp only [CollatzResearch.WordTrace]
  refine ⟨6366849343962172603731131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 67913059668929841106465397 6366849343962172603731131)
  ·
    refine ⟨9550274015943258905596697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6366849343962172603731131 9550274015943258905596697)
    ·
      refine ⟨7162705511957444179197523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9550274015943258905596697 7162705511957444179197523)
      ·
        refine ⟨10744058267936166268796285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7162705511957444179197523 10744058267936166268796285)
        ·
          refine ⟨4029021850476062350798607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10744058267936166268796285 4029021850476062350798607)
          ·
            refine ⟨6043532775714093526197911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4029021850476062350798607 6043532775714093526197911)
            ·
              refine ⟨9065299163571140289296867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6043532775714093526197911 9065299163571140289296867)
              ·
                refine ⟨13597948745356710433945301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9065299163571140289296867 13597948745356710433945301)
                ·
                  refine ⟨318701923719297900795593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13597948745356710433945301 318701923719297900795593)
                  ·
                    rfl

theorem cell22_2793014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 1, 7].length) (baseStart_2793014 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2793014 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2793014 prefixEnd_2793014 := by exact prefixLift 2793014
  have htrace : WordTrace (prefixWord ++ tailWord_2793014) baseStart_2793014 baseEnd_2793014 := by
    simpa [prefixWord, tailWord_2793014, baseEnd_2793014] using wordTrace_append hprefix tailTrace_2793014
  have hstable : (prefixWord ++ tailWord_2793014).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2793014).length < 2 ^ (prefixWord ++ tailWord_2793014).sum := by decide
  have hdescent : baseEnd_2793014 < baseStart_2793014 := by decide
  rcases family_descends (prefixWord ++ tailWord_2793014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2793042 : List Nat := [3, 2, 2, 1, 2, 2, 2, 2, 6]
def baseStart_2793042 : Nat := 118140960795 + 2793042 * 2 ^ 59
def prefixEnd_2793042 : Nat := 4983230072969 + 3 ^ 40 * 2793042 * 2
def baseEnd_2793042 : Nat := 318705118710036987562231

theorem tailTrace_2793042 : CollatzResearch.WordTrace tailWord_2793042 prefixEnd_2793042 318705118710036987562231 := by
  unfold tailWord_2793042
  simp only [CollatzResearch.WordTrace]
  refine ⟨25467652686823330610429345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67913740498195548294478253 25467652686823330610429345)
  ·
    refine ⟨19100739515117497957822009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25467652686823330610429345 19100739515117497957822009)
    ·
      refine ⟨14325554636338123468366507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19100739515117497957822009 14325554636338123468366507)
      ·
        refine ⟨21488331954507185202549761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14325554636338123468366507 21488331954507185202549761)
        ·
          refine ⟨16116248965880388901912321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21488331954507185202549761 16116248965880388901912321)
          ·
            refine ⟨12087186724410291676434241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16116248965880388901912321 12087186724410291676434241)
            ·
              refine ⟨9065390043307718757325681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12087186724410291676434241 9065390043307718757325681)
              ·
                refine ⟨6799042532480789067994261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9065390043307718757325681 6799042532480789067994261)
                ·
                  refine ⟨318705118710036987562231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6799042532480789067994261 318705118710036987562231)
                  ·
                    rfl

theorem cell22_2793042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 2, 6].length) (baseStart_2793042 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2793042 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2793042 prefixEnd_2793042 := by exact prefixLift 2793042
  have htrace : WordTrace (prefixWord ++ tailWord_2793042) baseStart_2793042 baseEnd_2793042 := by
    simpa [prefixWord, tailWord_2793042, baseEnd_2793042] using wordTrace_append hprefix tailTrace_2793042
  have hstable : (prefixWord ++ tailWord_2793042).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2793042).length < 2 ^ (prefixWord ++ tailWord_2793042).sum := by decide
  have hdescent : baseEnd_2793042 < baseStart_2793042 := by decide
  rcases family_descends (prefixWord ++ tailWord_2793042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2793044 : List Nat := [2, 4, 1, 1, 1, 2, 4, 2, 1, 4]
def baseStart_2793044 : Nat := 118140960795 + 2793044 * 2 ^ 59
def prefixEnd_2793044 : Nat := 4983230072969 + 3 ^ 40 * 2793044 * 2
def baseEnd_2793044 : Nat := 956116040770983624136687

theorem tailTrace_2793044 : CollatzResearch.WordTrace tailWord_2793044 prefixEnd_2793044 956116040770983624136687 := by
  unfold tailWord_2793044
  simp only [CollatzResearch.WordTrace]
  refine ⟨50935341846643038391645093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67913789128857384522193457 50935341846643038391645093)
  ·
    refine ⟨9550376596245569698433455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50935341846643038391645093 9550376596245569698433455)
    ·
      refine ⟨14325564894368354547650183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9550376596245569698433455 14325564894368354547650183)
      ·
        refine ⟨21488347341552531821475275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14325564894368354547650183 21488347341552531821475275)
        ·
          refine ⟨32232521012328797732212913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21488347341552531821475275 32232521012328797732212913)
          ·
            refine ⟨24174390759246598299159685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32232521012328797732212913 24174390759246598299159685)
            ·
              refine ⟨4532698267358737181092441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24174390759246598299159685 4532698267358737181092441)
              ·
                refine ⟨3399523700519052885819331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4532698267358737181092441 3399523700519052885819331)
                ·
                  refine ⟨5099285550778579328728997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3399523700519052885819331 5099285550778579328728997)
                  ·
                    refine ⟨956116040770983624136687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5099285550778579328728997 956116040770983624136687)
                    ·
                      rfl

theorem cell22_2793044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 4, 2, 1, 4].length) (baseStart_2793044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2793044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2793044 prefixEnd_2793044 := by exact prefixLift 2793044
  have htrace : WordTrace (prefixWord ++ tailWord_2793044) baseStart_2793044 baseEnd_2793044 := by
    simpa [prefixWord, tailWord_2793044, baseEnd_2793044] using wordTrace_append hprefix tailTrace_2793044
  have hstable : (prefixWord ++ tailWord_2793044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2793044).length < 2 ^ (prefixWord ++ tailWord_2793044).sum := by decide
  have hdescent : baseEnd_2793044 < baseStart_2793044 := by decide
  rcases family_descends (prefixWord ++ tailWord_2793044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2793057 : List Nat := [1, 2, 3, 1, 1, 3, 1, 1, 6, 3]
def baseStart_2793057 : Nat := 118140960795 + 2793057 * 2 ^ 59
def prefixEnd_2793057 : Nat := 4983230072969 + 3 ^ 40 * 2793057 * 2
def baseEnd_2793057 : Nat := 956120490936655923561647

theorem tailTrace_2793057 : CollatzResearch.WordTrace tailWord_2793057 prefixEnd_2793057 956120490936655923561647 := by
  unfold tailWord_2793057
  simp only [CollatzResearch.WordTrace]
  refine ⟨101871157842238980003513425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67914105228159320002342283 101871157842238980003513425)
  ·
    refine ⟨76403368381679235002635069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101871157842238980003513425 76403368381679235002635069)
    ·
      refine ⟨28651263143129713125988151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76403368381679235002635069 28651263143129713125988151)
      ·
        refine ⟨42976894714694569688982227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28651263143129713125988151 42976894714694569688982227)
        ·
          refine ⟨64465342072041854533473341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42976894714694569688982227 64465342072041854533473341)
          ·
            refine ⟨24174503277015695450052503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64465342072041854533473341 24174503277015695450052503)
            ·
              refine ⟨36261754915523543175078755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24174503277015695450052503 36261754915523543175078755)
              ·
                refine ⟨54392632373285314762618133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36261754915523543175078755 54392632373285314762618133)
                ·
                  refine ⟨2549654642497749129497725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 54392632373285314762618133 2549654642497749129497725)
                  ·
                    refine ⟨956120490936655923561647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2549654642497749129497725 956120490936655923561647)
                    ·
                      rfl

theorem cell22_2793057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 1, 6, 3].length) (baseStart_2793057 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2793057 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2793057 prefixEnd_2793057 := by exact prefixLift 2793057
  have htrace : WordTrace (prefixWord ++ tailWord_2793057) baseStart_2793057 baseEnd_2793057 := by
    simpa [prefixWord, tailWord_2793057, baseEnd_2793057] using wordTrace_append hprefix tailTrace_2793057
  have hstable : (prefixWord ++ tailWord_2793057).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2793057).length < 2 ^ (prefixWord ++ tailWord_2793057).sum := by decide
  have hdescent : baseEnd_2793057 < baseStart_2793057 := by decide
  rcases family_descends (prefixWord ++ tailWord_2793057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2793059 : List Nat := [1, 1, 1, 5, 1, 3, 3, 3, 4]
def baseStart_2793059 : Nat := 118140960795 + 2793059 * 2 ^ 59
def prefixEnd_2793059 : Nat := 4983230072969 + 3 ^ 40 * 2793059 * 2
def baseEnd_2793059 : Nat := 318707058525842861670547

theorem tailTrace_2793059 : CollatzResearch.WordTrace tailWord_2793059 prefixEnd_2793059 318707058525842861670547 := by
  unfold tailWord_2793059
  simp only [CollatzResearch.WordTrace]
  refine ⟨101871230788231734345086231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67914153858821156230057487 101871230788231734345086231)
  ·
    refine ⟨152806846182347601517629347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101871230788231734345086231 152806846182347601517629347)
    ·
      refine ⟨229210269273521402276444021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152806846182347601517629347 229210269273521402276444021)
      ·
        refine ⟨21488462744392631463416627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 229210269273521402276444021 21488462744392631463416627)
        ·
          refine ⟨32232694116588947195124941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21488462744392631463416627 32232694116588947195124941)
          ·
            refine ⟨12087260293720855198171853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32232694116588947195124941 12087260293720855198171853)
            ·
              refine ⟨4532722610145320699314445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12087260293720855198171853 4532722610145320699314445)
              ·
                refine ⟨1699770978804495262242917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4532722610145320699314445 1699770978804495262242917)
                ·
                  refine ⟨318707058525842861670547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1699770978804495262242917 318707058525842861670547)
                  ·
                    rfl

theorem cell22_2793059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 3, 3, 4].length) (baseStart_2793059 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2793059 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2793059 prefixEnd_2793059 := by exact prefixLift 2793059
  have htrace : WordTrace (prefixWord ++ tailWord_2793059) baseStart_2793059 baseEnd_2793059 := by
    simpa [prefixWord, tailWord_2793059, baseEnd_2793059] using wordTrace_append hprefix tailTrace_2793059
  have hstable : (prefixWord ++ tailWord_2793059).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2793059).length < 2 ^ (prefixWord ++ tailWord_2793059).sum := by decide
  have hdescent : baseEnd_2793059 < baseStart_2793059 := by decide
  rcases family_descends (prefixWord ++ tailWord_2793059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2793072 : List Nat := [2, 1, 1, 1, 6, 1, 1, 1, 4, 4]
def baseStart_2793072 : Nat := 118140960795 + 2793072 * 2 ^ 59
def prefixEnd_2793072 : Nat := 4983230072969 + 3 ^ 40 * 2793072 * 2
def baseEnd_2793072 : Nat := 956125625743200884436601

theorem tailTrace_2793072 : CollatzResearch.WordTrace tailWord_2793072 prefixEnd_2793072 956125625743200884436601 := by
  unfold tailWord_2793072
  simp only [CollatzResearch.WordTrace]
  refine ⟨50935852468592318782654735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67914469958123091710206313 50935852468592318782654735)
  ·
    refine ⟨76403778702888478173982103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50935852468592318782654735 76403778702888478173982103)
    ·
      refine ⟨114605668054332717260973155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76403778702888478173982103 114605668054332717260973155)
      ·
        refine ⟨171908502081499075891459733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114605668054332717260973155 171908502081499075891459733)
        ·
          refine ⟨8058211035070269182412175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 171908502081499075891459733 8058211035070269182412175)
          ·
            refine ⟨12087316552605403773618263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8058211035070269182412175 12087316552605403773618263)
            ·
              refine ⟨18130974828908105660427395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12087316552605403773618263 18130974828908105660427395)
              ·
                refine ⟨27196462243362158490641093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18130974828908105660427395 27196462243362158490641093)
                ·
                  refine ⟨5099336670630404716995205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27196462243362158490641093 5099336670630404716995205)
                  ·
                    refine ⟨956125625743200884436601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5099336670630404716995205 956125625743200884436601)
                    ·
                      rfl

theorem cell22_2793072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 1, 4, 4].length) (baseStart_2793072 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2793072 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2793072 prefixEnd_2793072 := by exact prefixLift 2793072
  have htrace : WordTrace (prefixWord ++ tailWord_2793072) baseStart_2793072 baseEnd_2793072 := by
    simpa [prefixWord, tailWord_2793072, baseEnd_2793072] using wordTrace_append hprefix tailTrace_2793072
  have hstable : (prefixWord ++ tailWord_2793072).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2793072).length < 2 ^ (prefixWord ++ tailWord_2793072).sum := by decide
  have hdescent : baseEnd_2793072 < baseStart_2793072 := by decide
  rcases family_descends (prefixWord ++ tailWord_2793072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2793074 : List Nat := [3, 2, 1, 2, 3, 1, 2, 1, 4, 3]
def baseStart_2793074 : Nat := 118140960795 + 2793074 * 2 ^ 59
def prefixEnd_2793074 : Nat := 4983230072969 + 3 ^ 40 * 2793074 * 2
def baseEnd_2793074 : Nat := 956126310384073545886595

theorem tailTrace_2793074 : CollatzResearch.WordTrace tailWord_2793074 prefixEnd_2793074 956126310384073545886595 := by
  unfold tailWord_2793074
  simp only [CollatzResearch.WordTrace]
  refine ⟨25467944470794347976720569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67914518588784927937921517 25467944470794347976720569)
  ·
    refine ⟨19100958353095760982540427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25467944470794347976720569 19100958353095760982540427)
    ·
      refine ⟨28651437529643641473810641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19100958353095760982540427 28651437529643641473810641)
      ·
        refine ⟨21488578147232731105357981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28651437529643641473810641 21488578147232731105357981)
        ·
          refine ⟨8058216805212274164509243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21488578147232731105357981 8058216805212274164509243)
          ·
            refine ⟨12087325207818411246763865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8058216805212274164509243 12087325207818411246763865)
            ·
              refine ⟨9065493905863808435072899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12087325207818411246763865 9065493905863808435072899)
              ·
                refine ⟨13598240858795712652609349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9065493905863808435072899 13598240858795712652609349)
                ·
                  refine ⟨2549670161024196122364253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13598240858795712652609349 2549670161024196122364253)
                  ·
                    refine ⟨956126310384073545886595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2549670161024196122364253 956126310384073545886595)
                    ·
                      rfl

theorem cell22_2793074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 1, 4, 3].length) (baseStart_2793074 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2793074 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2793074 prefixEnd_2793074 := by exact prefixLift 2793074
  have htrace : WordTrace (prefixWord ++ tailWord_2793074) baseStart_2793074 baseEnd_2793074 := by
    simpa [prefixWord, tailWord_2793074, baseEnd_2793074] using wordTrace_append hprefix tailTrace_2793074
  have hstable : (prefixWord ++ tailWord_2793074).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2793074).length < 2 ^ (prefixWord ++ tailWord_2793074).sum := by decide
  have hdescent : baseEnd_2793074 < baseStart_2793074 := by decide
  rcases family_descends (prefixWord ++ tailWord_2793074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2793106 : List Nat := [3, 2, 3, 1, 3, 1, 2, 1, 2, 4]
def baseStart_2793106 : Nat := 118140960795 + 2793106 * 2 ^ 59
def prefixEnd_2793106 : Nat := 4983230072969 + 3 ^ 40 * 2793106 * 2
def baseEnd_2793106 : Nat := 956137264638036129086497

theorem tailTrace_2793106 : CollatzResearch.WordTrace tailWord_2793106 prefixEnd_2793106 956137264638036129086497 := by
  unfold tailWord_2793106
  simp only [CollatzResearch.WordTrace]
  refine ⟨25468236254765365343011793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67915296679374307581364781 25468236254765365343011793)
  ·
    refine ⟨19101177191074024007258845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25468236254765365343011793 19101177191074024007258845)
    ·
      refine ⟨7162941446652759002722067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19101177191074024007258845 7162941446652759002722067)
      ·
        refine ⟨10744412169979138504083101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7162941446652759002722067 10744412169979138504083101)
        ·
          refine ⟨4029154563742176939031163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10744412169979138504083101 4029154563742176939031163)
          ·
            refine ⟨6043731845613265408546745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4029154563742176939031163 6043731845613265408546745)
            ·
              refine ⟨4532798884209949056410059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6043731845613265408546745 4532798884209949056410059)
              ·
                refine ⟨6799198326314923584615089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4532798884209949056410059 6799198326314923584615089)
                ·
                  refine ⟨5099398744736192688461317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6799198326314923584615089 5099398744736192688461317)
                  ·
                    refine ⟨956137264638036129086497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5099398744736192688461317 956137264638036129086497)
                    ·
                      rfl

theorem cell22_2793106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 2, 1, 2, 4].length) (baseStart_2793106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2793106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2793106 prefixEnd_2793106 := by exact prefixLift 2793106
  have htrace : WordTrace (prefixWord ++ tailWord_2793106) baseStart_2793106 baseEnd_2793106 := by
    simpa [prefixWord, tailWord_2793106, baseEnd_2793106] using wordTrace_append hprefix tailTrace_2793106
  have hstable : (prefixWord ++ tailWord_2793106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2793106).length < 2 ^ (prefixWord ++ tailWord_2793106).sum := by decide
  have hdescent : baseEnd_2793106 < baseStart_2793106 := by decide
  rcases family_descends (prefixWord ++ tailWord_2793106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2793207 : List Nat := [1, 1, 3, 1, 1, 1, 5, 2, 1, 6]
def baseStart_2793207 : Nat := 118140960795 + 2793207 * 2 ^ 59
def prefixEnd_2793207 : Nat := 4983230072969 + 3 ^ 40 * 2793207 * 2
def baseEnd_2793207 : Nat := 956171839002105532311187

theorem tailTrace_2793207 : CollatzResearch.WordTrace tailWord_2793207 prefixEnd_2793207 956171839002105532311187 := by
  unfold tailWord_2793207
  simp only [CollatzResearch.WordTrace]
  refine ⟨101876628791695555621473875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67917752527797037080982583 101876628791695555621473875)
  ·
    refine ⟨152814943187543333432210813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101876628791695555621473875 152814943187543333432210813)
    ·
      refine ⟨57305603695328750037079055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 152814943187543333432210813 57305603695328750037079055)
      ·
        refine ⟨85958405542993125055618583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57305603695328750037079055 85958405542993125055618583)
        ·
          refine ⟨128937608314489687583427875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85958405542993125055618583 128937608314489687583427875)
          ·
            refine ⟨193406412471734531375141813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128937608314489687583427875 193406412471734531375141813)
            ·
              refine ⟨18131851169225112316419545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 193406412471734531375141813 18131851169225112316419545)
              ·
                refine ⟨13598888376918834237314659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18131851169225112316419545 13598888376918834237314659)
                ·
                  refine ⟨20398332565378251355971989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13598888376918834237314659 20398332565378251355971989)
                  ·
                    refine ⟨956171839002105532311187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20398332565378251355971989 956171839002105532311187)
                    ·
                      rfl

theorem cell22_2793207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 2, 1, 6].length) (baseStart_2793207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2793207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2793207 prefixEnd_2793207 := by exact prefixLift 2793207
  have htrace : WordTrace (prefixWord ++ tailWord_2793207) baseStart_2793207 baseEnd_2793207 := by
    simpa [prefixWord, tailWord_2793207, baseEnd_2793207] using wordTrace_append hprefix tailTrace_2793207
  have hstable : (prefixWord ++ tailWord_2793207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2793207).length < 2 ^ (prefixWord ++ tailWord_2793207).sum := by decide
  have hdescent : baseEnd_2793207 < baseStart_2793207 := by decide
  rcases family_descends (prefixWord ++ tailWord_2793207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2793224 : List Nat := [2, 1, 3, 2, 2, 1, 2, 3, 2, 4]
def baseStart_2793224 : Nat := 118140960795 + 2793224 * 2 ^ 59
def prefixEnd_2793224 : Nat := 4983230072969 + 3 ^ 40 * 2793224 * 2
def baseEnd_2793224 : Nat := 956177658449523154636135

theorem tailTrace_2793224 : CollatzResearch.WordTrace tailWord_2793224 prefixEnd_2793224 956177658449523154636135 := by
  unfold tailWord_2793224
  simp only [CollatzResearch.WordTrace]
  refine ⟨50938624416316983762421363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67918165888422645016561817 50938624416316983762421363)
  ·
    refine ⟨76407936624475475643632045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50938624416316983762421363 76407936624475475643632045)
    ·
      refine ⟨28652976234178303366362017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76407936624475475643632045 28652976234178303366362017)
      ·
        refine ⟨21489732175633727524771513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28652976234178303366362017 21489732175633727524771513)
        ·
          refine ⟨16117299131725295643578635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21489732175633727524771513 16117299131725295643578635)
          ·
            refine ⟨24175948697587943465367953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16117299131725295643578635 24175948697587943465367953)
            ·
              refine ⟨18131961523190957599025965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24175948697587943465367953 18131961523190957599025965)
              ·
                refine ⟨6799485571196609099634737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18131961523190957599025965 6799485571196609099634737)
                ·
                  refine ⟨5099614178397456824726053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6799485571196609099634737 5099614178397456824726053)
                  ·
                    refine ⟨956177658449523154636135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5099614178397456824726053 956177658449523154636135)
                    ·
                      rfl

theorem cell22_2793224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 3, 2, 4].length) (baseStart_2793224 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2793224 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2793224 prefixEnd_2793224 := by exact prefixLift 2793224
  have htrace : WordTrace (prefixWord ++ tailWord_2793224) baseStart_2793224 baseEnd_2793224 := by
    simpa [prefixWord, tailWord_2793224, baseEnd_2793224] using wordTrace_append hprefix tailTrace_2793224
  have hstable : (prefixWord ++ tailWord_2793224).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2793224).length < 2 ^ (prefixWord ++ tailWord_2793224).sum := by decide
  have hdescent : baseEnd_2793224 < baseStart_2793224 := by decide
  rcases family_descends (prefixWord ++ tailWord_2793224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2793239 : List Nat := [1, 1, 3, 4, 2, 3, 8]
def baseStart_2793239 : Nat := 118140960795 + 2793239 * 2 ^ 59
def prefixEnd_2793239 : Nat := 4983230072969 + 3 ^ 40 * 2793239 * 2
def baseEnd_2793239 : Nat := 35414177528002522796707

theorem tailTrace_2793239 : CollatzResearch.WordTrace tailWord_2793239 prefixEnd_2793239 35414177528002522796707 := by
  unfold tailWord_2793239
  simp only [CollatzResearch.WordTrace]
  refine ⟨101877795927579625086638771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67918530618386416724425847 101877795927579625086638771)
  ·
    refine ⟨152816693891369437629958157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101877795927579625086638771 152816693891369437629958157)
    ·
      refine ⟨57306260209263539111234309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 152816693891369437629958157 57306260209263539111234309)
      ·
        refine ⟨10744923789236913583356433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57306260209263539111234309 10744923789236913583356433)
        ·
          refine ⟨8058692841927685187517325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10744923789236913583356433 8058692841927685187517325)
          ·
            refine ⟨3022009815722881945318997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8058692841927685187517325 3022009815722881945318997)
            ·
              refine ⟨35414177528002522796707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3022009815722881945318997 35414177528002522796707)
              ·
                rfl

theorem cell22_2793239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 8].length) (baseStart_2793239 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2793239 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2793239 prefixEnd_2793239 := by exact prefixLift 2793239
  have htrace : WordTrace (prefixWord ++ tailWord_2793239) baseStart_2793239 baseEnd_2793239 := by
    simpa [prefixWord, tailWord_2793239, baseEnd_2793239] using wordTrace_append hprefix tailTrace_2793239
  have hstable : (prefixWord ++ tailWord_2793239).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2793239).length < 2 ^ (prefixWord ++ tailWord_2793239).sum := by decide
  have hdescent : baseEnd_2793239 < baseStart_2793239 := by decide
  rcases family_descends (prefixWord ++ tailWord_2793239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2793301 : List Nat := [1, 3, 2, 2, 2, 3, 2, 2, 5]
def baseStart_2793301 : Nat := 118140960795 + 2793301 * 2 ^ 59
def prefixEnd_2793301 : Nat := 4983230072969 + 3 ^ 40 * 2793301 * 2
def baseEnd_2793301 : Nat := 318734672374373540153633

theorem tailTrace_2793301 : CollatzResearch.WordTrace tailWord_2793301 prefixEnd_2793301 318734672374373540153633 := by
  unfold tailWord_2793301
  simp only [CollatzResearch.WordTrace]
  refine ⟨101880057253355009675395757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67920038168903339783597171 101880057253355009675395757)
  ·
    refine ⟨38205021470008128628273409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101880057253355009675395757 38205021470008128628273409)
    ·
      refine ⟨28653766102506096471205057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38205021470008128628273409 28653766102506096471205057)
      ·
        refine ⟨21490324576879572353403793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28653766102506096471205057 21490324576879572353403793)
        ·
          refine ⟨16117743432659679265052845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21490324576879572353403793 16117743432659679265052845)
          ·
            refine ⟨6044153787247379724394817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16117743432659679265052845 6044153787247379724394817)
            ·
              refine ⟨4533115340435534793296113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6044153787247379724394817 4533115340435534793296113)
              ·
                refine ⟨3399836505326651094972085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4533115340435534793296113 3399836505326651094972085)
                ·
                  refine ⟨318734672374373540153633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3399836505326651094972085 318734672374373540153633)
                  ·
                    rfl

theorem cell22_2793301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 2, 2, 5].length) (baseStart_2793301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2793301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2793301 prefixEnd_2793301 := by exact prefixLift 2793301
  have htrace : WordTrace (prefixWord ++ tailWord_2793301) baseStart_2793301 baseEnd_2793301 := by
    simpa [prefixWord, tailWord_2793301, baseEnd_2793301] using wordTrace_append hprefix tailTrace_2793301
  have hstable : (prefixWord ++ tailWord_2793301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2793301).length < 2 ^ (prefixWord ++ tailWord_2793301).sum := by decide
  have hdescent : baseEnd_2793301 < baseStart_2793301 := by decide
  rcases family_descends (prefixWord ++ tailWord_2793301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2793316 : List Nat := [2, 3, 1, 1, 5, 1, 1, 1, 2, 5]
def baseStart_2793316 : Nat := 118140960795 + 2793316 * 2 ^ 59
def prefixEnd_2793316 : Nat := 4983230072969 + 3 ^ 40 * 2793316 * 2
def baseEnd_2793316 : Nat := 956209151929665581335853

theorem tailTrace_2793316 : CollatzResearch.WordTrace tailWord_2793316 prefixEnd_2793316 956209151929665581335853 := by
  unfold tailWord_2793316
  simp only [CollatzResearch.WordTrace]
  refine ⟨50940302174150333618595901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67920402898867111491461201 50940302174150333618595901)
  ·
    refine ⟨19102613315306375106973463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50940302174150333618595901 19102613315306375106973463)
    ·
      refine ⟨28653919972959562660460195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19102613315306375106973463 28653919972959562660460195)
      ·
        refine ⟨42980879959439343990690293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28653919972959562660460195 42980879959439343990690293)
        ·
          refine ⟨4029457496197438499127215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 42980879959439343990690293 4029457496197438499127215)
          ·
            refine ⟨6044186244296157748690823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4029457496197438499127215 6044186244296157748690823)
            ·
              refine ⟨9066279366444236623036235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6044186244296157748690823 9066279366444236623036235)
              ·
                refine ⟨13599419049666354934554353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9066279366444236623036235 13599419049666354934554353)
                ·
                  refine ⟨10199564287249766200915765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13599419049666354934554353 10199564287249766200915765)
                  ·
                    refine ⟨956209151929665581335853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10199564287249766200915765 956209151929665581335853)
                    ·
                      rfl

theorem cell22_2793316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 1, 2, 5].length) (baseStart_2793316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2793316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2793316 prefixEnd_2793316 := by exact prefixLift 2793316
  have htrace : WordTrace (prefixWord ++ tailWord_2793316) baseStart_2793316 baseEnd_2793316 := by
    simpa [prefixWord, tailWord_2793316, baseEnd_2793316] using wordTrace_append hprefix tailTrace_2793316
  have hstable : (prefixWord ++ tailWord_2793316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2793316).length < 2 ^ (prefixWord ++ tailWord_2793316).sum := by decide
  have hdescent : baseEnd_2793316 < baseStart_2793316 := by decide
  rcases family_descends (prefixWord ++ tailWord_2793316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2793329 : List Nat := [1, 2, 2, 2, 1, 3, 3, 2, 6]
def baseStart_2793329 : Nat := 118140960795 + 2793329 * 2 ^ 59
def prefixEnd_2793329 : Nat := 4983230072969 + 3 ^ 40 * 2793329 * 2
def baseEnd_2793329 : Nat := 318737867365112626920271

theorem tailTrace_2793329 : CollatzResearch.WordTrace tailWord_2793329 prefixEnd_2793329 318737867365112626920271 := by
  unfold tailWord_2793329
  simp only [CollatzResearch.WordTrace]
  refine ⟨101881078497253570457415041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67920718998169046971610027 101881078497253570457415041)
  ·
    refine ⟨76410808872940177843061281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101881078497253570457415041 76410808872940177843061281)
    ·
      refine ⟨57308106654705133382295961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76410808872940177843061281 57308106654705133382295961)
      ·
        refine ⟨42981079991028850036721971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57308106654705133382295961 42981079991028850036721971)
        ·
          refine ⟨64471619986543275055082957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42981079991028850036721971 64471619986543275055082957)
          ·
            refine ⟨24176857494953728145656109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64471619986543275055082957 24176857494953728145656109)
            ·
              refine ⟨9066321560607648054621041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24176857494953728145656109 9066321560607648054621041)
              ·
                refine ⟨6799741170455736040965781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9066321560607648054621041 6799741170455736040965781)
                ·
                  refine ⟨318737867365112626920271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6799741170455736040965781 318737867365112626920271)
                  ·
                    rfl

theorem cell22_2793329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 2, 6].length) (baseStart_2793329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2793329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2793329 prefixEnd_2793329 := by exact prefixLift 2793329
  have htrace : WordTrace (prefixWord ++ tailWord_2793329) baseStart_2793329 baseEnd_2793329 := by
    simpa [prefixWord, tailWord_2793329, baseEnd_2793329] using wordTrace_append hprefix tailTrace_2793329
  have hstable : (prefixWord ++ tailWord_2793329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2793329).length < 2 ^ (prefixWord ++ tailWord_2793329).sum := by decide
  have hdescent : baseEnd_2793329 < baseStart_2793329 := by decide
  rcases family_descends (prefixWord ++ tailWord_2793329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2793344 : List Nat := [2, 1, 1, 2, 1, 2, 3, 4, 1, 5]
def baseStart_2793344 : Nat := 118140960795 + 2793344 * 2 ^ 59
def prefixEnd_2793344 : Nat := 4983230072969 + 3 ^ 40 * 2793344 * 2
def baseEnd_2793344 : Nat := 956218736901882841635767

theorem tailTrace_2793344 : CollatzResearch.WordTrace tailWord_2793344 prefixEnd_2793344 956218736901882841635767 := by
  unfold tailWord_2793344
  simp only [CollatzResearch.WordTrace]
  refine ⟨50940812796099614009605543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67921083728132818679474057 50940812796099614009605543)
  ·
    refine ⟨76411219194149421014408315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50940812796099614009605543 76411219194149421014408315)
    ·
      refine ⟨114616828791224131521612473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76411219194149421014408315 114616828791224131521612473)
      ·
        refine ⟨85962621593418098641209355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114616828791224131521612473 85962621593418098641209355)
        ·
          refine ⟨128943932390127147961814033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85962621593418098641209355 128943932390127147961814033)
          ·
            refine ⟨96707949292595360971360525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 128943932390127147961814033 96707949292595360971360525)
            ·
              refine ⟨36265480984723260364260197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 96707949292595360971360525 36265480984723260364260197)
              ·
                refine ⟨6799777684635611318298787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36265480984723260364260197 6799777684635611318298787)
                ·
                  refine ⟨10199666526953416977448181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6799777684635611318298787 10199666526953416977448181)
                  ·
                    refine ⟨956218736901882841635767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10199666526953416977448181 956218736901882841635767)
                    ·
                      rfl

theorem cell22_2793344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 4, 1, 5].length) (baseStart_2793344 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2793344 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2793344 prefixEnd_2793344 := by exact prefixLift 2793344
  have htrace : WordTrace (prefixWord ++ tailWord_2793344) baseStart_2793344 baseEnd_2793344 := by
    simpa [prefixWord, tailWord_2793344, baseEnd_2793344] using wordTrace_append hprefix tailTrace_2793344
  have hstable : (prefixWord ++ tailWord_2793344).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2793344).length < 2 ^ (prefixWord ++ tailWord_2793344).sum := by decide
  have hdescent : baseEnd_2793344 < baseStart_2793344 := by decide
  rcases family_descends (prefixWord ++ tailWord_2793344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2793348 : List Nat := [2, 3, 2, 1, 1, 1, 6, 1, 1, 4]
def baseStart_2793348 : Nat := 118140960795 + 2793348 * 2 ^ 59
def prefixEnd_2793348 : Nat := 4983230072969 + 3 ^ 40 * 2793348 * 2
def baseEnd_2793348 : Nat := 956220106183628164535755

theorem tailTrace_2793348 : CollatzResearch.WordTrace tailWord_2793348 prefixEnd_2793348 956220106183628164535755 := by
  unfold tailWord_2793348
  simp only [CollatzResearch.WordTrace]
  refine ⟨50940885742092368351178349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67921180989456491134904465 50940885742092368351178349)
  ·
    refine ⟨19102832153284638131691881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50940885742092368351178349 19102832153284638131691881)
    ·
      refine ⟨14327124114963478598768911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19102832153284638131691881 14327124114963478598768911)
      ·
        refine ⟨21490686172445217898153367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14327124114963478598768911 21490686172445217898153367)
        ·
          refine ⟨32236029258667826847230051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21490686172445217898153367 32236029258667826847230051)
          ·
            refine ⟨48354043888001740270845077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32236029258667826847230051 48354043888001740270845077)
            ·
              refine ⟨2266595807250081575195863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 48354043888001740270845077 2266595807250081575195863)
              ·
                refine ⟨3399893710875122362793795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2266595807250081575195863 3399893710875122362793795)
                ·
                  refine ⟨5099840566312683544190693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3399893710875122362793795 5099840566312683544190693)
                  ·
                    refine ⟨956220106183628164535755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5099840566312683544190693 956220106183628164535755)
                    ·
                      rfl

theorem cell22_2793348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 6, 1, 1, 4].length) (baseStart_2793348 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2793348 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2793348 prefixEnd_2793348 := by exact prefixLift 2793348
  have htrace : WordTrace (prefixWord ++ tailWord_2793348) baseStart_2793348 baseEnd_2793348 := by
    simpa [prefixWord, tailWord_2793348, baseEnd_2793348] using wordTrace_append hprefix tailTrace_2793348
  have hstable : (prefixWord ++ tailWord_2793348).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2793348).length < 2 ^ (prefixWord ++ tailWord_2793348).sum := by decide
  have hdescent : baseEnd_2793348 < baseStart_2793348 := by decide
  rcases family_descends (prefixWord ++ tailWord_2793348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2793419 : List Nat := [1, 1, 1, 1, 3, 4, 1, 3, 7]
def baseStart_2793419 : Nat := 118140960795 + 2793419 * 2 ^ 59
def prefixEnd_2793419 : Nat := 4983230072969 + 3 ^ 40 * 2793419 * 2
def baseEnd_2793419 : Nat := 318748136978202548670179

theorem tailTrace_2793419 : CollatzResearch.WordTrace tailWord_2793419 prefixEnd_2793419 318748136978202548670179 := by
  unfold tailWord_2793419
  simp only [CollatzResearch.WordTrace]
  refine ⟨101884361066927515828191311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67922907377951677218794207 101884361066927515828191311)
  ·
    refine ⟨152826541600391273742286967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101884361066927515828191311 152826541600391273742286967)
    ·
      refine ⟨229239812400586910613430451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152826541600391273742286967 229239812400586910613430451)
      ·
        refine ⟨343859718600880365920145677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 229239812400586910613430451 343859718600880365920145677)
        ·
          refine ⟨128947394475330137220054629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 343859718600880365920145677 128947394475330137220054629)
          ·
            refine ⟨24177636464124400728760243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 128947394475330137220054629 24177636464124400728760243)
            ·
              refine ⟨36266454696186601093140365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24177636464124400728760243 36266454696186601093140365)
              ·
                refine ⟨13599920511069975409927637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36266454696186601093140365 13599920511069975409927637)
                ·
                  refine ⟨318748136978202548670179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13599920511069975409927637 318748136978202548670179)
                  ·
                    rfl

theorem cell22_2793419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 3, 7].length) (baseStart_2793419 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2793419 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2793419 prefixEnd_2793419 := by exact prefixLift 2793419
  have htrace : WordTrace (prefixWord ++ tailWord_2793419) baseStart_2793419 baseEnd_2793419 := by
    simpa [prefixWord, tailWord_2793419, baseEnd_2793419] using wordTrace_append hprefix tailTrace_2793419
  have hstable : (prefixWord ++ tailWord_2793419).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2793419).length < 2 ^ (prefixWord ++ tailWord_2793419).sum := by decide
  have hdescent : baseEnd_2793419 < baseStart_2793419 := by decide
  rcases family_descends (prefixWord ++ tailWord_2793419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2793470 : List Nat := [4, 2, 2, 2, 1, 2, 2, 2, 5]
def baseStart_2793470 : Nat := 118140960795 + 2793470 * 2 ^ 59
def prefixEnd_2793470 : Nat := 4983230072969 + 3 ^ 40 * 2793470 * 2
def baseEnd_2793470 : Nat := 318753956425620170995127

theorem tailTrace_2793470 : CollatzResearch.WordTrace tailWord_2793470 prefixEnd_2793470 318753956425620170995127 := by
  unfold tailWord_2793470
  simp only [CollatzResearch.WordTrace]
  refine ⟨12735777648717843942287233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67924147459828501025531909 12735777648717843942287233)
  ·
    refine ⟨9551833236538382956715425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12735777648717843942287233 9551833236538382956715425)
    ·
      refine ⟨7163874927403787217536569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9551833236538382956715425 7163874927403787217536569)
      ·
        refine ⟨5372906195552840413152427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7163874927403787217536569 5372906195552840413152427)
        ·
          refine ⟨8059359293329260619728641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5372906195552840413152427 8059359293329260619728641)
          ·
            refine ⟨6044519469996945464796481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8059359293329260619728641 6044519469996945464796481)
            ·
              refine ⟨4533389602497709098597361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6044519469996945464796481 4533389602497709098597361)
              ·
                refine ⟨3400042201873281823948021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4533389602497709098597361 3400042201873281823948021)
                ·
                  refine ⟨318753956425620170995127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3400042201873281823948021 318753956425620170995127)
                  ·
                    rfl

theorem cell22_2793470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 2, 2, 5].length) (baseStart_2793470 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2793470 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2793470 prefixEnd_2793470 := by exact prefixLift 2793470
  have htrace : WordTrace (prefixWord ++ tailWord_2793470) baseStart_2793470 baseEnd_2793470 := by
    simpa [prefixWord, tailWord_2793470, baseEnd_2793470] using wordTrace_append hprefix tailTrace_2793470
  have hstable : (prefixWord ++ tailWord_2793470).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2793470).length < 2 ^ (prefixWord ++ tailWord_2793470).sum := by decide
  have hdescent : baseEnd_2793470 < baseStart_2793470 := by decide
  rcases family_descends (prefixWord ++ tailWord_2793470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2793566 : List Nat := [4, 4, 1, 1, 2, 2, 1, 3, 4]
def baseStart_2793566 : Nat := 118140960795 + 2793566 * 2 ^ 59
def prefixEnd_2793566 : Nat := 4983230072969 + 3 ^ 40 * 2793566 * 2
def baseEnd_2793566 : Nat := 318764910679582754195029

theorem tailTrace_2793566 : CollatzResearch.WordTrace tailWord_2793566 prefixEnd_2793566 318764910679582754195029 := by
  unfold tailWord_2793566
  simp only [CollatzResearch.WordTrace]
  refine ⟨12736215324674369991724069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67926481731596639955861701 12736215324674369991724069)
  ·
    refine ⟨2388040373376444373448263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12736215324674369991724069 2388040373376444373448263)
    ·
      refine ⟨3582060560064666560172395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2388040373376444373448263 3582060560064666560172395)
      ·
        refine ⟨5373090840096999840258593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3582060560064666560172395 5373090840096999840258593)
        ·
          refine ⟨4029818130072749880193945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5373090840096999840258593 4029818130072749880193945)
          ·
            refine ⟨3022363597554562410145459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4029818130072749880193945 3022363597554562410145459)
            ·
              refine ⟨4533545396331843615218189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3022363597554562410145459 4533545396331843615218189)
              ·
                refine ⟨1700079523624441355706821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4533545396331843615218189 1700079523624441355706821)
                ·
                  refine ⟨318764910679582754195029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1700079523624441355706821 318764910679582754195029)
                  ·
                    rfl

theorem cell22_2793566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 1, 3, 4].length) (baseStart_2793566 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2793566 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2793566 prefixEnd_2793566 := by exact prefixLift 2793566
  have htrace : WordTrace (prefixWord ++ tailWord_2793566) baseStart_2793566 baseEnd_2793566 := by
    simpa [prefixWord, tailWord_2793566, baseEnd_2793566] using wordTrace_append hprefix tailTrace_2793566
  have hstable : (prefixWord ++ tailWord_2793566).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2793566).length < 2 ^ (prefixWord ++ tailWord_2793566).sum := by decide
  have hdescent : baseEnd_2793566 < baseStart_2793566 := by decide
  rcases family_descends (prefixWord ++ tailWord_2793566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2793571 : List Nat := [1, 1, 1, 5, 1, 1, 3, 2, 7]
def baseStart_2793571 : Nat := 118140960795 + 2793571 * 2 ^ 59
def prefixEnd_2793571 : Nat := 4983230072969 + 3 ^ 40 * 2793571 * 2
def baseEnd_2793571 : Nat := 318765481213643305403357

theorem tailTrace_2793571 : CollatzResearch.WordTrace tailWord_2793571 prefixEnd_2793571 318765481213643305403357 := by
  unfold tailWord_2793571
  simp only [CollatzResearch.WordTrace]
  refine ⟨101889904962376845787724567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67926603308251230525149711 101889904962376845787724567)
  ·
    refine ⟨152834857443565268681586851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101889904962376845787724567 152834857443565268681586851)
    ·
      refine ⟨229252286165347903022380277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152834857443565268681586851 229252286165347903022380277)
      ·
        refine ⟨21492401828001365908348151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 229252286165347903022380277 21492401828001365908348151)
        ·
          refine ⟨32238602742002048862522227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21492401828001365908348151 32238602742002048862522227)
          ·
            refine ⟨48357904113003073293783341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32238602742002048862522227 48357904113003073293783341)
            ·
              refine ⟨18134214042376152485168753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48357904113003073293783341 18134214042376152485168753)
              ·
                refine ⟨13600660531782114363876565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18134214042376152485168753 13600660531782114363876565)
                ·
                  refine ⟨318765481213643305403357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13600660531782114363876565 318765481213643305403357)
                  ·
                    rfl

theorem cell22_2793571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 2, 7].length) (baseStart_2793571 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2793571 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2793571 prefixEnd_2793571 := by exact prefixLift 2793571
  have htrace : WordTrace (prefixWord ++ tailWord_2793571) baseStart_2793571 baseEnd_2793571 := by
    simpa [prefixWord, tailWord_2793571, baseEnd_2793571] using wordTrace_append hprefix tailTrace_2793571
  have hstable : (prefixWord ++ tailWord_2793571).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2793571).length < 2 ^ (prefixWord ++ tailWord_2793571).sum := by decide
  have hdescent : baseEnd_2793571 < baseStart_2793571 := by decide
  rcases family_descends (prefixWord ++ tailWord_2793571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2793605 : List Nat := [1, 3, 1, 1, 5, 1, 4, 1, 5]
def baseStart_2793605 : Nat := 118140960795 + 2793605 * 2 ^ 59
def prefixEnd_2793605 : Nat := 4983230072969 + 3 ^ 40 * 2793605 * 2
def baseEnd_2793605 : Nat := 318769360845255053619989

theorem tailTrace_2793605 : CollatzResearch.WordTrace tailWord_2793605 prefixEnd_2793605 318769360845255053619989 := by
  unfold tailWord_2793605
  simp only [CollatzResearch.WordTrace]
  refine ⟨101891145044253669594462269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67927430029502446396308179 101891145044253669594462269)
  ·
    refine ⟨38209179391595126097923351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101891145044253669594462269 38209179391595126097923351)
    ·
      refine ⟨57313769087392689146885027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38209179391595126097923351 57313769087392689146885027)
      ·
        refine ⟨85970653631089033720327541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57313769087392689146885027 85970653631089033720327541)
        ·
          refine ⟨8059748777914596911280707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 85970653631089033720327541 8059748777914596911280707)
          ·
            refine ⟨12089623166871895366921061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8059748777914596911280707 12089623166871895366921061)
            ·
              refine ⟨2266804343788480381297699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12089623166871895366921061 2266804343788480381297699)
              ·
                refine ⟨3400206515682720571946549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2266804343788480381297699 3400206515682720571946549)
                ·
                  refine ⟨318769360845255053619989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3400206515682720571946549 318769360845255053619989)
                  ·
                    rfl

theorem cell22_2793605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 4, 1, 5].length) (baseStart_2793605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2793605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2793605 prefixEnd_2793605 := by exact prefixLift 2793605
  have htrace : WordTrace (prefixWord ++ tailWord_2793605) baseStart_2793605 baseEnd_2793605 := by
    simpa [prefixWord, tailWord_2793605, baseEnd_2793605] using wordTrace_append hprefix tailTrace_2793605
  have hstable : (prefixWord ++ tailWord_2793605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2793605).length < 2 ^ (prefixWord ++ tailWord_2793605).sum := by decide
  have hdescent : baseEnd_2793605 < baseStart_2793605 := by decide
  rcases family_descends (prefixWord ++ tailWord_2793605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2793616 : List Nat := [2, 1, 1, 1, 1, 1, 6, 1, 8]
def baseStart_2793616 : Nat := 118140960795 + 2793616 * 2 ^ 59
def prefixEnd_2793616 : Nat := 4983230072969 + 3 ^ 40 * 2793616 * 2
def baseEnd_2793616 : Nat := 318770616020188266278311

theorem tailTrace_2793616 : CollatzResearch.WordTrace tailWord_2793616 prefixEnd_2793616 318770616020188266278311 := by
  unfold tailWord_2793616
  simp only [CollatzResearch.WordTrace]
  refine ⟨50945773123606909236556351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67927697498142545648741801 50945773123606909236556351)
  ·
    refine ⟨76418659685410363854834527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50945773123606909236556351 76418659685410363854834527)
    ·
      refine ⟨114627989528115545782251791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76418659685410363854834527 114627989528115545782251791)
      ·
        refine ⟨171941984292173318673377687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114627989528115545782251791 171941984292173318673377687)
        ·
          refine ⟨257912976438259978010066531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171941984292173318673377687 257912976438259978010066531)
          ·
            refine ⟨386869464657389967015099797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 257912976438259978010066531 386869464657389967015099797)
            ·
              refine ⟨18134506155815154703832803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 386869464657389967015099797 18134506155815154703832803)
              ·
                refine ⟨27201759233722732055749205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18134506155815154703832803 27201759233722732055749205)
                ·
                  refine ⟨318770616020188266278311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27201759233722732055749205 318770616020188266278311)
                  ·
                    rfl

theorem cell22_2793616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 1, 8].length) (baseStart_2793616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2793616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2793616 prefixEnd_2793616 := by exact prefixLift 2793616
  have htrace : WordTrace (prefixWord ++ tailWord_2793616) baseStart_2793616 baseEnd_2793616 := by
    simpa [prefixWord, tailWord_2793616, baseEnd_2793616] using wordTrace_append hprefix tailTrace_2793616
  have hstable : (prefixWord ++ tailWord_2793616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2793616).length < 2 ^ (prefixWord ++ tailWord_2793616).sum := by decide
  have hdescent : baseEnd_2793616 < baseStart_2793616 := by decide
  rcases family_descends (prefixWord ++ tailWord_2793616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2793650 : List Nat := [3, 2, 1, 1, 1, 3, 3, 4, 4]
def baseStart_2793650 : Nat := 118140960795 + 2793650 * 2 ^ 59
def prefixEnd_2793650 : Nat := 4983230072969 + 3 ^ 40 * 2793650 * 2
def baseEnd_2793650 : Nat := 318774495651800014494943

theorem tailTrace_2793650 : CollatzResearch.WordTrace tailWord_2793650 prefixEnd_2793650 318774495651800014494943 := by
  unfold tailWord_2793650
  simp only [CollatzResearch.WordTrace]
  refine ⟨25473196582272660569962601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67928524219393761519900269 25473196582272660569962601)
  ·
    refine ⟨19104897436704495427471951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25473196582272660569962601 19104897436704495427471951)
    ·
      refine ⟨28657346155056743141207927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19104897436704495427471951 28657346155056743141207927)
      ·
        refine ⟨42986019232585114711811891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28657346155056743141207927 42986019232585114711811891)
        ·
          refine ⟨64479028848877672067717837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42986019232585114711811891 64479028848877672067717837)
          ·
            refine ⟨24179635818329127025394189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64479028848877672067717837 24179635818329127025394189)
            ·
              refine ⟨9067363431873422634522821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24179635818329127025394189 9067363431873422634522821)
              ·
                refine ⟨1700130643476266743973029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9067363431873422634522821 1700130643476266743973029)
                ·
                  refine ⟨318774495651800014494943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1700130643476266743973029 318774495651800014494943)
                  ·
                    rfl

theorem cell22_2793650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 4, 4].length) (baseStart_2793650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2793650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2793650 prefixEnd_2793650 := by exact prefixLift 2793650
  have htrace : WordTrace (prefixWord ++ tailWord_2793650) baseStart_2793650 baseEnd_2793650 := by
    simpa [prefixWord, tailWord_2793650, baseEnd_2793650] using wordTrace_append hprefix tailTrace_2793650
  have hstable : (prefixWord ++ tailWord_2793650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2793650).length < 2 ^ (prefixWord ++ tailWord_2793650).sum := by decide
  have hdescent : baseEnd_2793650 < baseStart_2793650 := by decide
  rcases family_descends (prefixWord ++ tailWord_2793650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2793686 : List Nat := [5, 2, 1, 2, 1, 3, 2, 1, 1, 4]
def baseStart_2793686 : Nat := 118140960795 + 2793686 * 2 ^ 59
def prefixEnd_2793686 : Nat := 4983230072969 + 3 ^ 40 * 2793686 * 2
def baseEnd_2793686 : Nat := 956335810491107949584719

theorem tailTrace_2793686 : CollatzResearch.WordTrace tailWord_2793686 prefixEnd_2793686 956335810491107949584719 := by
  unfold tailWord_2793686
  simp only [CollatzResearch.WordTrace]
  refine ⟨6368381209810013776760057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 67929399571306813618773941 6368381209810013776760057)
  ·
    refine ⟨4776285907357510332570043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6368381209810013776760057 4776285907357510332570043)
    ·
      refine ⟨7164428861036265498855065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4776285907357510332570043 7164428861036265498855065)
      ·
        refine ⟨5373321645777199124141299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7164428861036265498855065 5373321645777199124141299)
        ·
          refine ⟨8059982468665798686211949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5373321645777199124141299 8059982468665798686211949)
          ·
            refine ⟨3022493425749674507329481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8059982468665798686211949 3022493425749674507329481)
            ·
              refine ⟨2266870069312255880497111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3022493425749674507329481 2266870069312255880497111)
              ·
                refine ⟨3400305103968383820745667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2266870069312255880497111 3400305103968383820745667)
                ·
                  refine ⟨5100457655952575731118501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3400305103968383820745667 5100457655952575731118501)
                  ·
                    refine ⟨956335810491107949584719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5100457655952575731118501 956335810491107949584719)
                    ·
                      rfl

theorem cell22_2793686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 2, 1, 1, 4].length) (baseStart_2793686 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2793686 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2793686 prefixEnd_2793686 := by exact prefixLift 2793686
  have htrace : WordTrace (prefixWord ++ tailWord_2793686) baseStart_2793686 baseEnd_2793686 := by
    simpa [prefixWord, tailWord_2793686, baseEnd_2793686] using wordTrace_append hprefix tailTrace_2793686
  have hstable : (prefixWord ++ tailWord_2793686).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2793686).length < 2 ^ (prefixWord ++ tailWord_2793686).sum := by decide
  have hdescent : baseEnd_2793686 < baseStart_2793686 := by decide
  rcases family_descends (prefixWord ++ tailWord_2793686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2793738 : List Nat := [3, 1, 2, 2, 1, 1, 2, 2, 1, 7]
def baseStart_2793738 : Nat := 118140960795 + 2793738 * 2 ^ 59
def prefixEnd_2793738 : Nat := 4983230072969 + 3 ^ 40 * 2793738 * 2
def baseEnd_2793738 : Nat := 956353611153797147284559

theorem tailTrace_2793738 : CollatzResearch.WordTrace tailWord_2793738 prefixEnd_2793738 956353611153797147284559 := by
  unfold tailWord_2793738
  simp only [CollatzResearch.WordTrace]
  refine ⟨25473998988192958327263467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67930663968514555539369245 25473998988192958327263467)
  ·
    refine ⟨38210998482289437490895201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25473998988192958327263467 38210998482289437490895201)
    ·
      refine ⟨28658248861717078118171401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38210998482289437490895201 28658248861717078118171401)
      ·
        refine ⟨21493686646287808588628551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28658248861717078118171401 21493686646287808588628551)
        ·
          refine ⟨32240529969431712882942827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21493686646287808588628551 32240529969431712882942827)
          ·
            refine ⟨48360794954147569324414241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32240529969431712882942827 48360794954147569324414241)
            ·
              refine ⟨36270596215610676993310681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48360794954147569324414241 36270596215610676993310681)
              ·
                refine ⟨27202947161708007744983011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36270596215610676993310681 27202947161708007744983011)
                ·
                  refine ⟨40804420742562011617474517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27202947161708007744983011 40804420742562011617474517)
                  ·
                    refine ⟨956353611153797147284559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40804420742562011617474517 956353611153797147284559)
                    ·
                      rfl

theorem cell22_2793738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 2, 1, 7].length) (baseStart_2793738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2793738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2793738 prefixEnd_2793738 := by exact prefixLift 2793738
  have htrace : WordTrace (prefixWord ++ tailWord_2793738) baseStart_2793738 baseEnd_2793738 := by
    simpa [prefixWord, tailWord_2793738, baseEnd_2793738] using wordTrace_append hprefix tailTrace_2793738
  have hstable : (prefixWord ++ tailWord_2793738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2793738).length < 2 ^ (prefixWord ++ tailWord_2793738).sum := by decide
  have hdescent : baseEnd_2793738 < baseStart_2793738 := by decide
  rcases family_descends (prefixWord ++ tailWord_2793738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2793774 : List Nat := [4, 1, 3, 3, 1, 1, 1, 3, 5]
def baseStart_2793774 : Nat := 118140960795 + 2793774 * 2 ^ 59
def prefixEnd_2793774 : Nat := 4983230072969 + 3 ^ 40 * 2793774 * 2
def baseEnd_2793774 : Nat := 318788644896501684461483

theorem tailTrace_2793774 : CollatzResearch.WordTrace tailWord_2793774 prefixEnd_2793774 318788644896501684461483 := by
  unfold tailWord_2793774
  simp only [CollatzResearch.WordTrace]
  refine ⟨12737163622580176432170547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67931539320427607638242917 12737163622580176432170547)
  ·
    refine ⟨19105745433870264648255821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12737163622580176432170547 19105745433870264648255821)
    ·
      refine ⟨7164654537701349243095933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19105745433870264648255821 7164654537701349243095933)
      ·
        refine ⟨2686745451638005966160975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7164654537701349243095933 2686745451638005966160975)
        ·
          refine ⟨4030118177457008949241463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2686745451638005966160975 4030118177457008949241463)
          ·
            refine ⟨6045177266185513423862195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4030118177457008949241463 6045177266185513423862195)
            ·
              refine ⟨9067765899278270135793293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6045177266185513423862195 9067765899278270135793293)
              ·
                refine ⟨3400412212229351300922485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9067765899278270135793293 3400412212229351300922485)
                ·
                  refine ⟨318788644896501684461483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3400412212229351300922485 318788644896501684461483)
                  ·
                    rfl

theorem cell22_2793774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 3, 5].length) (baseStart_2793774 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2793774 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2793774 prefixEnd_2793774 := by exact prefixLift 2793774
  have htrace : WordTrace (prefixWord ++ tailWord_2793774) baseStart_2793774 baseEnd_2793774 := by
    simpa [prefixWord, tailWord_2793774, baseEnd_2793774] using wordTrace_append hprefix tailTrace_2793774
  have hstable : (prefixWord ++ tailWord_2793774).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2793774).length < 2 ^ (prefixWord ++ tailWord_2793774).sum := by decide
  have hdescent : baseEnd_2793774 < baseStart_2793774 := by decide
  rcases family_descends (prefixWord ++ tailWord_2793774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2793783 : List Nat := [1, 1, 3, 1, 2, 1, 1, 2, 5, 5]
def baseStart_2793783 : Nat := 118140960795 + 2793783 * 2 ^ 59
def prefixEnd_2793783 : Nat := 4983230072969 + 3 ^ 40 * 2793783 * 2
def baseEnd_2793783 : Nat := 956369015573432029909421

theorem tailTrace_2793783 : CollatzResearch.WordTrace tailWord_2793783 prefixEnd_2793783 956369015573432029909421 := by
  unfold tailWord_2793783
  simp only [CollatzResearch.WordTrace]
  refine ⟨101897637237608805994442003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67931758158405870662961335 101897637237608805994442003)
  ·
    refine ⟨152846455856413208991663005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101897637237608805994442003 152846455856413208991663005)
    ·
      refine ⟨57317420946154953371873627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 152846455856413208991663005 57317420946154953371873627)
      ·
        refine ⟨85976131419232430057810441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57317420946154953371873627 85976131419232430057810441)
        ·
          refine ⟨64482098564424322543357831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85976131419232430057810441 64482098564424322543357831)
          ·
            refine ⟨96723147846636483815036747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64482098564424322543357831 96723147846636483815036747)
            ·
              refine ⟨145084721769954725722555121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96723147846636483815036747 145084721769954725722555121)
              ·
                refine ⟨108813541327466044291916341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 145084721769954725722555121 108813541327466044291916341)
                ·
                  refine ⟨10201269499449941652367157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 108813541327466044291916341 10201269499449941652367157)
                  ·
                    refine ⟨956369015573432029909421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10201269499449941652367157 956369015573432029909421)
                    ·
                      rfl

theorem cell22_2793783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 2, 5, 5].length) (baseStart_2793783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2793783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2793783 prefixEnd_2793783 := by exact prefixLift 2793783
  have htrace : WordTrace (prefixWord ++ tailWord_2793783) baseStart_2793783 baseEnd_2793783 := by
    simpa [prefixWord, tailWord_2793783, baseEnd_2793783] using wordTrace_append hprefix tailTrace_2793783
  have hstable : (prefixWord ++ tailWord_2793783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2793783).length < 2 ^ (prefixWord ++ tailWord_2793783).sum := by decide
  have hdescent : baseEnd_2793783 < baseStart_2793783 := by decide
  rcases family_descends (prefixWord ++ tailWord_2793783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2793800 : List Nat := [2, 1, 3, 1, 1, 2, 2, 1, 6, 3]
def baseStart_2793800 : Nat := 118140960795 + 2793800 * 2 ^ 59
def prefixEnd_2793800 : Nat := 4983230072969 + 3 ^ 40 * 2793800 * 2
def baseEnd_2793800 : Nat := 956374835020849652234369

theorem tailTrace_2793800 : CollatzResearch.WordTrace tailWord_2793800 prefixEnd_2793800 956374835020849652234369 := by
  unfold tailWord_2793800
  simp only [CollatzResearch.WordTrace]
  refine ⟨50949128639273608948905427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67932171519031478598540569 50949128639273608948905427)
  ·
    refine ⟨76423692958910413423358141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50949128639273608948905427 76423692958910413423358141)
    ·
      refine ⟨28658884859591405033759303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76423692958910413423358141 28658884859591405033759303)
      ·
        refine ⟨42988327289387107550638955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28658884859591405033759303 42988327289387107550638955)
        ·
          refine ⟨64482490934080661325958433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42988327289387107550638955 64482490934080661325958433)
          ·
            refine ⟨48361868200560495994468825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64482490934080661325958433 48361868200560495994468825)
            ·
              refine ⟨36271401150420371995851619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48361868200560495994468825 36271401150420371995851619)
              ·
                refine ⟨54407101725630557993777429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36271401150420371995851619 54407101725630557993777429)
                ·
                  refine ⟨2550332893388932405958317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 54407101725630557993777429 2550332893388932405958317)
                  ·
                    refine ⟨956374835020849652234369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2550332893388932405958317 956374835020849652234369)
                    ·
                      rfl

theorem cell22_2793800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 1, 6, 3].length) (baseStart_2793800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2793800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2793800 prefixEnd_2793800 := by exact prefixLift 2793800
  have htrace : WordTrace (prefixWord ++ tailWord_2793800) baseStart_2793800 baseEnd_2793800 := by
    simpa [prefixWord, tailWord_2793800, baseEnd_2793800] using wordTrace_append hprefix tailTrace_2793800
  have hstable : (prefixWord ++ tailWord_2793800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2793800).length < 2 ^ (prefixWord ++ tailWord_2793800).sum := by decide
  have hdescent : baseEnd_2793800 < baseStart_2793800 := by decide
  rcases family_descends (prefixWord ++ tailWord_2793800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2793813 : List Nat := [1, 3, 2, 2, 14]
def baseStart_2793813 : Nat := 118140960795 + 2793813 * 2 ^ 59
def prefixEnd_2793813 : Nat := 4983230072969 + 3 ^ 40 * 2793813 * 2
def baseEnd_2793813 : Nat := 3935717222989802270203

theorem tailTrace_2793813 : CollatzResearch.WordTrace tailWord_2793813 prefixEnd_2793813 3935717222989802270203 := by
  unfold tailWord_2793813
  simp only [CollatzResearch.WordTrace]
  refine ⟨101898731427500121118034093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67932487618333414078689395 101898731427500121118034093)
  ·
    refine ⟨38212024285312545419262785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101898731427500121118034093 38212024285312545419262785)
    ·
      refine ⟨28659018213984409064447089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38212024285312545419262785 28659018213984409064447089)
      ·
        refine ⟨21494263660488306798335317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28659018213984409064447089 21494263660488306798335317)
        ·
          refine ⟨3935717222989802270203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 14 21494263660488306798335317 3935717222989802270203)
          ·
            rfl

theorem cell22_2793813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 14].length) (baseStart_2793813 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2793813 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2793813 prefixEnd_2793813 := by exact prefixLift 2793813
  have htrace : WordTrace (prefixWord ++ tailWord_2793813) baseStart_2793813 baseEnd_2793813 := by
    simpa [prefixWord, tailWord_2793813, baseEnd_2793813] using wordTrace_append hprefix tailTrace_2793813
  have hstable : (prefixWord ++ tailWord_2793813).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2793813).length < 2 ^ (prefixWord ++ tailWord_2793813).sum := by decide
  have hdescent : baseEnd_2793813 < baseStart_2793813 := by decide
  rcases family_descends (prefixWord ++ tailWord_2793813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2793815 : List Nat := [1, 1, 3, 2, 3, 1, 1, 4, 2, 4]
def baseStart_2793815 : Nat := 118140960795 + 2793815 * 2 ^ 59
def prefixEnd_2793815 : Nat := 4983230072969 + 3 ^ 40 * 2793815 * 2
def baseEnd_2793815 : Nat := 956379969827394613109323

theorem tailTrace_2793815 : CollatzResearch.WordTrace tailWord_2793815 prefixEnd_2793815 956379969827394613109323 := by
  unfold tailWord_2793815
  simp only [CollatzResearch.WordTrace]
  refine ⟨101898804373492875459606899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67932536248995250306404599 101898804373492875459606899)
  ·
    refine ⟨152848206560239313189410349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101898804373492875459606899 152848206560239313189410349)
    ·
      refine ⟨57318077460089742446028881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 152848206560239313189410349 57318077460089742446028881)
      ·
        refine ⟨42988558095067306834521661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57318077460089742446028881 42988558095067306834521661)
        ·
          refine ⟨16120709285650240062945623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42988558095067306834521661 16120709285650240062945623)
          ·
            refine ⟨24181063928475360094418435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16120709285650240062945623 24181063928475360094418435)
            ·
              refine ⟨36271595892713040141627653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24181063928475360094418435 36271595892713040141627653)
              ·
                refine ⟨6800924229883695026555185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36271595892713040141627653 6800924229883695026555185)
                ·
                  refine ⟨5100693172412771269916389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6800924229883695026555185 5100693172412771269916389)
                  ·
                    refine ⟨956379969827394613109323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5100693172412771269916389 956379969827394613109323)
                    ·
                      rfl

theorem cell22_2793815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 4, 2, 4].length) (baseStart_2793815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2793815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2793815 prefixEnd_2793815 := by exact prefixLift 2793815
  have htrace : WordTrace (prefixWord ++ tailWord_2793815) baseStart_2793815 baseEnd_2793815 := by
    simpa [prefixWord, tailWord_2793815, baseEnd_2793815] using wordTrace_append hprefix tailTrace_2793815
  have hstable : (prefixWord ++ tailWord_2793815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2793815).length < 2 ^ (prefixWord ++ tailWord_2793815).sum := by decide
  have hdescent : baseEnd_2793815 < baseStart_2793815 := by decide
  rcases family_descends (prefixWord ++ tailWord_2793815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2793834 : List Nat := [3, 1, 3, 3, 1, 1, 2, 3, 2, 3]
def baseStart_2793834 : Nat := 118140960795 + 2793834 * 2 ^ 59
def prefixEnd_2793834 : Nat := 4983230072969 + 3 ^ 40 * 2793834 * 2
def baseEnd_2793834 : Nat := 956386473915684896884265

theorem tailTrace_2793834 : CollatzResearch.WordTrace tailWord_2793834 prefixEnd_2793834 956386473915684896884265 := by
  unfold tailWord_2793834
  simp only [CollatzResearch.WordTrace]
  refine ⟨25474874340106010426137139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67932998240282694469699037 25474874340106010426137139)
  ·
    refine ⟨38212311510159015639205709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25474874340106010426137139 38212311510159015639205709)
    ·
      refine ⟨14329616816309630864702141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38212311510159015639205709 14329616816309630864702141)
      ·
        refine ⟨5373606306116111574263303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14329616816309630864702141 5373606306116111574263303)
        ·
          refine ⟨8060409459174167361394955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5373606306116111574263303 8060409459174167361394955)
          ·
            refine ⟨12090614188761251042092433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8060409459174167361394955 12090614188761251042092433)
            ·
              refine ⟨9067960641570938281569325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12090614188761251042092433 9067960641570938281569325)
              ·
                refine ⟨3400485240589101855588497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9067960641570938281569325 3400485240589101855588497)
                ·
                  refine ⟨2550363930441826391691373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3400485240589101855588497 2550363930441826391691373)
                  ·
                    refine ⟨956386473915684896884265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2550363930441826391691373 956386473915684896884265)
                    ·
                      rfl

theorem cell22_2793834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 3, 2, 3].length) (baseStart_2793834 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2793834 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2793834 prefixEnd_2793834 := by exact prefixLift 2793834
  have htrace : WordTrace (prefixWord ++ tailWord_2793834) baseStart_2793834 baseEnd_2793834 := by
    simpa [prefixWord, tailWord_2793834, baseEnd_2793834] using wordTrace_append hprefix tailTrace_2793834
  have hstable : (prefixWord ++ tailWord_2793834).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2793834).length < 2 ^ (prefixWord ++ tailWord_2793834).sum := by decide
  have hdescent : baseEnd_2793834 < baseStart_2793834 := by decide
  rcases family_descends (prefixWord ++ tailWord_2793834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2793879 : List Nat := [1, 1, 3, 3, 1, 1, 4, 4, 1, 3]
def baseStart_2793879 : Nat := 118140960795 + 2793879 * 2 ^ 59
def prefixEnd_2793879 : Nat := 4983230072969 + 3 ^ 40 * 2793879 * 2
def baseEnd_2793879 : Nat := 956401878335319779509127

theorem tailTrace_2793879 : CollatzResearch.WordTrace tailWord_2793879 prefixEnd_2793879 956401878335319779509127 := by
  unfold tailWord_2793879
  simp only [CollatzResearch.WordTrace]
  refine ⟨101901138645261014389936691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67934092430174009593291127 101901138645261014389936691)
  ·
    refine ⟨152851707967891521584905037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101901138645261014389936691 152851707967891521584905037)
    ·
      refine ⟨57319390487959320594339389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 152851707967891521584905037 57319390487959320594339389)
      ·
        refine ⟨21494771432984745222877271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57319390487959320594339389 21494771432984745222877271)
        ·
          refine ⟨32242157149477117834315907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21494771432984745222877271 32242157149477117834315907)
          ·
            refine ⟨48363235724215676751473861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32242157149477117834315907 48363235724215676751473861)
            ·
              refine ⟨9068106698290439390901349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48363235724215676751473861 9068106698290439390901349)
              ·
                refine ⟨1700270005929457385794003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9068106698290439390901349 1700270005929457385794003)
                ·
                  refine ⟨2550405008894186078691005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1700270005929457385794003 2550405008894186078691005)
                  ·
                    refine ⟨956401878335319779509127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2550405008894186078691005 956401878335319779509127)
                    ·
                      rfl

theorem cell22_2793879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 4, 1, 3].length) (baseStart_2793879 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2793879 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2793879 prefixEnd_2793879 := by exact prefixLift 2793879
  have htrace : WordTrace (prefixWord ++ tailWord_2793879) baseStart_2793879 baseEnd_2793879 := by
    simpa [prefixWord, tailWord_2793879, baseEnd_2793879] using wordTrace_append hprefix tailTrace_2793879
  have hstable : (prefixWord ++ tailWord_2793879).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2793879).length < 2 ^ (prefixWord ++ tailWord_2793879).sum := by decide
  have hdescent : baseEnd_2793879 < baseStart_2793879 := by decide
  rcases family_descends (prefixWord ++ tailWord_2793879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2793898 : List Nat := [3, 1, 6, 1, 1, 2, 2, 6]
def baseStart_2793898 : Nat := 118140960795 + 2793898 * 2 ^ 59
def prefixEnd_2793898 : Nat := 4983230072969 + 3 ^ 40 * 2793898 * 2
def baseEnd_2793898 : Nat := 106267598047067784809341

theorem tailTrace_2793898 : CollatzResearch.WordTrace tailWord_2793898 prefixEnd_2793898 106267598047067784809341 := by
  unfold tailWord_2793898
  simp only [CollatzResearch.WordTrace]
  refine ⟨25475457908048045158719587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67934554421461453756585565 25475457908048045158719587)
  ·
    refine ⟨38213186862072067738079381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25475457908048045158719587 38213186862072067738079381)
    ·
      refine ⟨1791243134159628175222471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 38213186862072067738079381 1791243134159628175222471)
      ·
        refine ⟨2686864701239442262833707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1791243134159628175222471 2686864701239442262833707)
        ·
          refine ⟨4030297051859163394250561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2686864701239442262833707 4030297051859163394250561)
          ·
            refine ⟨3022722788894372545687921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4030297051859163394250561 3022722788894372545687921)
            ·
              refine ⟨2267042091670779409265941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3022722788894372545687921 2267042091670779409265941)
              ·
                refine ⟨106267598047067784809341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2267042091670779409265941 106267598047067784809341)
                ·
                  rfl

theorem cell22_2793898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 2, 6].length) (baseStart_2793898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2793898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2793898 prefixEnd_2793898 := by exact prefixLift 2793898
  have htrace : WordTrace (prefixWord ++ tailWord_2793898) baseStart_2793898 baseEnd_2793898 := by
    simpa [prefixWord, tailWord_2793898, baseEnd_2793898] using wordTrace_append hprefix tailTrace_2793898
  have hstable : (prefixWord ++ tailWord_2793898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2793898).length < 2 ^ (prefixWord ++ tailWord_2793898).sum := by decide
  have hdescent : baseEnd_2793898 < baseStart_2793898 := by decide
  rcases family_descends (prefixWord ++ tailWord_2793898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2793937 : List Nat := [1, 2, 2, 1, 2, 1, 1, 8, 4]
def baseStart_2793937 : Nat := 118140960795 + 2793937 * 2 ^ 59
def prefixEnd_2793937 : Nat := 4983230072969 + 3 ^ 40 * 2793937 * 2
def baseEnd_2793937 : Nat := 318807244306875653852983

theorem tailTrace_2793937 : CollatzResearch.WordTrace tailWord_2793937 prefixEnd_2793937 318807244306875653852983 := by
  unfold tailWord_2793937
  simp only [CollatzResearch.WordTrace]
  refine ⟨101903254079050890295548065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67935502719367260197032043 101903254079050890295548065)
  ·
    refine ⟨76427440559288167721661049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101903254079050890295548065 76427440559288167721661049)
    ·
      refine ⟨57320580419466125791245787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76427440559288167721661049 57320580419466125791245787)
      ·
        refine ⟨85980870629199188686868681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57320580419466125791245787 85980870629199188686868681)
        ·
          refine ⟨64485652971899391515151511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85980870629199188686868681 64485652971899391515151511)
          ·
            refine ⟨96728479457849087272727267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64485652971899391515151511 96728479457849087272727267)
            ·
              refine ⟨145092719186773630909090901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96728479457849087272727267 145092719186773630909090901)
              ·
                refine ⟨1700305302970003487215909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 145092719186773630909090901 1700305302970003487215909)
                ·
                  refine ⟨318807244306875653852983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1700305302970003487215909 318807244306875653852983)
                  ·
                    rfl

theorem cell22_2793937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 8, 4].length) (baseStart_2793937 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2793937 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2793937 prefixEnd_2793937 := by exact prefixLift 2793937
  have htrace : WordTrace (prefixWord ++ tailWord_2793937) baseStart_2793937 baseEnd_2793937 := by
    simpa [prefixWord, tailWord_2793937, baseEnd_2793937] using wordTrace_append hprefix tailTrace_2793937
  have hstable : (prefixWord ++ tailWord_2793937).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2793937).length < 2 ^ (prefixWord ++ tailWord_2793937).sum := by decide
  have hdescent : baseEnd_2793937 < baseStart_2793937 := by decide
  rcases family_descends (prefixWord ++ tailWord_2793937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2793973 : List Nat := [1, 3, 5, 1, 2, 1, 3, 1, 1, 4]
def baseStart_2793973 : Nat := 118140960795 + 2793973 * 2 ^ 59
def prefixEnd_2793973 : Nat := 4983230072969 + 3 ^ 40 * 2793973 * 2
def baseEnd_2793973 : Nat := 956434056456334867658839

theorem tailTrace_2793973 : CollatzResearch.WordTrace tailWord_2793973 prefixEnd_2793973 956434056456334867658839 := by
  unfold tailWord_2793973
  simp only [CollatzResearch.WordTrace]
  refine ⟨101904567106920468443858573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67936378071280312295905715 101904567106920468443858573)
  ·
    refine ⟨38214212665095175666446965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101904567106920468443858573 38214212665095175666446965)
    ·
      refine ⟨3582582437352672718729403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 38214212665095175666446965 3582582437352672718729403)
      ·
        refine ⟨5373873656029009078094105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3582582437352672718729403 5373873656029009078094105)
        ·
          refine ⟨4030405242021756808570579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5373873656029009078094105 4030405242021756808570579)
          ·
            refine ⟨6045607863032635212855869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4030405242021756808570579 6045607863032635212855869)
            ·
              refine ⟨2267102948637238204820951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6045607863032635212855869 2267102948637238204820951)
              ·
                refine ⟨3400654422955857307231427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2267102948637238204820951 3400654422955857307231427)
                ·
                  refine ⟨5100981634433785960847141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3400654422955857307231427 5100981634433785960847141)
                  ·
                    refine ⟨956434056456334867658839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5100981634433785960847141 956434056456334867658839)
                    ·
                      rfl

theorem cell22_2793973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 3, 1, 1, 4].length) (baseStart_2793973 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2793973 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2793973 prefixEnd_2793973 := by exact prefixLift 2793973
  have htrace : WordTrace (prefixWord ++ tailWord_2793973) baseStart_2793973 baseEnd_2793973 := by
    simpa [prefixWord, tailWord_2793973, baseEnd_2793973] using wordTrace_append hprefix tailTrace_2793973
  have hstable : (prefixWord ++ tailWord_2793973).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2793973).length < 2 ^ (prefixWord ++ tailWord_2793973).sum := by decide
  have hdescent : baseEnd_2793973 < baseStart_2793973 := by decide
  rcases family_descends (prefixWord ++ tailWord_2793973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2793988 : List Nat := [2, 3, 2, 3, 1, 3, 2, 2, 4]
def baseStart_2793988 : Nat := 118140960795 + 2793988 * 2 ^ 59
def prefixEnd_2793988 : Nat := 4983230072969 + 3 ^ 40 * 2793988 * 2
def baseEnd_2793988 : Nat := 318813063754293276177931

theorem tailTrace_2793988 : CollatzResearch.WordTrace tailWord_2793988 prefixEnd_2793988 318813063754293276177931 := by
  unfold tailWord_2793988
  simp only [CollatzResearch.WordTrace]
  refine ⟨50952557100933063002827309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67936742801244084003769745 50952557100933063002827309)
  ·
    refine ⟨19107208912849898626060241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50952557100933063002827309 19107208912849898626060241)
    ·
      refine ⟨14330406684637423969545181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19107208912849898626060241 14330406684637423969545181)
      ·
        refine ⟨5373902506739033988579443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14330406684637423969545181 5373902506739033988579443)
        ·
          refine ⟨8060853760108550982869165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5373902506739033988579443 8060853760108550982869165)
          ·
            refine ⟨3022820160040706618575937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8060853760108550982869165 3022820160040706618575937)
            ·
              refine ⟨2267115120030529963931953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3022820160040706618575937 2267115120030529963931953)
              ·
                refine ⟨1700336340022897472948965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2267115120030529963931953 1700336340022897472948965)
                ·
                  refine ⟨318813063754293276177931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1700336340022897472948965 318813063754293276177931)
                  ·
                    rfl

theorem cell22_2793988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 2, 2, 4].length) (baseStart_2793988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2793988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2793988 prefixEnd_2793988 := by exact prefixLift 2793988
  have htrace : WordTrace (prefixWord ++ tailWord_2793988) baseStart_2793988 baseEnd_2793988 := by
    simpa [prefixWord, tailWord_2793988, baseEnd_2793988] using wordTrace_append hprefix tailTrace_2793988
  have hstable : (prefixWord ++ tailWord_2793988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2793988).length < 2 ^ (prefixWord ++ tailWord_2793988).sum := by decide
  have hdescent : baseEnd_2793988 < baseStart_2793988 := by decide
  rcases family_descends (prefixWord ++ tailWord_2793988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2794042 : List Nat := [3, 1, 1, 1, 3, 3, 1, 2, 2, 5]
def baseStart_2794042 : Nat := 118140960795 + 2794042 * 2 ^ 59
def prefixEnd_2794042 : Nat := 4983230072969 + 3 ^ 40 * 2794042 * 2
def baseEnd_2794042 : Nat := 956457676566441687683627

theorem tailTrace_2794042 : CollatzResearch.WordTrace tailWord_2794042 prefixEnd_2794042 956457676566441687683627 := by
  unfold tailWord_2794042
  simp only [CollatzResearch.WordTrace]
  refine ⟨25476770935917623307030095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67938055829113662152080253 25476770935917623307030095)
  ·
    refine ⟨38215156403876434960545143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25476770935917623307030095 38215156403876434960545143)
    ·
      refine ⟨57322734605814652440817715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38215156403876434960545143 57322734605814652440817715)
      ·
        refine ⟨85984101908721978661226573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57322734605814652440817715 85984101908721978661226573)
        ·
          refine ⟨32244038215770741997959965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85984101908721978661226573 32244038215770741997959965)
          ·
            refine ⟨12091514330914028249234987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32244038215770741997959965 12091514330914028249234987)
            ·
              refine ⟨18137271496371042373852481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12091514330914028249234987 18137271496371042373852481)
              ·
                refine ⟨13602953622278281780389361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18137271496371042373852481 13602953622278281780389361)
                ·
                  refine ⟨10202215216708711335292021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13602953622278281780389361 10202215216708711335292021)
                  ·
                    refine ⟨956457676566441687683627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10202215216708711335292021 956457676566441687683627)
                    ·
                      rfl

theorem cell22_2794042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 2, 2, 5].length) (baseStart_2794042 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2794042 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2794042 prefixEnd_2794042 := by exact prefixLift 2794042
  have htrace : WordTrace (prefixWord ++ tailWord_2794042) baseStart_2794042 baseEnd_2794042 := by
    simpa [prefixWord, tailWord_2794042, baseEnd_2794042] using wordTrace_append hprefix tailTrace_2794042
  have hstable : (prefixWord ++ tailWord_2794042).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2794042).length < 2 ^ (prefixWord ++ tailWord_2794042).sum := by decide
  have hdescent : baseEnd_2794042 < baseStart_2794042 := by decide
  rcases family_descends (prefixWord ++ tailWord_2794042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2794044 : List Nat := [2, 2, 2, 2, 3, 1, 3, 2, 5]
def baseStart_2794044 : Nat := 118140960795 + 2794044 * 2 ^ 59
def prefixEnd_2794044 : Nat := 4983230072969 + 3 ^ 40 * 2794044 * 2
def baseEnd_2794044 : Nat := 318819453735771449711207

theorem tailTrace_2794044 : CollatzResearch.WordTrace tailWord_2794044 prefixEnd_2794044 318819453735771449711207 := by
  unfold tailWord_2794044
  simp only [CollatzResearch.WordTrace]
  refine ⟨50953578344831623784846593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67938104459775498379795457 50953578344831623784846593)
  ·
    refine ⟨38215183758623717838634945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50953578344831623784846593 38215183758623717838634945)
    ·
      refine ⟨28661387818967788378976209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38215183758623717838634945 28661387818967788378976209)
      ·
        refine ⟨21496040864225841284232157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28661387818967788378976209 21496040864225841284232157)
        ·
          refine ⟨8061015324084690481587059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21496040864225841284232157 8061015324084690481587059)
          ·
            refine ⟨12091522986127035722380589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8061015324084690481587059 12091522986127035722380589)
            ·
              refine ⟨4534321119797638395892721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12091522986127035722380589 4534321119797638395892721)
              ·
                refine ⟨3400740839848228796919541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4534321119797638395892721 3400740839848228796919541)
                ·
                  refine ⟨318819453735771449711207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3400740839848228796919541 318819453735771449711207)
                  ·
                    rfl

theorem cell22_2794044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 3, 2, 5].length) (baseStart_2794044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2794044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2794044 prefixEnd_2794044 := by exact prefixLift 2794044
  have htrace : WordTrace (prefixWord ++ tailWord_2794044) baseStart_2794044 baseEnd_2794044 := by
    simpa [prefixWord, tailWord_2794044, baseEnd_2794044] using wordTrace_append hprefix tailTrace_2794044
  have hstable : (prefixWord ++ tailWord_2794044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2794044).length < 2 ^ (prefixWord ++ tailWord_2794044).sum := by decide
  have hdescent : baseEnd_2794044 < baseStart_2794044 := by decide
  rcases family_descends (prefixWord ++ tailWord_2794044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2794072 : List Nat := [2, 1, 2, 2, 1, 2, 4, 2, 6]
def baseStart_2794072 : Nat := 118140960795 + 2794072 * 2 ^ 59
def prefixEnd_2794072 : Nat := 4983230072969 + 3 ^ 40 * 2794072 * 2
def baseEnd_2794072 : Nat := 318822648726510536477845

theorem tailTrace_2794072 : CollatzResearch.WordTrace tailWord_2794072 prefixEnd_2794072 318822648726510536477845 := by
  unfold tailWord_2794072
  simp only [CollatzResearch.WordTrace]
  refine ⟨50954088966780904175856235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67938785289041205567808313 50954088966780904175856235)
  ·
    refine ⟨76431133450171356263784353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50954088966780904175856235 76431133450171356263784353)
    ·
      refine ⟨57323350087628517197838265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76431133450171356263784353 57323350087628517197838265)
      ·
        refine ⟨42992512565721387898378699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57323350087628517197838265 42992512565721387898378699)
        ·
          refine ⟨64488768848582081847568049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42992512565721387898378699 64488768848582081847568049)
          ·
            refine ⟨48366576636436561385676037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64488768848582081847568049 48366576636436561385676037)
            ·
              refine ⟨9068733119331855259814257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48366576636436561385676037 9068733119331855259814257)
              ·
                refine ⟨6801549839498891444860693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9068733119331855259814257 6801549839498891444860693)
                ·
                  refine ⟨318822648726510536477845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6801549839498891444860693 318822648726510536477845)
                  ·
                    rfl

theorem cell22_2794072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 2, 6].length) (baseStart_2794072 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2794072 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2794072 prefixEnd_2794072 := by exact prefixLift 2794072
  have htrace : WordTrace (prefixWord ++ tailWord_2794072) baseStart_2794072 baseEnd_2794072 := by
    simpa [prefixWord, tailWord_2794072, baseEnd_2794072] using wordTrace_append hprefix tailTrace_2794072
  have hstable : (prefixWord ++ tailWord_2794072).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2794072).length < 2 ^ (prefixWord ++ tailWord_2794072).sum := by decide
  have hdescent : baseEnd_2794072 < baseStart_2794072 := by decide
  rcases family_descends (prefixWord ++ tailWord_2794072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2794082 : List Nat := [3, 3, 2, 3, 1, 2, 1, 3, 1, 3]
def baseStart_2794082 : Nat := 118140960795 + 2794082 * 2 ^ 59
def prefixEnd_2794082 : Nat := 4983230072969 + 3 ^ 40 * 2794082 * 2
def baseEnd_2794082 : Nat := 956471369383894916683505

theorem tailTrace_2794082 : CollatzResearch.WordTrace tailWord_2794082 prefixEnd_2794082 956471369383894916683505 := by
  unfold tailWord_2794082
  simp only [CollatzResearch.WordTrace]
  refine ⟨25477135665881395014894125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67939028442350386706384333 25477135665881395014894125)
  ·
    refine ⟨9553925874705523130585297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25477135665881395014894125 9553925874705523130585297)
    ·
      refine ⟨7165444406029142347938973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9553925874705523130585297 7165444406029142347938973)
      ·
        refine ⟨2687041652260928380477115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7165444406029142347938973 2687041652260928380477115)
        ·
          refine ⟨4030562478391392570715673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2687041652260928380477115 4030562478391392570715673)
          ·
            refine ⟨3022921858793544428036755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4030562478391392570715673 3022921858793544428036755)
            ·
              refine ⟨4534382788190316642055133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3022921858793544428036755 4534382788190316642055133)
              ·
                refine ⟨1700393545571368740770675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4534382788190316642055133 1700393545571368740770675)
                ·
                  refine ⟨2550590318357053111156013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1700393545571368740770675 2550590318357053111156013)
                  ·
                    refine ⟨956471369383894916683505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2550590318357053111156013 956471369383894916683505)
                    ·
                      rfl

theorem cell22_2794082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 1, 3, 1, 3].length) (baseStart_2794082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2794082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2794082 prefixEnd_2794082 := by exact prefixLift 2794082
  have htrace : WordTrace (prefixWord ++ tailWord_2794082) baseStart_2794082 baseEnd_2794082 := by
    simpa [prefixWord, tailWord_2794082, baseEnd_2794082] using wordTrace_append hprefix tailTrace_2794082
  have hstable : (prefixWord ++ tailWord_2794082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2794082).length < 2 ^ (prefixWord ++ tailWord_2794082).sum := by decide
  have hdescent : baseEnd_2794082 < baseStart_2794082 := by decide
  rcases family_descends (prefixWord ++ tailWord_2794082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2794087 : List Nat := [1, 1, 5, 1, 1, 1, 1, 3, 3, 5]
def baseStart_2794087 : Nat := 118140960795 + 2794087 * 2 ^ 59
def prefixEnd_2794087 : Nat := 4983230072969 + 3 ^ 40 * 2794087 * 2
def baseEnd_2794087 : Nat := 956473080986076570308489

theorem tailTrace_2794087 : CollatzResearch.WordTrace tailWord_2794087 prefixEnd_2794087 956473080986076570308489 := by
  unfold tailWord_2794087
  simp only [CollatzResearch.WordTrace]
  refine ⟨101908725028507465913508515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67939150019004977275672343 101908725028507465913508515)
  ·
    refine ⟨152863087542761198870262773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101908725028507465913508515 152863087542761198870262773)
    ·
      refine ⟨14330914457133862394087135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 152863087542761198870262773 14330914457133862394087135)
      ·
        refine ⟨21496371685700793591130703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14330914457133862394087135 21496371685700793591130703)
        ·
          refine ⟨32244557528551190386696055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21496371685700793591130703 32244557528551190386696055)
          ·
            refine ⟨48366836292826785580044083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32244557528551190386696055 48366836292826785580044083)
            ·
              refine ⟨72550254439240178370066125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48366836292826785580044083 72550254439240178370066125)
              ·
                refine ⟨27206345414715066888774797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72550254439240178370066125 27206345414715066888774797)
                ·
                  refine ⟨10202379530518150083290549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27206345414715066888774797 10202379530518150083290549)
                  ·
                    refine ⟨956473080986076570308489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10202379530518150083290549 956473080986076570308489)
                    ·
                      rfl

theorem cell22_2794087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 3, 3, 5].length) (baseStart_2794087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2794087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2794087 prefixEnd_2794087 := by exact prefixLift 2794087
  have htrace : WordTrace (prefixWord ++ tailWord_2794087) baseStart_2794087 baseEnd_2794087 := by
    simpa [prefixWord, tailWord_2794087, baseEnd_2794087] using wordTrace_append hprefix tailTrace_2794087
  have hstable : (prefixWord ++ tailWord_2794087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2794087).length < 2 ^ (prefixWord ++ tailWord_2794087).sum := by decide
  have hdescent : baseEnd_2794087 < baseStart_2794087 := by decide
  rcases family_descends (prefixWord ++ tailWord_2794087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2794117 : List Nat := [1, 3, 1, 1, 4, 2, 1, 9]
def baseStart_2794117 : Nat := 118140960795 + 2794117 * 2 ^ 59
def prefixEnd_2794117 : Nat := 4983230072969 + 3 ^ 40 * 2794117 * 2
def baseEnd_2794117 : Nat := 106275927844351832450933

theorem tailTrace_2794117 : CollatzResearch.WordTrace tailWord_2794117 prefixEnd_2794117 106275927844351832450933 := by
  unfold tailWord_2794117
  simp only [CollatzResearch.WordTrace]
  refine ⟨101909819218398781037100605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67939879478932520691400403 101909819218398781037100605)
  ·
    refine ⟨38216182206899542888912727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101909819218398781037100605 38216182206899542888912727)
    ·
      refine ⟨57324273310349314333369091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38216182206899542888912727 57324273310349314333369091)
      ·
        refine ⟨85986409965523971500053637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57324273310349314333369091 85986409965523971500053637)
        ·
          refine ⟨16122451868535744656260057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 85986409965523971500053637 16122451868535744656260057)
          ·
            refine ⟨12091838901401808492195043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16122451868535744656260057 12091838901401808492195043)
            ·
              refine ⟨18137758352102712738292565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12091838901401808492195043 18137758352102712738292565)
              ·
                refine ⟨106275927844351832450933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18137758352102712738292565 106275927844351832450933)
                ·
                  rfl

theorem cell22_2794117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 9].length) (baseStart_2794117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2794117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2794117 prefixEnd_2794117 := by exact prefixLift 2794117
  have htrace : WordTrace (prefixWord ++ tailWord_2794117) baseStart_2794117 baseEnd_2794117 := by
    simpa [prefixWord, tailWord_2794117, baseEnd_2794117] using wordTrace_append hprefix tailTrace_2794117
  have hstable : (prefixWord ++ tailWord_2794117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2794117).length < 2 ^ (prefixWord ++ tailWord_2794117).sum := by decide
  have hdescent : baseEnd_2794117 < baseStart_2794117 := by decide
  rcases family_descends (prefixWord ++ tailWord_2794117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2794151 : List Nat := [1, 1, 6, 3, 2, 9]
def baseStart_2794151 : Nat := 118140960795 + 2794151 * 2 ^ 59
def prefixEnd_2794151 : Nat := 4983230072969 + 3 ^ 40 * 2794151 * 2
def baseEnd_2794151 : Nat := 11808580117209897984053

theorem tailTrace_2794151 : CollatzResearch.WordTrace tailWord_2794151 prefixEnd_2794151 11808580117209897984053 := by
  unfold tailWord_2794151
  simp only [CollatzResearch.WordTrace]
  refine ⟨101911059300275604843838307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67940706200183736562558871 101911059300275604843838307)
  ·
    refine ⟨152866588950413407265757461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101911059300275604843838307 152866588950413407265757461)
    ·
      refine ⟨7165621357050628465582381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 152866588950413407265757461 7165621357050628465582381)
      ·
        refine ⟨2687108008893985674593393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7165621357050628465582381 2687108008893985674593393)
        ·
          refine ⟨2015331006670489255945045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2687108008893985674593393 2015331006670489255945045)
          ·
            refine ⟨11808580117209897984053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2015331006670489255945045 11808580117209897984053)
            ·
              rfl

theorem cell22_2794151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 9].length) (baseStart_2794151 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2794151 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2794151 prefixEnd_2794151 := by exact prefixLift 2794151
  have htrace : WordTrace (prefixWord ++ tailWord_2794151) baseStart_2794151 baseEnd_2794151 := by
    simpa [prefixWord, tailWord_2794151, baseEnd_2794151] using wordTrace_append hprefix tailTrace_2794151
  have hstable : (prefixWord ++ tailWord_2794151).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2794151).length < 2 ^ (prefixWord ++ tailWord_2794151).sum := by decide
  have hdescent : baseEnd_2794151 < baseStart_2794151 := by decide
  rcases family_descends (prefixWord ++ tailWord_2794151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2794224 : List Nat := [2, 1, 1, 1, 3, 1, 6, 1, 6]
def baseStart_2794224 : Nat := 118140960795 + 2794224 * 2 ^ 59
def prefixEnd_2794224 : Nat := 4983230072969 + 3 ^ 40 * 2794224 * 2
def baseEnd_2794224 : Nat := 318839992961951293211023

theorem tailTrace_2794224 : CollatzResearch.WordTrace tailWord_2794224 prefixEnd_2794224 318839992961951293211023 := by
  unfold tailWord_2794224
  simp only [CollatzResearch.WordTrace]
  refine ⟨50956860914505569155622863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67942481219340758874163817 50956860914505569155622863)
  ·
    refine ⟨76435291371758353733434295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50956860914505569155622863 76435291371758353733434295)
    ·
      refine ⟨114652937057637530600151443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76435291371758353733434295 114652937057637530600151443)
      ·
        refine ⟨171979405586456295900227165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114652937057637530600151443 171979405586456295900227165)
        ·
          refine ⟨64492277094921110962585187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 171979405586456295900227165 64492277094921110962585187)
          ·
            refine ⟨96738415642381666443877781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64492277094921110962585187 96738415642381666443877781)
            ·
              refine ⟨4534613233236640614556771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 96738415642381666443877781 4534613233236640614556771)
              ·
                refine ⟨6801919849854960921835157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4534613233236640614556771 6801919849854960921835157)
                ·
                  refine ⟨318839992961951293211023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6801919849854960921835157 318839992961951293211023)
                  ·
                    rfl

theorem cell22_2794224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 6, 1, 6].length) (baseStart_2794224 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2794224 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2794224 prefixEnd_2794224 := by exact prefixLift 2794224
  have htrace : WordTrace (prefixWord ++ tailWord_2794224) baseStart_2794224 baseEnd_2794224 := by
    simpa [prefixWord, tailWord_2794224, baseEnd_2794224] using wordTrace_append hprefix tailTrace_2794224
  have hstable : (prefixWord ++ tailWord_2794224).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2794224).length < 2 ^ (prefixWord ++ tailWord_2794224).sum := by decide
  have hdescent : baseEnd_2794224 < baseStart_2794224 := by decide
  rcases family_descends (prefixWord ++ tailWord_2794224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2794271 : List Nat := [1, 1, 2, 4, 2, 3, 1, 2, 2, 4]
def baseStart_2794271 : Nat := 118140960795 + 2794271 * 2 ^ 59
def prefixEnd_2794271 : Nat := 4983230072969 + 3 ^ 40 * 2794271 * 2
def baseEnd_2794271 : Nat := 956536067946361423707925

theorem tailTrace_2794271 : CollatzResearch.WordTrace tailWord_2794271 prefixEnd_2794271 956536067946361423707925 := by
  unfold tailWord_2794271
  simp only [CollatzResearch.WordTrace]
  refine ⟨101915436059840865338206667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67943624039893910225471111 101915436059840865338206667)
  ·
    refine ⟨152873154089761298007310001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101915436059840865338206667 152873154089761298007310001)
    ·
      refine ⟨114654865567320973505482501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152873154089761298007310001 114654865567320973505482501)
      ·
        refine ⟨21497787293872682532277969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 114654865567320973505482501 21497787293872682532277969)
        ·
          refine ⟨16123340470404511899208477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21497787293872682532277969 16123340470404511899208477)
          ·
            refine ⟨6046252676401691962203179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16123340470404511899208477 6046252676401691962203179)
            ·
              refine ⟨9069379014602537943304769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6046252676401691962203179 9069379014602537943304769)
              ·
                refine ⟨6802034260951903457478577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9069379014602537943304769 6802034260951903457478577)
                ·
                  refine ⟨5101525695713927593108933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6802034260951903457478577 5101525695713927593108933)
                  ·
                    refine ⟨956536067946361423707925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5101525695713927593108933 956536067946361423707925)
                    ·
                      rfl

theorem cell22_2794271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 2, 2, 4].length) (baseStart_2794271 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2794271 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2794271 prefixEnd_2794271 := by exact prefixLift 2794271
  have htrace : WordTrace (prefixWord ++ tailWord_2794271) baseStart_2794271 baseEnd_2794271 := by
    simpa [prefixWord, tailWord_2794271, baseEnd_2794271] using wordTrace_append hprefix tailTrace_2794271
  have hstable : (prefixWord ++ tailWord_2794271).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2794271).length < 2 ^ (prefixWord ++ tailWord_2794271).sum := by decide
  have hdescent : baseEnd_2794271 < baseStart_2794271 := by decide
  rcases family_descends (prefixWord ++ tailWord_2794271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2794286 : List Nat := [4, 1, 3, 2, 1, 1, 1, 9]
def baseStart_2794286 : Nat := 118140960795 + 2794286 * 2 ^ 59
def prefixEnd_2794286 : Nat := 4983230072969 + 3 ^ 40 * 2794286 * 2
def baseEnd_2794286 : Nat := 106282355861434042731431

theorem tailTrace_2794286 : CollatzResearch.WordTrace tailWord_2794286 prefixEnd_2794286 106282355861434042731431 := by
  unfold tailWord_2794286
  simp only [CollatzResearch.WordTrace]
  refine ⟨12739497894348315362500339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67943988769857681933335141 12739497894348315362500339)
  ·
    refine ⟨19109246841522473043750509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12739497894348315362500339 19109246841522473043750509)
    ·
      refine ⟨7165967565570927391406441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19109246841522473043750509 7165967565570927391406441)
      ·
        refine ⟨5374475674178195543554831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7165967565570927391406441 5374475674178195543554831)
        ·
          refine ⟨8061713511267293315332247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5374475674178195543554831 8061713511267293315332247)
          ·
            refine ⟨12092570266900939972998371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8061713511267293315332247 12092570266900939972998371)
            ·
              refine ⟨18138855400351409959497557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12092570266900939972998371 18138855400351409959497557)
              ·
                refine ⟨106282355861434042731431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18138855400351409959497557 106282355861434042731431)
                ·
                  rfl

theorem cell22_2794286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 9].length) (baseStart_2794286 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2794286 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2794286 prefixEnd_2794286 := by exact prefixLift 2794286
  have htrace : WordTrace (prefixWord ++ tailWord_2794286) baseStart_2794286 baseEnd_2794286 := by
    simpa [prefixWord, tailWord_2794286, baseEnd_2794286] using wordTrace_append hprefix tailTrace_2794286
  have hstable : (prefixWord ++ tailWord_2794286).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2794286).length < 2 ^ (prefixWord ++ tailWord_2794286).sum := by decide
  have hdescent : baseEnd_2794286 < baseStart_2794286 := by decide
  rcases family_descends (prefixWord ++ tailWord_2794286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2794305 : List Nat := [1, 2, 5, 3, 1, 1, 2, 1, 2, 4]
def baseStart_2794305 : Nat := 118140960795 + 2794305 * 2 ^ 59
def prefixEnd_2794305 : Nat := 4983230072969 + 3 ^ 40 * 2794305 * 2
def baseEnd_2794305 : Nat := 956547706841196668357821

theorem tailTrace_2794305 : CollatzResearch.WordTrace tailWord_2794305 prefixEnd_2794305 956547706841196668357821 := by
  unfold tailWord_2794305
  simp only [CollatzResearch.WordTrace]
  refine ⟨101916676141717689144944369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67944450761145126096629579 101916676141717689144944369)
  ·
    refine ⟨76437507106288266858708277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101916676141717689144944369 76437507106288266858708277)
    ·
      refine ⟨7166016291214525018003901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 76437507106288266858708277 7166016291214525018003901)
      ·
        refine ⟨2687256109205446881751463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7166016291214525018003901 2687256109205446881751463)
        ·
          refine ⟨4030884163808170322627195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2687256109205446881751463 4030884163808170322627195)
          ·
            refine ⟨6046326245712255483940793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4030884163808170322627195 6046326245712255483940793)
            ·
              refine ⟨4534744684284191612955595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6046326245712255483940793 4534744684284191612955595)
              ·
                refine ⟨6802117026426287419433393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4534744684284191612955595 6802117026426287419433393)
                ·
                  refine ⟨5101587769819715564575045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6802117026426287419433393 5101587769819715564575045)
                  ·
                    refine ⟨956547706841196668357821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5101587769819715564575045 956547706841196668357821)
                    ·
                      rfl

theorem cell22_2794305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 2, 1, 2, 4].length) (baseStart_2794305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2794305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2794305 prefixEnd_2794305 := by exact prefixLift 2794305
  have htrace : WordTrace (prefixWord ++ tailWord_2794305) baseStart_2794305 baseEnd_2794305 := by
    simpa [prefixWord, tailWord_2794305, baseEnd_2794305] using wordTrace_append hprefix tailTrace_2794305
  have hstable : (prefixWord ++ tailWord_2794305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2794305).length < 2 ^ (prefixWord ++ tailWord_2794305).sum := by decide
  have hdescent : baseEnd_2794305 < baseStart_2794305 := by decide
  rcases family_descends (prefixWord ++ tailWord_2794305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2794314 : List Nat := [3, 1, 2, 1, 1, 1, 2, 4, 7]
def baseStart_2794314 : Nat := 118140960795 + 2794314 * 2 ^ 59
def prefixEnd_2794314 : Nat := 4983230072969 + 3 ^ 40 * 2794314 * 2
def baseEnd_2794314 : Nat := 318850262575041214960931

theorem tailTrace_2794314 : CollatzResearch.WordTrace tailWord_2794314 prefixEnd_2794314 318850262575041214960931 := by
  unfold tailWord_2794314
  simp only [CollatzResearch.WordTrace]
  refine ⟨25479251099671270920505499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67944669599123389121347997 25479251099671270920505499)
  ·
    refine ⟨38218876649506906380758249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25479251099671270920505499 38218876649506906380758249)
    ·
      refine ⟨28664157487130179785568687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38218876649506906380758249 28664157487130179785568687)
      ·
        refine ⟨42996236230695269678353031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28664157487130179785568687 42996236230695269678353031)
        ·
          refine ⟨64494354346042904517529547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42996236230695269678353031 64494354346042904517529547)
          ·
            refine ⟨96741531519064356776294321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64494354346042904517529547 96741531519064356776294321)
            ·
              refine ⟨72556148639298267582220741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96741531519064356776294321 72556148639298267582220741)
              ·
                refine ⟨13604277869868425171666389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 72556148639298267582220741 13604277869868425171666389)
                ·
                  refine ⟨318850262575041214960931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13604277869868425171666389 318850262575041214960931)
                  ·
                    rfl

theorem cell22_2794314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 4, 7].length) (baseStart_2794314 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2794314 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2794314 prefixEnd_2794314 := by exact prefixLift 2794314
  have htrace : WordTrace (prefixWord ++ tailWord_2794314) baseStart_2794314 baseEnd_2794314 := by
    simpa [prefixWord, tailWord_2794314, baseEnd_2794314] using wordTrace_append hprefix tailTrace_2794314
  have hstable : (prefixWord ++ tailWord_2794314).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2794314).length < 2 ^ (prefixWord ++ tailWord_2794314).sum := by decide
  have hdescent : baseEnd_2794314 < baseStart_2794314 := by decide
  rcases family_descends (prefixWord ++ tailWord_2794314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2794361 : List Nat := [1, 2, 1, 3, 2, 3, 2, 1, 3, 4]
def baseStart_2794361 : Nat := 118140960795 + 2794361 * 2 ^ 59
def prefixEnd_2794361 : Nat := 4983230072969 + 3 ^ 40 * 2794361 * 2
def baseEnd_2794361 : Nat := 956566876785631188957649

theorem tailTrace_2794361 : CollatzResearch.WordTrace tailWord_2794361 prefixEnd_2794361 956566876785631188957649 := by
  unfold tailWord_2794361
  simp only [CollatzResearch.WordTrace]
  refine ⟨101918718629514810708982937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67945812419676540472655291 101918718629514810708982937)
  ·
    refine ⟨76439038972136108031737203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101918718629514810708982937 76439038972136108031737203)
    ·
      refine ⟨114658558458204162047605805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76439038972136108031737203 114658558458204162047605805)
      ·
        refine ⟨42996959421826560767852177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 114658558458204162047605805 42996959421826560767852177)
        ·
          refine ⟨32247719566369920575889133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42996959421826560767852177 32247719566369920575889133)
          ·
            refine ⟨12092894837388720215958425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32247719566369920575889133 12092894837388720215958425)
            ·
              refine ⟨9069671128041540161968819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12092894837388720215958425 9069671128041540161968819)
              ·
                refine ⟨13604506692062310242953229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9069671128041540161968819 13604506692062310242953229)
                ·
                  refine ⟨5101690009523366341107461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13604506692062310242953229 5101690009523366341107461)
                  ·
                    refine ⟨956566876785631188957649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5101690009523366341107461 956566876785631188957649)
                    ·
                      rfl

theorem cell22_2794361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 1, 3, 4].length) (baseStart_2794361 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2794361 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2794361 prefixEnd_2794361 := by exact prefixLift 2794361
  have htrace : WordTrace (prefixWord ++ tailWord_2794361) baseStart_2794361 baseEnd_2794361 := by
    simpa [prefixWord, tailWord_2794361, baseEnd_2794361] using wordTrace_append hprefix tailTrace_2794361
  have hstable : (prefixWord ++ tailWord_2794361).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2794361).length < 2 ^ (prefixWord ++ tailWord_2794361).sum := by decide
  have hdescent : baseEnd_2794361 < baseStart_2794361 := by decide
  rcases family_descends (prefixWord ++ tailWord_2794361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2794421 : List Nat := [1, 3, 3, 2, 1, 1, 3, 8]
def baseStart_2794421 : Nat := 118140960795 + 2794421 * 2 ^ 59
def prefixEnd_2794421 : Nat := 4983230072969 + 3 ^ 40 * 2794421 * 2
def baseEnd_2794421 : Nat := 106287490667979003606385

theorem tailTrace_2794421 : CollatzResearch.WordTrace tailWord_2794421 prefixEnd_2794421 106287490667979003606385 := by
  unfold tailWord_2794421
  simp only [CollatzResearch.WordTrace]
  refine ⟨101920907009297440956167117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67947271339531627304111411 101920907009297440956167117)
  ·
    refine ⟨38220340128486540358562669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101920907009297440956167117 38220340128486540358562669)
    ·
      refine ⟨14332627548182452634461001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38220340128486540358562669 14332627548182452634461001)
      ·
        refine ⟨10749470661136839475845751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14332627548182452634461001 10749470661136839475845751)
        ·
          refine ⟨16124205991705259213768627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10749470661136839475845751 16124205991705259213768627)
          ·
            refine ⟨24186308987557888820652941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16124205991705259213768627 24186308987557888820652941)
            ·
              refine ⟨9069865870334208307744853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24186308987557888820652941 9069865870334208307744853)
              ·
                refine ⟨106287490667979003606385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9069865870334208307744853 106287490667979003606385)
                ·
                  rfl

theorem cell22_2794421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 8].length) (baseStart_2794421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2794421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2794421 prefixEnd_2794421 := by exact prefixLift 2794421
  have htrace : WordTrace (prefixWord ++ tailWord_2794421) baseStart_2794421 baseEnd_2794421 := by
    simpa [prefixWord, tailWord_2794421, baseEnd_2794421] using wordTrace_append hprefix tailTrace_2794421
  have hstable : (prefixWord ++ tailWord_2794421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2794421).length < 2 ^ (prefixWord ++ tailWord_2794421).sum := by decide
  have hdescent : baseEnd_2794421 < baseStart_2794421 := by decide
  rcases family_descends (prefixWord ++ tailWord_2794421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2794504 : List Nat := [2, 1, 3, 2, 1, 5, 2, 2, 1, 3]
def baseStart_2794504 : Nat := 118140960795 + 2794504 * 2 ^ 59
def prefixEnd_2794504 : Nat := 4983230072969 + 3 ^ 40 * 2794504 * 2
def baseEnd_2794504 : Nat := 956615828608026482632211

theorem tailTrace_2794504 : CollatzResearch.WordTrace tailWord_2794504 prefixEnd_2794504 956615828608026482632211 := by
  unfold tailWord_2794504
  simp only [CollatzResearch.WordTrace]
  refine ⟨50961967133998373065719283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67949289511997830754292377 50961967133998373065719283)
  ·
    refine ⟨76442950700997559598578925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50961967133998373065719283 76442950700997559598578925)
    ·
      refine ⟨28666106512874084849467097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76442950700997559598578925 28666106512874084849467097)
      ·
        refine ⟨21499579884655563637100323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28666106512874084849467097 21499579884655563637100323)
        ·
          refine ⟨32249369826983345455650485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21499579884655563637100323 32249369826983345455650485)
          ·
            refine ⟨3023378421279688636467233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 32249369826983345455650485 3023378421279688636467233)
            ·
              refine ⟨2267533815959766477350425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3023378421279688636467233 2267533815959766477350425)
              ·
                refine ⟨1700650361969824858012819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2267533815959766477350425 1700650361969824858012819)
                ·
                  refine ⟨2550975542954737287019229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1700650361969824858012819 2550975542954737287019229)
                  ·
                    refine ⟨956615828608026482632211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2550975542954737287019229 956615828608026482632211)
                    ·
                      rfl

theorem cell22_2794504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 2, 2, 1, 3].length) (baseStart_2794504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2794504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2794504 prefixEnd_2794504 := by exact prefixLift 2794504
  have htrace : WordTrace (prefixWord ++ tailWord_2794504) baseStart_2794504 baseEnd_2794504 := by
    simpa [prefixWord, tailWord_2794504, baseEnd_2794504] using wordTrace_append hprefix tailTrace_2794504
  have hstable : (prefixWord ++ tailWord_2794504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2794504).length < 2 ^ (prefixWord ++ tailWord_2794504).sum := by decide
  have hdescent : baseEnd_2794504 < baseStart_2794504 := by decide
  rcases family_descends (prefixWord ++ tailWord_2794504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2794545 : List Nat := [1, 2, 2, 3, 1, 2, 4, 3, 4]
def baseStart_2794545 : Nat := 118140960795 + 2794545 * 2 ^ 59
def prefixEnd_2794545 : Nat := 4983230072969 + 3 ^ 40 * 2794545 * 2
def baseEnd_2794545 : Nat := 318876621248638680785695

theorem tailTrace_2794545 : CollatzResearch.WordTrace tailWord_2794545 prefixEnd_2794545 318876621248638680785695 := by
  unfold tailWord_2794545
  simp only [CollatzResearch.WordTrace]
  refine ⟨101925429660848210133681089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67950286440565473422454059 101925429660848210133681089)
  ·
    refine ⟨76444072245636157600260817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101925429660848210133681089 76444072245636157600260817)
    ·
      refine ⟨57333054184227118200195613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76444072245636157600260817 57333054184227118200195613)
      ·
        refine ⟨21499895319085169325073355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57333054184227118200195613 21499895319085169325073355)
        ·
          refine ⟨32249842978627753987610033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21499895319085169325073355 32249842978627753987610033)
          ·
            refine ⟨24187382233970815490707525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32249842978627753987610033 24187382233970815490707525)
            ·
              refine ⟨4535134168869527904507661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24187382233970815490707525 4535134168869527904507661)
              ·
                refine ⟨1700675313326072964190373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4535134168869527904507661 1700675313326072964190373)
                ·
                  refine ⟨318876621248638680785695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1700675313326072964190373 318876621248638680785695)
                  ·
                    rfl

theorem cell22_2794545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 4, 3, 4].length) (baseStart_2794545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2794545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2794545 prefixEnd_2794545 := by exact prefixLift 2794545
  have htrace : WordTrace (prefixWord ++ tailWord_2794545) baseStart_2794545 baseEnd_2794545 := by
    simpa [prefixWord, tailWord_2794545, baseEnd_2794545] using wordTrace_append hprefix tailTrace_2794545
  have hstable : (prefixWord ++ tailWord_2794545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2794545).length < 2 ^ (prefixWord ++ tailWord_2794545).sum := by decide
  have hdescent : baseEnd_2794545 < baseStart_2794545 := by decide
  rcases family_descends (prefixWord ++ tailWord_2794545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2794571 : List Nat := [1, 1, 1, 1, 3, 1, 2, 1, 4, 7]
def baseStart_2794571 : Nat := 118140960795 + 2794571 * 2 ^ 59
def prefixEnd_2794571 : Nat := 4983230072969 + 3 ^ 40 * 2794571 * 2
def baseEnd_2794571 : Nat := 956638764077260641207005

theorem tailTrace_2794571 : CollatzResearch.WordTrace tailWord_2794571 prefixEnd_2794571 956638764077260641207005 := by
  unfold tailWord_2794571
  simp only [CollatzResearch.WordTrace]
  refine ⟨101926377958754016574127567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67950918639169344382751711 101926377958754016574127567)
  ·
    refine ⟨152889566938131024861191351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101926377958754016574127567 152889566938131024861191351)
    ·
      refine ⟨229334350407196537291787027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152889566938131024861191351 229334350407196537291787027)
      ·
        refine ⟨344001525610794805937680541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 229334350407196537291787027 344001525610794805937680541)
        ·
          refine ⟨129000572104048052226630203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 344001525610794805937680541 129000572104048052226630203)
          ·
            refine ⟨193500858156072078339945305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129000572104048052226630203 193500858156072078339945305)
            ·
              refine ⟨145125643617054058754958979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 193500858156072078339945305 145125643617054058754958979)
              ·
                refine ⟨217688465425581088132438469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 145125643617054058754958979 217688465425581088132438469)
                ·
                  refine ⟨40816587267296454024832213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 217688465425581088132438469 40816587267296454024832213)
                  ·
                    refine ⟨956638764077260641207005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40816587267296454024832213 956638764077260641207005)
                    ·
                      rfl

theorem cell22_2794571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 4, 7].length) (baseStart_2794571 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2794571 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2794571 prefixEnd_2794571 := by exact prefixLift 2794571
  have htrace : WordTrace (prefixWord ++ tailWord_2794571) baseStart_2794571 baseEnd_2794571 := by
    simpa [prefixWord, tailWord_2794571, baseEnd_2794571] using wordTrace_append hprefix tailTrace_2794571
  have hstable : (prefixWord ++ tailWord_2794571).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2794571).length < 2 ^ (prefixWord ++ tailWord_2794571).sum := by decide
  have hdescent : baseEnd_2794571 < baseStart_2794571 := by decide
  rcases family_descends (prefixWord ++ tailWord_2794571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2794588 : List Nat := [2, 2, 4, 1, 1, 1, 1, 1, 2, 7]
def baseStart_2794588 : Nat := 118140960795 + 2794588 * 2 ^ 59
def prefixEnd_2794588 : Nat := 4983230072969 + 3 ^ 40 * 2794588 * 2
def baseEnd_2794588 : Nat := 956644583524678263531953

theorem tailTrace_2794588 : CollatzResearch.WordTrace tailWord_2794588 prefixEnd_2794588 956644583524678263531953 := by
  unfold tailWord_2794588
  simp only [CollatzResearch.WordTrace]
  refine ⟨50963498999846214238748209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67951331999794952318330945 50963498999846214238748209)
  ·
    refine ⟨38222624249884660679061157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50963498999846214238748209 38222624249884660679061157)
    ·
      refine ⟨7166742046853373877323967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38222624249884660679061157 7166742046853373877323967)
      ·
        refine ⟨10750113070280060815985951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7166742046853373877323967 10750113070280060815985951)
        ·
          refine ⟨16125169605420091223978927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10750113070280060815985951 16125169605420091223978927)
          ·
            refine ⟨24187754408130136835968391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16125169605420091223978927 24187754408130136835968391)
            ·
              refine ⟨36281631612195205253952587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24187754408130136835968391 36281631612195205253952587)
              ·
                refine ⟨54422447418292807880928881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36281631612195205253952587 54422447418292807880928881)
                ·
                  refine ⟨40816835563719605910696661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54422447418292807880928881 40816835563719605910696661)
                  ·
                    refine ⟨956644583524678263531953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40816835563719605910696661 956644583524678263531953)
                    ·
                      rfl

theorem cell22_2794588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 1, 2, 7].length) (baseStart_2794588 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2794588 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2794588 prefixEnd_2794588 := by exact prefixLift 2794588
  have htrace : WordTrace (prefixWord ++ tailWord_2794588) baseStart_2794588 baseEnd_2794588 := by
    simpa [prefixWord, tailWord_2794588, baseEnd_2794588] using wordTrace_append hprefix tailTrace_2794588
  have hstable : (prefixWord ++ tailWord_2794588).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2794588).length < 2 ^ (prefixWord ++ tailWord_2794588).sum := by decide
  have hdescent : baseEnd_2794588 < baseStart_2794588 := by decide
  rcases family_descends (prefixWord ++ tailWord_2794588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2794693 : List Nat := [1, 3, 1, 1, 1, 1, 3, 4, 1, 6]
def baseStart_2794693 : Nat := 118140960795 + 2794693 * 2 ^ 59
def prefixEnd_2794693 : Nat := 4983230072969 + 3 ^ 40 * 2794693 * 2
def baseEnd_2794693 : Nat := 956680527170492989656631

theorem tailTrace_2794693 : CollatzResearch.WordTrace tailWord_2794693 prefixEnd_2794693 956680527170492989656631 := by
  unfold tailWord_2794693
  simp only [CollatzResearch.WordTrace]
  refine ⟨101930827664312031410068733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67953885109541354273379155 101930827664312031410068733)
  ·
    refine ⟨38224060374117011778775775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101930827664312031410068733 38224060374117011778775775)
    ·
      refine ⟨57336090561175517668163663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38224060374117011778775775 57336090561175517668163663)
      ·
        refine ⟨86004135841763276502245495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57336090561175517668163663 86004135841763276502245495)
        ·
          refine ⟨129006203762644914753368243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86004135841763276502245495 129006203762644914753368243)
          ·
            refine ⟨193509305643967372130052365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129006203762644914753368243 193509305643967372130052365)
            ·
              refine ⟨72565989616487764548769637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 193509305643967372130052365 72565989616487764548769637)
              ·
                refine ⟨13606123053091455852894307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 72565989616487764548769637 13606123053091455852894307)
                ·
                  refine ⟨20409184579637183779341461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13606123053091455852894307 20409184579637183779341461)
                  ·
                    refine ⟨956680527170492989656631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20409184579637183779341461 956680527170492989656631)
                    ·
                      rfl

theorem cell22_2794693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 4, 1, 6].length) (baseStart_2794693 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2794693 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2794693 prefixEnd_2794693 := by exact prefixLift 2794693
  have htrace : WordTrace (prefixWord ++ tailWord_2794693) baseStart_2794693 baseEnd_2794693 := by
    simpa [prefixWord, tailWord_2794693, baseEnd_2794693] using wordTrace_append hprefix tailTrace_2794693
  have hstable : (prefixWord ++ tailWord_2794693).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2794693).length < 2 ^ (prefixWord ++ tailWord_2794693).sum := by decide
  have hdescent : baseEnd_2794693 < baseStart_2794693 := by decide
  rcases family_descends (prefixWord ++ tailWord_2794693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2794725 : List Nat := [1, 3, 1, 4, 3, 1, 9]
def baseStart_2794725 : Nat := 118140960795 + 2794725 * 2 ^ 59
def prefixEnd_2794725 : Nat := 4983230072969 + 3 ^ 40 * 2794725 * 2
def baseEnd_2794725 : Nat := 35433017830535391587279

theorem tailTrace_2794725 : CollatzResearch.WordTrace tailWord_2794725 prefixEnd_2794725 35433017830535391587279 := by
  unfold tailWord_2794725
  simp only [CollatzResearch.WordTrace]
  refine ⟨101931994800196100875233629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67954663200130733916822419 101931994800196100875233629)
  ·
    refine ⟨38224498050073537828212611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101931994800196100875233629 38224498050073537828212611)
    ·
      refine ⟨57336747075110306742318917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38224498050073537828212611 57336747075110306742318917)
      ·
        refine ⟨10750640076583182514184797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57336747075110306742318917 10750640076583182514184797)
        ·
          refine ⟨4031490028718693442819299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10750640076583182514184797 4031490028718693442819299)
          ·
            refine ⟨6047235043078040164228949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4031490028718693442819299 6047235043078040164228949)
            ·
              refine ⟨35433017830535391587279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6047235043078040164228949 35433017830535391587279)
              ·
                rfl

theorem cell22_2794725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 9].length) (baseStart_2794725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2794725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2794725 prefixEnd_2794725 := by exact prefixLift 2794725
  have htrace : WordTrace (prefixWord ++ tailWord_2794725) baseStart_2794725 baseEnd_2794725 := by
    simpa [prefixWord, tailWord_2794725, baseEnd_2794725] using wordTrace_append hprefix tailTrace_2794725
  have hstable : (prefixWord ++ tailWord_2794725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2794725).length < 2 ^ (prefixWord ++ tailWord_2794725).sum := by decide
  have hdescent : baseEnd_2794725 < baseStart_2794725 := by decide
  rcases family_descends (prefixWord ++ tailWord_2794725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2794800 : List Nat := [2, 1, 1, 1, 2, 2, 4, 2, 3, 4]
def baseStart_2794800 : Nat := 118140960795 + 2794800 * 2 ^ 59
def prefixEnd_2794800 : Nat := 4983230072969 + 3 ^ 40 * 2794800 * 2
def baseEnd_2794800 : Nat := 956717155457180377231303

theorem tailTrace_2794800 : CollatzResearch.WordTrace tailWord_2794800 prefixEnd_2794800 956717155457180377231303 := by
  unfold tailWord_2794800
  simp only [CollatzResearch.WordTrace]
  refine ⟨50967365137462194342106927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67956486849949592456142569 50967365137462194342106927)
  ·
    refine ⟨76451047706193291513160391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50967365137462194342106927 76451047706193291513160391)
    ·
      refine ⟨114676571559289937269740587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76451047706193291513160391 114676571559289937269740587)
      ·
        refine ⟨172014857338934905904610881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114676571559289937269740587 172014857338934905904610881)
        ·
          refine ⟨129011143004201179428458161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 172014857338934905904610881 129011143004201179428458161)
          ·
            refine ⟨96758357253150884571343621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 129011143004201179428458161 96758357253150884571343621)
            ·
              refine ⟨18142191984965790857126929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 96758357253150884571343621 18142191984965790857126929)
              ·
                refine ⟨13606643988724343142845197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18142191984965790857126929 13606643988724343142845197)
                ·
                  refine ⟨5102491495771628678566949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13606643988724343142845197 5102491495771628678566949)
                  ·
                    refine ⟨956717155457180377231303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5102491495771628678566949 956717155457180377231303)
                    ·
                      rfl

theorem cell22_2794800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 2, 3, 4].length) (baseStart_2794800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2794800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2794800 prefixEnd_2794800 := by exact prefixLift 2794800
  have htrace : WordTrace (prefixWord ++ tailWord_2794800) baseStart_2794800 baseEnd_2794800 := by
    simpa [prefixWord, tailWord_2794800, baseEnd_2794800] using wordTrace_append hprefix tailTrace_2794800
  have hstable : (prefixWord ++ tailWord_2794800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2794800).length < 2 ^ (prefixWord ++ tailWord_2794800).sum := by decide
  have hdescent : baseEnd_2794800 < baseStart_2794800 := by decide
  rcases family_descends (prefixWord ++ tailWord_2794800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2794832 : List Nat := [2, 1, 1, 1, 1, 5, 2, 5, 4]
def baseStart_2794832 : Nat := 118140960795 + 2794832 * 2 ^ 59
def prefixEnd_2794832 : Nat := 4983230072969 + 3 ^ 40 * 2794832 * 2
def baseEnd_2794832 : Nat := 318909369903714320143735

theorem tailTrace_2794832 : CollatzResearch.WordTrace tailWord_2794832 prefixEnd_2794832 318909369903714320143735 := by
  unfold tailWord_2794832
  simp only [CollatzResearch.WordTrace]
  refine ⟨50967948705404229074689375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67957264940538972099585833 50967948705404229074689375)
  ·
    refine ⟨76451923058106343612034063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50967948705404229074689375 76451923058106343612034063)
    ·
      refine ⟨114677884587159515418051095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76451923058106343612034063 114677884587159515418051095)
      ·
        refine ⟨172016826880739273127076643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114677884587159515418051095 172016826880739273127076643)
        ·
          refine ⟨258025240321108909690614965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172016826880739273127076643 258025240321108909690614965)
          ·
            refine ⟨24189866280103960283495153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 258025240321108909690614965 24189866280103960283495153)
            ·
              refine ⟨18142399710077970212621365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24189866280103960283495153 18142399710077970212621365)
              ·
                refine ⟨1700849972819809707433253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18142399710077970212621365 1700849972819809707433253)
                ·
                  refine ⟨318909369903714320143735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1700849972819809707433253 318909369903714320143735)
                  ·
                    rfl

theorem cell22_2794832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 5, 4].length) (baseStart_2794832 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2794832 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2794832 prefixEnd_2794832 := by exact prefixLift 2794832
  have htrace : WordTrace (prefixWord ++ tailWord_2794832) baseStart_2794832 baseEnd_2794832 := by
    simpa [prefixWord, tailWord_2794832, baseEnd_2794832] using wordTrace_append hprefix tailTrace_2794832
  have hstable : (prefixWord ++ tailWord_2794832).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2794832).length < 2 ^ (prefixWord ++ tailWord_2794832).sum := by decide
  have hdescent : baseEnd_2794832 < baseStart_2794832 := by decide
  rcases family_descends (prefixWord ++ tailWord_2794832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2794877 : List Nat := [1, 4, 1, 1, 2, 2, 5, 6]
def baseStart_2794877 : Nat := 118140960795 + 2794877 * 2 ^ 59
def prefixEnd_2794877 : Nat := 4983230072969 + 3 ^ 40 * 2794877 * 2
def baseEnd_2794877 : Nat := 106304834903419760339563

theorem tailTrace_2794877 : CollatzResearch.WordTrace tailWord_2794877 prefixEnd_2794877 106304834903419760339563 := by
  unfold tailWord_2794877
  simp only [CollatzResearch.WordTrace]
  refine ⟨101937538695645430834766885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67958359130430287223177923 101937538695645430834766885)
  ·
    refine ⟨19113288505433518281518791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 101937538695645430834766885 19113288505433518281518791)
    ·
      refine ⟨28669932758150277422278187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19113288505433518281518791 28669932758150277422278187)
      ·
        refine ⟨43004899137225416133417281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28669932758150277422278187 43004899137225416133417281)
        ·
          refine ⟨32253674352919062100062961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43004899137225416133417281 32253674352919062100062961)
          ·
            refine ⟨24190255764689296575047221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32253674352919062100062961 24190255764689296575047221)
            ·
              refine ⟨2267836477939621553910677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24190255764689296575047221 2267836477939621553910677)
              ·
                refine ⟨106304834903419760339563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2267836477939621553910677 106304834903419760339563)
                ·
                  rfl

theorem cell22_2794877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 5, 6].length) (baseStart_2794877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2794877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2794877 prefixEnd_2794877 := by exact prefixLift 2794877
  have htrace : WordTrace (prefixWord ++ tailWord_2794877) baseStart_2794877 baseEnd_2794877 := by
    simpa [prefixWord, tailWord_2794877, baseEnd_2794877] using wordTrace_append hprefix tailTrace_2794877
  have hstable : (prefixWord ++ tailWord_2794877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2794877).length < 2 ^ (prefixWord ++ tailWord_2794877).sum := by decide
  have hdescent : baseEnd_2794877 < baseStart_2794877 := by decide
  rcases family_descends (prefixWord ++ tailWord_2794877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2794892 : List Nat := [2, 2, 1, 2, 1, 3, 1, 2, 5, 3]
def baseStart_2794892 : Nat := 118140960795 + 2794892 * 2 ^ 59
def prefixEnd_2794892 : Nat := 4983230072969 + 3 ^ 40 * 2794892 * 2
def baseEnd_2794892 : Nat := 956748648937322803931021

theorem tailTrace_2794892 : CollatzResearch.WordTrace tailWord_2794892 prefixEnd_2794892 956748648937322803931021 := by
  unfold tailWord_2794892
  simp only [CollatzResearch.WordTrace]
  refine ⟨50969042895295544198281465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67958723860394058931041953 50969042895295544198281465)
  ·
    refine ⟨38226782171471658148711099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50969042895295544198281465 38226782171471658148711099)
    ·
      refine ⟨57340173257207487223066649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38226782171471658148711099 57340173257207487223066649)
      ·
        refine ⟨43005129942905615417299987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57340173257207487223066649 43005129942905615417299987)
        ·
          refine ⟨64507694914358423125949981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43005129942905615417299987 64507694914358423125949981)
          ·
            refine ⟨24190385592884408672231243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64507694914358423125949981 24190385592884408672231243)
            ·
              refine ⟨36285578389326613008346865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24190385592884408672231243 36285578389326613008346865)
              ·
                refine ⟨27214183791994959756260149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36285578389326613008346865 27214183791994959756260149)
                ·
                  refine ⟨2551329730499527477149389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27214183791994959756260149 2551329730499527477149389)
                  ·
                    refine ⟨956748648937322803931021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2551329730499527477149389 956748648937322803931021)
                    ·
                      rfl

theorem cell22_2794892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 2, 5, 3].length) (baseStart_2794892 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2794892 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2794892 prefixEnd_2794892 := by exact prefixLift 2794892
  have htrace : WordTrace (prefixWord ++ tailWord_2794892) baseStart_2794892 baseEnd_2794892 := by
    simpa [prefixWord, tailWord_2794892, baseEnd_2794892] using wordTrace_append hprefix tailTrace_2794892
  have hstable : (prefixWord ++ tailWord_2794892).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2794892).length < 2 ^ (prefixWord ++ tailWord_2794892).sum := by decide
  have hdescent : baseEnd_2794892 < baseStart_2794892 := by decide
  rcases family_descends (prefixWord ++ tailWord_2794892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2794909 : List Nat := [1, 4, 2, 1, 3, 1, 1, 3, 3, 3]
def baseStart_2794909 : Nat := 118140960795 + 2794909 * 2 ^ 59
def prefixEnd_2794909 : Nat := 4983230072969 + 3 ^ 40 * 2794909 * 2
def baseEnd_2794909 : Nat := 956754468384740426255969

theorem tailTrace_2794909 : CollatzResearch.WordTrace tailWord_2794909 prefixEnd_2794909 956754468384740426255969 := by
  unfold tailWord_2794909
  simp only [CollatzResearch.WordTrace]
  refine ⟨101938705831529500299931781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67959137221019666866621187 101938705831529500299931781)
  ·
    refine ⟨19113507343411781306237209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 101938705831529500299931781 19113507343411781306237209)
    ·
      refine ⟨14335130507558835979677907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19113507343411781306237209 14335130507558835979677907)
      ·
        refine ⟨21502695761338253969516861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14335130507558835979677907 21502695761338253969516861)
        ·
          refine ⟨8063510910501845238568823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21502695761338253969516861 8063510910501845238568823)
          ·
            refine ⟨12095266365752767857853235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8063510910501845238568823 12095266365752767857853235)
            ·
              refine ⟨18142899548629151786779853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12095266365752767857853235 18142899548629151786779853)
              ·
                refine ⟨6803587330735931920042445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18142899548629151786779853 6803587330735931920042445)
                ·
                  refine ⟨2551345249025974470015917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6803587330735931920042445 2551345249025974470015917)
                  ·
                    refine ⟨956754468384740426255969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2551345249025974470015917 956754468384740426255969)
                    ·
                      rfl

theorem cell22_2794909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 3, 3, 3].length) (baseStart_2794909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2794909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2794909 prefixEnd_2794909 := by exact prefixLift 2794909
  have htrace : WordTrace (prefixWord ++ tailWord_2794909) baseStart_2794909 baseEnd_2794909 := by
    simpa [prefixWord, tailWord_2794909, baseEnd_2794909] using wordTrace_append hprefix tailTrace_2794909
  have hstable : (prefixWord ++ tailWord_2794909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2794909).length < 2 ^ (prefixWord ++ tailWord_2794909).sum := by decide
  have hdescent : baseEnd_2794909 < baseStart_2794909 := by decide
  rcases family_descends (prefixWord ++ tailWord_2794909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2795012 : List Nat := [2, 3, 2, 3, 12]
def baseStart_2795012 : Nat := 118140960795 + 2795012 * 2 ^ 59
def prefixEnd_2795012 : Nat := 4983230072969 + 3 ^ 40 * 2795012 * 2
def baseEnd_2795012 : Nat := 3937406285554248933871

theorem tailTrace_2795012 : CollatzResearch.WordTrace tailWord_2795012 prefixEnd_2795012 3937406285554248933871 := by
  unfold tailWord_2795012
  simp only [CollatzResearch.WordTrace]
  refine ⟨50971231275078174445465645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67961641700104232593954193 50971231275078174445465645)
  ·
    refine ⟨19114211728154315417049617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50971231275078174445465645 19114211728154315417049617)
    ·
      refine ⟨14335658796115736562787213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19114211728154315417049617 14335658796115736562787213)
      ·
        refine ⟨5375872048543401211045205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14335658796115736562787213 5375872048543401211045205)
        ·
          refine ⟨3937406285554248933871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 5375872048543401211045205 3937406285554248933871)
          ·
            rfl

theorem cell22_2795012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 12].length) (baseStart_2795012 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2795012 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2795012 prefixEnd_2795012 := by exact prefixLift 2795012
  have htrace : WordTrace (prefixWord ++ tailWord_2795012) baseStart_2795012 baseEnd_2795012 := by
    simpa [prefixWord, tailWord_2795012, baseEnd_2795012] using wordTrace_append hprefix tailTrace_2795012
  have hstable : (prefixWord ++ tailWord_2795012).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2795012).length < 2 ^ (prefixWord ++ tailWord_2795012).sum := by decide
  have hdescent : baseEnd_2795012 < baseStart_2795012 := by decide
  rcases family_descends (prefixWord ++ tailWord_2795012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2795018 : List Nat := [3, 1, 2, 2, 2, 4, 2, 2, 4]
def baseStart_2795018 : Nat := 118140960795 + 2795018 * 2 ^ 59
def prefixEnd_2795018 : Nat := 4983230072969 + 3 ^ 40 * 2795018 * 2
def baseEnd_2795018 : Nat := 318930593770766825093545

theorem tailTrace_2795018 : CollatzResearch.WordTrace tailWord_2795018 prefixEnd_2795018 318930593770766825093545 := by
  unfold tailWord_2795018
  simp only [CollatzResearch.WordTrace]
  refine ⟨25485670347033652978912427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67961787592089741277099805 25485670347033652978912427)
  ·
    refine ⟨38228505520550479468368641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25485670347033652978912427 38228505520550479468368641)
    ·
      refine ⟨28671379140412859601276481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38228505520550479468368641 28671379140412859601276481)
      ·
        refine ⟨21503534355309644700957361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28671379140412859601276481 21503534355309644700957361)
        ·
          refine ⟨16127650766482233525718021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21503534355309644700957361 16127650766482233525718021)
          ·
            refine ⟨3023934518715418786072129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16127650766482233525718021 3023934518715418786072129)
            ·
              refine ⟨2267950889036564089554097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3023934518715418786072129 2267950889036564089554097)
              ·
                refine ⟨1700963166777423067165573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2267950889036564089554097 1700963166777423067165573)
                ·
                  refine ⟨318930593770766825093545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1700963166777423067165573 318930593770766825093545)
                  ·
                    rfl

theorem cell22_2795018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 2, 2, 4].length) (baseStart_2795018 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2795018 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2795018 prefixEnd_2795018 := by exact prefixLift 2795018
  have htrace : WordTrace (prefixWord ++ tailWord_2795018) baseStart_2795018 baseEnd_2795018 := by
    simpa [prefixWord, tailWord_2795018, baseEnd_2795018] using wordTrace_append hprefix tailTrace_2795018
  have hstable : (prefixWord ++ tailWord_2795018).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2795018).length < 2 ^ (prefixWord ++ tailWord_2795018).sum := by decide
  have hdescent : baseEnd_2795018 < baseStart_2795018 := by decide
  rcases family_descends (prefixWord ++ tailWord_2795018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2795029 : List Nat := [1, 3, 2, 1, 3, 4, 1, 7]
def baseStart_2795029 : Nat := 118140960795 + 2795029 * 2 ^ 59
def prefixEnd_2795029 : Nat := 4983230072969 + 3 ^ 40 * 2795029 * 2
def baseEnd_2795029 : Nat := 106310616315233345917289

theorem tailTrace_2795029 : CollatzResearch.WordTrace tailWord_2795029 prefixEnd_2795029 106310616315233345917289 := by
  unfold tailWord_2795029
  simp only [CollatzResearch.WordTrace]
  refine ⟨101943082591094760794300141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67962055060729840529533427 101943082591094760794300141)
  ·
    refine ⟨38228655971660535297862553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101943082591094760794300141 38228655971660535297862553)
    ·
      refine ⟨28671491978745401473396915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38228655971660535297862553 28671491978745401473396915)
      ·
        refine ⟨43007237968118102210095373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28671491978745401473396915 43007237968118102210095373)
        ·
          refine ⟨16127714238044288328785765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43007237968118102210095373 16127714238044288328785765)
          ·
            refine ⟨3023946419633304061647331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16127714238044288328785765 3023946419633304061647331)
            ·
              refine ⟨4535919629449956092470997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3023946419633304061647331 4535919629449956092470997)
              ·
                refine ⟨106310616315233345917289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4535919629449956092470997 106310616315233345917289)
                ·
                  rfl

theorem cell22_2795029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 1, 7].length) (baseStart_2795029 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2795029 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2795029 prefixEnd_2795029 := by exact prefixLift 2795029
  have htrace : WordTrace (prefixWord ++ tailWord_2795029) baseStart_2795029 baseEnd_2795029 := by
    simpa [prefixWord, tailWord_2795029, baseEnd_2795029] using wordTrace_append hprefix tailTrace_2795029
  have hstable : (prefixWord ++ tailWord_2795029).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2795029).length < 2 ^ (prefixWord ++ tailWord_2795029).sum := by decide
  have hdescent : baseEnd_2795029 < baseStart_2795029 := by decide
  rcases family_descends (prefixWord ++ tailWord_2795029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2795048 : List Nat := [2, 1, 5, 2, 2, 2, 1, 1, 2, 4]
def baseStart_2795048 : Nat := 118140960795 + 2795048 * 2 ^ 59
def prefixEnd_2795048 : Nat := 4983230072969 + 3 ^ 40 * 2795048 * 2
def baseEnd_2795048 : Nat := 956802050925390397030543

theorem tailTrace_2795048 : CollatzResearch.WordTrace tailWord_2795048 prefixEnd_2795048 956802050925390397030543 := by
  unfold tailWord_2795048
  simp only [CollatzResearch.WordTrace]
  refine ⟨50971887789012963519620899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67962517052017284692827865 50971887789012963519620899)
  ·
    refine ⟨76457831683519445279431349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50971887789012963519620899 76457831683519445279431349)
    ·
      refine ⟨7167921720329947994946689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 76457831683519445279431349 7167921720329947994946689)
      ·
        refine ⟨5375941290247460996210017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7167921720329947994946689 5375941290247460996210017)
        ·
          refine ⟨4031955967685595747157513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5375941290247460996210017 4031955967685595747157513)
          ·
            refine ⟨3023966975764196810368135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4031955967685595747157513 3023966975764196810368135)
            ·
              refine ⟨4535950463646295215552203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3023966975764196810368135 4535950463646295215552203)
              ·
                refine ⟨6803925695469442823328305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4535950463646295215552203 6803925695469442823328305)
                ·
                  refine ⟨5102944271602082117496229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6803925695469442823328305 5102944271602082117496229)
                  ·
                    refine ⟨956802050925390397030543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5102944271602082117496229 956802050925390397030543)
                    ·
                      rfl

theorem cell22_2795048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 1, 1, 2, 4].length) (baseStart_2795048 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2795048 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2795048 prefixEnd_2795048 := by exact prefixLift 2795048
  have htrace : WordTrace (prefixWord ++ tailWord_2795048) baseStart_2795048 baseEnd_2795048 := by
    simpa [prefixWord, tailWord_2795048, baseEnd_2795048] using wordTrace_append hprefix tailTrace_2795048
  have hstable : (prefixWord ++ tailWord_2795048).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2795048).length < 2 ^ (prefixWord ++ tailWord_2795048).sum := by decide
  have hdescent : baseEnd_2795048 < baseStart_2795048 := by decide
  rcases family_descends (prefixWord ++ tailWord_2795048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2795057 : List Nat := [1, 2, 2, 3, 1, 1, 1, 4, 7]
def baseStart_2795057 : Nat := 118140960795 + 2795057 * 2 ^ 59
def prefixEnd_2795057 : Nat := 4983230072969 + 3 ^ 40 * 2795057 * 2
def baseEnd_2795057 : Nat := 318935043936439124518505

theorem tailTrace_2795057 : CollatzResearch.WordTrace tailWord_2795057 prefixEnd_2795057 318935043936439124518505 := by
  unfold tailWord_2795057
  simp only [CollatzResearch.WordTrace]
  refine ⟨101944103834993321576319425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67962735889995547717546283 101944103834993321576319425)
  ·
    refine ⟨76458077876244991182239569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101944103834993321576319425 76458077876244991182239569)
    ·
      refine ⟨57343558407183743386679677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76458077876244991182239569 57343558407183743386679677)
      ·
        refine ⟨21503834402693903770004879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57343558407183743386679677 21503834402693903770004879)
        ·
          refine ⟨32255751604040855655007319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21503834402693903770004879 32255751604040855655007319)
          ·
            refine ⟨48383627406061283482510979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32255751604040855655007319 48383627406061283482510979)
            ·
              refine ⟨72575441109091925223766469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48383627406061283482510979 72575441109091925223766469)
              ·
                refine ⟨13607895207954735979456213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 72575441109091925223766469 13607895207954735979456213)
                ·
                  refine ⟨318935043936439124518505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13607895207954735979456213 318935043936439124518505)
                  ·
                    rfl

theorem cell22_2795057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 4, 7].length) (baseStart_2795057 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2795057 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2795057 prefixEnd_2795057 := by exact prefixLift 2795057
  have htrace : WordTrace (prefixWord ++ tailWord_2795057) baseStart_2795057 baseEnd_2795057 := by
    simpa [prefixWord, tailWord_2795057, baseEnd_2795057] using wordTrace_append hprefix tailTrace_2795057
  have hstable : (prefixWord ++ tailWord_2795057).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2795057).length < 2 ^ (prefixWord ++ tailWord_2795057).sum := by decide
  have hdescent : baseEnd_2795057 < baseStart_2795057 := by decide
  rcases family_descends (prefixWord ++ tailWord_2795057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2795194 : List Nat := [3, 1, 1, 1, 2, 4, 1, 1, 2, 6]
def baseStart_2795194 : Nat := 118140960795 + 2795194 * 2 ^ 59
def prefixEnd_2795194 : Nat := 4983230072969 + 3 ^ 40 * 2795194 * 2
def baseEnd_2795194 : Nat := 956852029709094682880095

theorem tailTrace_2795194 : CollatzResearch.WordTrace tailWord_2795194 prefixEnd_2795194 956852029709094682880095 := by
  unfold tailWord_2795194
  simp only [CollatzResearch.WordTrace]
  refine ⟨25487275158874248493514159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67966067090331329316037757 25487275158874248493514159)
  ·
    refine ⟨38230912738311372740271239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25487275158874248493514159 38230912738311372740271239)
    ·
      refine ⟨57346369107467059110406859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38230912738311372740271239 57346369107467059110406859)
      ·
        refine ⟨86019553661200588665610289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57346369107467059110406859 86019553661200588665610289)
        ·
          refine ⟨64514665245900441499207717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86019553661200588665610289 64514665245900441499207717)
          ·
            refine ⟨12096499733606332781101447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64514665245900441499207717 12096499733606332781101447)
            ·
              refine ⟨18144749600409499171652171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12096499733606332781101447 18144749600409499171652171)
              ·
                refine ⟨27217124400614248757478257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18144749600409499171652171 27217124400614248757478257)
                ·
                  refine ⟨20412843300460686568108693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27217124400614248757478257 20412843300460686568108693)
                  ·
                    refine ⟨956852029709094682880095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20412843300460686568108693 956852029709094682880095)
                    ·
                      rfl

theorem cell22_2795194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 1, 2, 6].length) (baseStart_2795194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2795194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2795194 prefixEnd_2795194 := by exact prefixLift 2795194
  have htrace : WordTrace (prefixWord ++ tailWord_2795194) baseStart_2795194 baseEnd_2795194 := by
    simpa [prefixWord, tailWord_2795194, baseEnd_2795194] using wordTrace_append hprefix tailTrace_2795194
  have hstable : (prefixWord ++ tailWord_2795194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2795194).length < 2 ^ (prefixWord ++ tailWord_2795194).sum := by decide
  have hdescent : baseEnd_2795194 < baseStart_2795194 := by decide
  rcases family_descends (prefixWord ++ tailWord_2795194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2795202 : List Nat := [3, 5, 1, 2, 1, 1, 2, 1, 1, 5]
def baseStart_2795202 : Nat := 118140960795 + 2795202 * 2 ^ 59
def prefixEnd_2795202 : Nat := 4983230072969 + 3 ^ 40 * 2795202 * 2
def baseEnd_2795202 : Nat := 956854768272585328680071

theorem tailTrace_2795202 : CollatzResearch.WordTrace tailWord_2795202 prefixEnd_2795202 956854768272585328680071 := by
  unfold tailWord_2795202
  simp only [CollatzResearch.WordTrace]
  refine ⟨25487348104867002835086965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67966261612978674226898573 25487348104867002835086965)
  ·
    refine ⟨2389438884831281515789403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 25487348104867002835086965 2389438884831281515789403)
    ·
      refine ⟨3584158327246922273684105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2389438884831281515789403 3584158327246922273684105)
      ·
        refine ⟨2688118745435191705263079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3584158327246922273684105 2688118745435191705263079)
        ·
          refine ⟨4032178118152787557894619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2688118745435191705263079 4032178118152787557894619)
          ·
            refine ⟨6048267177229181336841929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4032178118152787557894619 6048267177229181336841929)
            ·
              refine ⟨4536200382921886002631447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6048267177229181336841929 4536200382921886002631447)
              ·
                refine ⟨6804300574382829003947171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4536200382921886002631447 6804300574382829003947171)
                ·
                  refine ⟨10206450861574243505920757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6804300574382829003947171 10206450861574243505920757)
                  ·
                    refine ⟨956854768272585328680071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10206450861574243505920757 956854768272585328680071)
                    ·
                      rfl

theorem cell22_2795202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 2, 1, 1, 5].length) (baseStart_2795202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2795202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2795202 prefixEnd_2795202 := by exact prefixLift 2795202
  have htrace : WordTrace (prefixWord ++ tailWord_2795202) baseStart_2795202 baseEnd_2795202 := by
    simpa [prefixWord, tailWord_2795202, baseEnd_2795202] using wordTrace_append hprefix tailTrace_2795202
  have hstable : (prefixWord ++ tailWord_2795202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2795202).length < 2 ^ (prefixWord ++ tailWord_2795202).sum := by decide
  have hdescent : baseEnd_2795202 < baseStart_2795202 := by decide
  rcases family_descends (prefixWord ++ tailWord_2795202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2795224 : List Nat := [2, 1, 2, 2, 3, 1, 1, 2, 1, 7]
def baseStart_2795224 : Nat := 118140960795 + 2795224 * 2 ^ 59
def prefixEnd_2795224 : Nat := 4983230072969 + 3 ^ 40 * 2795224 * 2
def baseEnd_2795224 : Nat := 956862299322184604630003

theorem tailTrace_2795224 : CollatzResearch.WordTrace tailWord_2795224 prefixEnd_2795224 956862299322184604630003 := by
  unfold tailWord_2795224
  simp only [CollatzResearch.WordTrace]
  refine ⟨50975097412694154548824363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67966796550258872731765817 50975097412694154548824363)
  ·
    refine ⟨76462646119041231823236545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50975097412694154548824363 76462646119041231823236545)
    ·
      refine ⟨57346984589280923867427409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76462646119041231823236545 57346984589280923867427409)
      ·
        refine ⟨43010238441960692900570557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57346984589280923867427409 43010238441960692900570557)
        ·
          refine ⟨16128839415735259837713959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43010238441960692900570557 16128839415735259837713959)
          ·
            refine ⟨24193259123602889756570939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16128839415735259837713959 24193259123602889756570939)
            ·
              refine ⟨36289888685404334634856409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24193259123602889756570939 36289888685404334634856409)
              ·
                refine ⟨27217416514053250976142307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36289888685404334634856409 27217416514053250976142307)
                ·
                  refine ⟨40826124771079876464213461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27217416514053250976142307 40826124771079876464213461)
                  ·
                    refine ⟨956862299322184604630003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40826124771079876464213461 956862299322184604630003)
                    ·
                      rfl

theorem cell22_2795224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 2, 1, 7].length) (baseStart_2795224 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2795224 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2795224 prefixEnd_2795224 := by exact prefixLift 2795224
  have htrace : WordTrace (prefixWord ++ tailWord_2795224) baseStart_2795224 baseEnd_2795224 := by
    simpa [prefixWord, tailWord_2795224, baseEnd_2795224] using wordTrace_append hprefix tailTrace_2795224
  have hstable : (prefixWord ++ tailWord_2795224).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2795224).length < 2 ^ (prefixWord ++ tailWord_2795224).sum := by decide
  have hdescent : baseEnd_2795224 < baseStart_2795224 := by decide
  rcases family_descends (prefixWord ++ tailWord_2795224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2795288 : List Nat := [2, 1, 2, 3, 1, 1, 5, 3, 4]
def baseStart_2795288 : Nat := 118140960795 + 2795288 * 2 ^ 59
def prefixEnd_2795288 : Nat := 4983230072969 + 3 ^ 40 * 2795288 * 2
def baseEnd_2795288 : Nat := 318961402610036590343269

theorem tailTrace_2795288 : CollatzResearch.WordTrace tailWord_2795288 prefixEnd_2795288 318961402610036590343269 := by
  unfold tailWord_2795288
  simp only [CollatzResearch.WordTrace]
  refine ⟨50976264548578224013989259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67968352731437632018652345 50976264548578224013989259)
  ·
    refine ⟨76464396822867336020983889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50976264548578224013989259 76464396822867336020983889)
    ·
      refine ⟨57348297617150502015737917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76464396822867336020983889 57348297617150502015737917)
      ·
        refine ⟨21505611606431438255901719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57348297617150502015737917 21505611606431438255901719)
        ·
          refine ⟨32258417409647157383852579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21505611606431438255901719 32258417409647157383852579)
          ·
            refine ⟨48387626114470736075778869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32258417409647157383852579 48387626114470736075778869)
            ·
              refine ⟨4536339948231631507104269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 48387626114470736075778869 4536339948231631507104269)
              ·
                refine ⟨1701127480586861815164101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4536339948231631507104269 1701127480586861815164101)
                ·
                  refine ⟨318961402610036590343269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1701127480586861815164101 318961402610036590343269)
                  ·
                    rfl

theorem cell22_2795288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 5, 3, 4].length) (baseStart_2795288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2795288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2795288 prefixEnd_2795288 := by exact prefixLift 2795288
  have htrace : WordTrace (prefixWord ++ tailWord_2795288) baseStart_2795288 baseEnd_2795288 := by
    simpa [prefixWord, tailWord_2795288, baseEnd_2795288] using wordTrace_append hprefix tailTrace_2795288
  have hstable : (prefixWord ++ tailWord_2795288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2795288).length < 2 ^ (prefixWord ++ tailWord_2795288).sum := by decide
  have hdescent : baseEnd_2795288 < baseStart_2795288 := by decide
  rcases family_descends (prefixWord ++ tailWord_2795288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2795299 : List Nat := [1, 1, 1, 4, 2, 1, 12]
def baseStart_2795299 : Nat := 118140960795 + 2795299 * 2 ^ 59
def prefixEnd_2795299 : Nat := 4983230072969 + 3 ^ 40 * 2795299 * 2
def baseEnd_2795299 : Nat := 35440295309441089222399

theorem tailTrace_2795299 : CollatzResearch.WordTrace tailWord_2795299 prefixEnd_2795299 35440295309441089222399 := by
  unfold tailWord_2795299
  simp only [CollatzResearch.WordTrace]
  refine ⟨101952930300116596906628951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67968620200077731271085967 101952930300116596906628951)
  ·
    refine ⟨152929395450174895359943427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101952930300116596906628951 152929395450174895359943427)
    ·
      refine ⟨229394093175262343039915141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152929395450174895359943427 229394093175262343039915141)
      ·
        refine ⟨43011392470361689319984089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 229394093175262343039915141 43011392470361689319984089)
        ·
          refine ⟨32258544352771266989988067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43011392470361689319984089 32258544352771266989988067)
          ·
            refine ⟨48387816529156900484982101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32258544352771266989988067 48387816529156900484982101)
            ·
              refine ⟨35440295309441089222399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 48387816529156900484982101 35440295309441089222399)
              ·
                rfl

theorem cell22_2795299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 12].length) (baseStart_2795299 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2795299 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2795299 prefixEnd_2795299 := by exact prefixLift 2795299
  have htrace : WordTrace (prefixWord ++ tailWord_2795299) baseStart_2795299 baseEnd_2795299 := by
    simpa [prefixWord, tailWord_2795299, baseEnd_2795299] using wordTrace_append hprefix tailTrace_2795299
  have hstable : (prefixWord ++ tailWord_2795299).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2795299).length < 2 ^ (prefixWord ++ tailWord_2795299).sum := by decide
  have hdescent : baseEnd_2795299 < baseStart_2795299 := by decide
  rcases family_descends (prefixWord ++ tailWord_2795299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2795301 : List Nat := [1, 3, 1, 2, 3, 2, 1, 1, 4, 4]
def baseStart_2795301 : Nat := 118140960795 + 2795301 * 2 ^ 59
def prefixEnd_2795301 : Nat := 4983230072969 + 3 ^ 40 * 2795301 * 2
def baseEnd_2795301 : Nat := 956888657995782070454767

theorem tailTrace_2795301 : CollatzResearch.WordTrace tailWord_2795301 prefixEnd_2795301 956888657995782070454767 := by
  unfold tailWord_2795301
  simp only [CollatzResearch.WordTrace]
  refine ⟨101953003246109351248201757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67968668830739567498801171 101953003246109351248201757)
  ·
    refine ⟨38232376217291006718075659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101953003246109351248201757 38232376217291006718075659)
    ·
      refine ⟨57348564325936510077113489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38232376217291006718075659 57348564325936510077113489)
      ·
        refine ⟨43011423244452382557835117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57348564325936510077113489 43011423244452382557835117)
        ·
          refine ⟨16129283716669643459188169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43011423244452382557835117 16129283716669643459188169)
          ·
            refine ⟨12096962787502232594391127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16129283716669643459188169 12096962787502232594391127)
            ·
              refine ⟨18145444181253348891586691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12096962787502232594391127 18145444181253348891586691)
              ·
                refine ⟨27218166271880023337380037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18145444181253348891586691 27218166271880023337380037)
                ·
                  refine ⟨5103406175977504375758757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27218166271880023337380037 5103406175977504375758757)
                  ·
                    refine ⟨956888657995782070454767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5103406175977504375758757 956888657995782070454767)
                    ·
                      rfl

theorem cell22_2795301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 1, 4, 4].length) (baseStart_2795301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2795301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2795301 prefixEnd_2795301 := by exact prefixLift 2795301
  have htrace : WordTrace (prefixWord ++ tailWord_2795301) baseStart_2795301 baseEnd_2795301 := by
    simpa [prefixWord, tailWord_2795301, baseEnd_2795301] using wordTrace_append hprefix tailTrace_2795301
  have hstable : (prefixWord ++ tailWord_2795301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2795301).length < 2 ^ (prefixWord ++ tailWord_2795301).sum := by decide
  have hdescent : baseEnd_2795301 < baseStart_2795301 := by decide
  rcases family_descends (prefixWord ++ tailWord_2795301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2795320 : List Nat := [2, 1, 2, 1, 3, 3, 4, 1, 2, 3]
def baseStart_2795320 : Nat := 118140960795 + 2795320 * 2 ^ 59
def prefixEnd_2795320 : Nat := 4983230072969 + 3 ^ 40 * 2795320 * 2
def baseEnd_2795320 : Nat := 956895162084072354229709

theorem tailTrace_2795320 : CollatzResearch.WordTrace tailWord_2795320 prefixEnd_2795320 956895162084072354229709 := by
  unfold tailWord_2795320
  simp only [CollatzResearch.WordTrace]
  refine ⟨50976848116520258746571707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67969130822027011662095609 50976848116520258746571707)
  ·
    refine ⟨76465272174780388119857561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50976848116520258746571707 76465272174780388119857561)
    ·
      refine ⟨57348954131085291089893171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76465272174780388119857561 57348954131085291089893171)
      ·
        refine ⟨86023431196627936634839757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57348954131085291089893171 86023431196627936634839757)
        ·
          refine ⟨32258786698735476238064909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86023431196627936634839757 32258786698735476238064909)
          ·
            refine ⟨12097045012025803589274341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32258786698735476238064909 12097045012025803589274341)
            ·
              refine ⟨2268195939754838172988939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12097045012025803589274341 2268195939754838172988939)
              ·
                refine ⟨3402293909632257259483409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2268195939754838172988939 3402293909632257259483409)
                ·
                  refine ⟨2551720432224192944612557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3402293909632257259483409 2551720432224192944612557)
                  ·
                    refine ⟨956895162084072354229709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2551720432224192944612557 956895162084072354229709)
                    ·
                      rfl

theorem cell22_2795320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 4, 1, 2, 3].length) (baseStart_2795320 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2795320 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2795320 prefixEnd_2795320 := by exact prefixLift 2795320
  have htrace : WordTrace (prefixWord ++ tailWord_2795320) baseStart_2795320 baseEnd_2795320 := by
    simpa [prefixWord, tailWord_2795320, baseEnd_2795320] using wordTrace_append hprefix tailTrace_2795320
  have hstable : (prefixWord ++ tailWord_2795320).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2795320).length < 2 ^ (prefixWord ++ tailWord_2795320).sum := by decide
  have hdescent : baseEnd_2795320 < baseStart_2795320 := by decide
  rcases family_descends (prefixWord ++ tailWord_2795320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2795382 : List Nat := [5, 1, 1, 3, 2, 1, 1, 2, 3, 3]
def baseStart_2795382 : Nat := 118140960795 + 2795382 * 2 ^ 59
def prefixEnd_2795382 : Nat := 4983230072969 + 3 ^ 40 * 2795382 * 2
def baseEnd_2795382 : Nat := 956916385951124859179519

theorem tailTrace_2795382 : CollatzResearch.WordTrace tailWord_2795382 prefixEnd_2795382 956916385951124859179519 := by
  unfold tailWord_2795382
  simp only [CollatzResearch.WordTrace]
  refine ⟨6372247347425993880118775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 67970638372543934721266933 6372247347425993880118775)
  ·
    refine ⟨9558371021138990820178163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6372247347425993880118775 9558371021138990820178163)
    ·
      refine ⟨14337556531708486230267245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9558371021138990820178163 14337556531708486230267245)
      ·
        refine ⟨5376583699390682336350217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14337556531708486230267245 5376583699390682336350217)
        ·
          refine ⟨4032437774543011752262663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5376583699390682336350217 4032437774543011752262663)
          ·
            refine ⟨6048656661814517628393995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4032437774543011752262663 6048656661814517628393995)
            ·
              refine ⟨9072984992721776442590993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6048656661814517628393995 9072984992721776442590993)
              ·
                refine ⟨6804738744541332331943245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9072984992721776442590993 6804738744541332331943245)
                ·
                  refine ⟨2551777029202999624478717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6804738744541332331943245 2551777029202999624478717)
                  ·
                    refine ⟨956916385951124859179519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2551777029202999624478717 956916385951124859179519)
                    ·
                      rfl

theorem cell22_2795382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 2, 3, 3].length) (baseStart_2795382 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2795382 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2795382 prefixEnd_2795382 := by exact prefixLift 2795382
  have htrace : WordTrace (prefixWord ++ tailWord_2795382) baseStart_2795382 baseEnd_2795382 := by
    simpa [prefixWord, tailWord_2795382, baseEnd_2795382] using wordTrace_append hprefix tailTrace_2795382
  have hstable : (prefixWord ++ tailWord_2795382).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2795382).length < 2 ^ (prefixWord ++ tailWord_2795382).sum := by decide
  have hdescent : baseEnd_2795382 < baseStart_2795382 := by decide
  rcases family_descends (prefixWord ++ tailWord_2795382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2795453 : List Nat := [1, 4, 1, 2, 3, 1, 2, 1, 1, 6]
def baseStart_2795453 : Nat := 118140960795 + 2795453 * 2 ^ 59
def prefixEnd_2795453 : Nat := 4983230072969 + 3 ^ 40 * 2795453 * 2
def baseEnd_2795453 : Nat := 956940690702104340654301

theorem tailTrace_2795453 : CollatzResearch.WordTrace tailWord_2795453 prefixEnd_2795453 956940690702104340654301 := by
  unfold tailWord_2795453
  simp only [CollatzResearch.WordTrace]
  refine ⟨101958547141558681207735013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67972364761039120805156675 101958547141558681207735013)
  ·
    refine ⟨19117227589042252726450315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 101958547141558681207735013 19117227589042252726450315)
    ·
      refine ⟨28675841383563379089675473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19117227589042252726450315 28675841383563379089675473)
      ·
        refine ⟨21506881037672534317256605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28675841383563379089675473 21506881037672534317256605)
        ·
          refine ⟨8065080389127200368971227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21506881037672534317256605 8065080389127200368971227)
          ·
            refine ⟨12097620583690800553456841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8065080389127200368971227 12097620583690800553456841)
            ·
              refine ⟨9073215437768100415092631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12097620583690800553456841 9073215437768100415092631)
              ·
                refine ⟨13609823156652150622638947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9073215437768100415092631 13609823156652150622638947)
                ·
                  refine ⟨20414734734978225933958421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13609823156652150622638947 20414734734978225933958421)
                  ·
                    refine ⟨956940690702104340654301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20414734734978225933958421 956940690702104340654301)
                    ·
                      rfl

theorem cell22_2795453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 1, 1, 6].length) (baseStart_2795453 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2795453 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2795453 prefixEnd_2795453 := by exact prefixLift 2795453
  have htrace : WordTrace (prefixWord ++ tailWord_2795453) baseStart_2795453 baseEnd_2795453 := by
    simpa [prefixWord, tailWord_2795453, baseEnd_2795453] using wordTrace_append hprefix tailTrace_2795453
  have hstable : (prefixWord ++ tailWord_2795453).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2795453).length < 2 ^ (prefixWord ++ tailWord_2795453).sum := by decide
  have hdescent : baseEnd_2795453 < baseStart_2795453 := by decide
  rcases family_descends (prefixWord ++ tailWord_2795453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2795468 : List Nat := [2, 2, 1, 4, 1, 4, 8]
def baseStart_2795468 : Nat := 118140960795 + 2795468 * 2 ^ 59
def prefixEnd_2795468 : Nat := 4983230072969 + 3 ^ 40 * 2795468 * 2
def baseEnd_2795468 : Nat := 35442437981801825982565

theorem tailTrace_2795468 : CollatzResearch.WordTrace tailWord_2795468 prefixEnd_2795468 35442437981801825982565 := by
  unfold tailWord_2795468
  simp only [CollatzResearch.WordTrace]
  refine ⟨50979547118252169384765529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67972729491002892513020705 50979547118252169384765529)
  ·
    refine ⟨38234660338689127038574147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50979547118252169384765529 38234660338689127038574147)
    ·
      refine ⟨57351990508033690557861221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38234660338689127038574147 57351990508033690557861221)
      ·
        refine ⟨10753498220256316979598979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57351990508033690557861221 10753498220256316979598979)
        ·
          refine ⟨16130247330384475469398469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10753498220256316979598979 16130247330384475469398469)
          ·
            refine ⟨3024421374447089150512213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16130247330384475469398469 3024421374447089150512213)
            ·
              refine ⟨35442437981801825982565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3024421374447089150512213 35442437981801825982565)
              ·
                rfl

theorem cell22_2795468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 8].length) (baseStart_2795468 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2795468 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2795468 prefixEnd_2795468 := by exact prefixLift 2795468
  have htrace : WordTrace (prefixWord ++ tailWord_2795468) baseStart_2795468 baseEnd_2795468 := by
    simpa [prefixWord, tailWord_2795468, baseEnd_2795468] using wordTrace_append hprefix tailTrace_2795468
  have hstable : (prefixWord ++ tailWord_2795468).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2795468).length < 2 ^ (prefixWord ++ tailWord_2795468).sum := by decide
  have hdescent : baseEnd_2795468 < baseStart_2795468 := by decide
  rcases family_descends (prefixWord ++ tailWord_2795468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2795474 : List Nat := [3, 2, 2, 3, 2, 1, 3, 2, 4]
def baseStart_2795474 : Nat := 118140960795 + 2795474 * 2 ^ 59
def prefixEnd_2795474 : Nat := 4983230072969 + 3 ^ 40 * 2795474 * 2
def baseEnd_2795474 : Nat := 318982626477089095293079

theorem tailTrace_2795474 : CollatzResearch.WordTrace tailWord_2795474 prefixEnd_2795474 318982626477089095293079 := by
  unfold tailWord_2795474
  simp only [CollatzResearch.WordTrace]
  refine ⟨25489828268620650448562369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67972875382988401196166317 25489828268620650448562369)
  ·
    refine ⟨19117371201465487836421777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25489828268620650448562369 19117371201465487836421777)
    ·
      refine ⟨14338028401099115877316333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19117371201465487836421777 14338028401099115877316333)
      ·
        refine ⟨5376760650412168453993625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14338028401099115877316333 5376760650412168453993625)
        ·
          refine ⟨4032570487809126340495219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5376760650412168453993625 4032570487809126340495219)
          ·
            refine ⟨6048855731713689510742829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4032570487809126340495219 6048855731713689510742829)
            ·
              refine ⟨2268320899392633566528561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6048855731713689510742829 2268320899392633566528561)
              ·
                refine ⟨1701240674544475174896421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2268320899392633566528561 1701240674544475174896421)
                ·
                  refine ⟨318982626477089095293079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1701240674544475174896421 318982626477089095293079)
                  ·
                    rfl

theorem cell22_2795474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 3, 2, 4].length) (baseStart_2795474 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2795474 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2795474 prefixEnd_2795474 := by exact prefixLift 2795474
  have htrace : WordTrace (prefixWord ++ tailWord_2795474) baseStart_2795474 baseEnd_2795474 := by
    simpa [prefixWord, tailWord_2795474, baseEnd_2795474] using wordTrace_append hprefix tailTrace_2795474
  have hstable : (prefixWord ++ tailWord_2795474).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2795474).length < 2 ^ (prefixWord ++ tailWord_2795474).sum := by decide
  have hdescent : baseEnd_2795474 < baseStart_2795474 := by decide
  rcases family_descends (prefixWord ++ tailWord_2795474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2795485 : List Nat := [1, 4, 3, 1, 3, 1, 2, 7]
def baseStart_2795485 : Nat := 118140960795 + 2795485 * 2 ^ 59
def prefixEnd_2795485 : Nat := 4983230072969 + 3 ^ 40 * 2795485 * 2
def baseEnd_2795485 : Nat := 106327960550674102650467

theorem tailTrace_2795485 : CollatzResearch.WordTrace tailWord_2795485 prefixEnd_2795485 106327960550674102650467 := by
  unfold tailWord_2795485
  simp only [CollatzResearch.WordTrace]
  refine ⟨101959714277442750672899909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67973142851628500448599939 101959714277442750672899909)
  ·
    refine ⟨19117446427020515751168733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 101959714277442750672899909 19117446427020515751168733)
    ·
      refine ⟨7169042410132693406688275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19117446427020515751168733 7169042410132693406688275)
      ·
        refine ⟨10753563615199040110032413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7169042410132693406688275 10753563615199040110032413)
        ·
          refine ⟨4032586355699640041262155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10753563615199040110032413 4032586355699640041262155)
          ·
            refine ⟨6048879533549460061893233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4032586355699640041262155 6048879533549460061893233)
            ·
              refine ⟨4536659650162095046419925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6048879533549460061893233 4536659650162095046419925)
              ·
                refine ⟨106327960550674102650467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4536659650162095046419925 106327960550674102650467)
                ·
                  rfl

theorem cell22_2795485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 2, 7].length) (baseStart_2795485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2795485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2795485 prefixEnd_2795485 := by exact prefixLift 2795485
  have htrace : WordTrace (prefixWord ++ tailWord_2795485) baseStart_2795485 baseEnd_2795485 := by
    simpa [prefixWord, tailWord_2795485, baseEnd_2795485] using wordTrace_append hprefix tailTrace_2795485
  have hstable : (prefixWord ++ tailWord_2795485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2795485).length < 2 ^ (prefixWord ++ tailWord_2795485).sum := by decide
  have hdescent : baseEnd_2795485 < baseStart_2795485 := by decide
  rcases family_descends (prefixWord ++ tailWord_2795485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2795528 : List Nat := [2, 1, 3, 2, 1, 2, 2, 2, 2, 5]
def baseStart_2795528 : Nat := 118140960795 + 2795528 * 2 ^ 59
def prefixEnd_2795528 : Nat := 4983230072969 + 3 ^ 40 * 2795528 * 2
def baseEnd_2795528 : Nat := 956966364734829145029071

theorem tailTrace_2795528 : CollatzResearch.WordTrace tailWord_2795528 prefixEnd_2795528 956966364734829145029071 := by
  unfold tailWord_2795528
  simp only [CollatzResearch.WordTrace]
  refine ⟨50980641308143484508357619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67974188410857979344476825 50980641308143484508357619)
  ·
    refine ⟨76470961962215226762536429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50980641308143484508357619 76470961962215226762536429)
    ·
      refine ⟨28676610735830710035951161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76470961962215226762536429 28676610735830710035951161)
      ·
        refine ⟨21507458051873032526963371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28676610735830710035951161 21507458051873032526963371)
        ·
          refine ⟨32261187077809548790445057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21507458051873032526963371 32261187077809548790445057)
          ·
            refine ⟨24195890308357161592833793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32261187077809548790445057 24195890308357161592833793)
            ·
              refine ⟨18146917731267871194625345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24195890308357161592833793 18146917731267871194625345)
              ·
                refine ⟨13610188298450903395969009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18146917731267871194625345 13610188298450903395969009)
                ·
                  refine ⟨10207641223838177546976757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13610188298450903395969009 10207641223838177546976757)
                  ·
                    refine ⟨956966364734829145029071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10207641223838177546976757 956966364734829145029071)
                    ·
                      rfl

theorem cell22_2795528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 2, 2, 5].length) (baseStart_2795528 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2795528 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2795528 prefixEnd_2795528 := by exact prefixLift 2795528
  have htrace : WordTrace (prefixWord ++ tailWord_2795528) baseStart_2795528 baseEnd_2795528 := by
    simpa [prefixWord, tailWord_2795528, baseEnd_2795528] using wordTrace_append hprefix tailTrace_2795528
  have hstable : (prefixWord ++ tailWord_2795528).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2795528).length < 2 ^ (prefixWord ++ tailWord_2795528).sum := by decide
  have hdescent : baseEnd_2795528 < baseStart_2795528 := by decide
  rcases family_descends (prefixWord ++ tailWord_2795528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2795575 : List Nat := [1, 1, 3, 1, 2, 2, 3, 5, 4]
def baseStart_2795575 : Nat := 118140960795 + 2795575 * 2 ^ 59
def prefixEnd_2795575 : Nat := 4983230072969 + 3 ^ 40 * 2795575 * 2
def baseEnd_2795575 : Nat := 318994151265112229701309

theorem tailTrace_2795575 : CollatzResearch.WordTrace tailWord_2795575 prefixEnd_2795575 318994151265112229701309 := by
  unfold tailWord_2795575
  simp only [CollatzResearch.WordTrace]
  refine ⟨101962996847116696043676179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67975331231411130695784119 101962996847116696043676179)
  ·
    refine ⟨152944495270675044065514269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101962996847116696043676179 152944495270675044065514269)
    ·
      refine ⟨57354185726503141524567851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 152944495270675044065514269 57354185726503141524567851)
      ·
        refine ⟨86031278589754712286851777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57354185726503141524567851 86031278589754712286851777)
        ·
          refine ⟨64523458942316034215138833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86031278589754712286851777 64523458942316034215138833)
          ·
            refine ⟨48392594206737025661354125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64523458942316034215138833 48392594206737025661354125)
            ·
              refine ⟨18147222827526384623007797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48392594206737025661354125 18147222827526384623007797)
              ·
                refine ⟨1701302140080598558406981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18147222827526384623007797 1701302140080598558406981)
                ·
                  refine ⟨318994151265112229701309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1701302140080598558406981 318994151265112229701309)
                  ·
                    rfl

theorem cell22_2795575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 5, 4].length) (baseStart_2795575 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2795575 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2795575 prefixEnd_2795575 := by exact prefixLift 2795575
  have htrace : WordTrace (prefixWord ++ tailWord_2795575) baseStart_2795575 baseEnd_2795575 := by
    simpa [prefixWord, tailWord_2795575, baseEnd_2795575] using wordTrace_append hprefix tailTrace_2795575
  have hstable : (prefixWord ++ tailWord_2795575).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2795575).length < 2 ^ (prefixWord ++ tailWord_2795575).sum := by decide
  have hdescent : baseEnd_2795575 < baseStart_2795575 := by decide
  rcases family_descends (prefixWord ++ tailWord_2795575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2795577 : List Nat := [1, 2, 1, 5, 3, 1, 1, 3, 1, 4]
def baseStart_2795577 : Nat := 118140960795 + 2795577 * 2 ^ 59
def prefixEnd_2795577 : Nat := 4983230072969 + 3 ^ 40 * 2795577 * 2
def baseEnd_2795577 : Nat := 956983138436209350553921

theorem tailTrace_2795577 : CollatzResearch.WordTrace tailWord_2795577 prefixEnd_2795577 956983138436209350553921 := by
  unfold tailWord_2795577
  simp only [CollatzResearch.WordTrace]
  refine ⟨101963069793109450385248985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67975379862072966923499323 101963069793109450385248985)
  ·
    refine ⟨76472302344832087788936739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101963069793109450385248985 76472302344832087788936739)
    ·
      refine ⟨114708453517248131683405109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76472302344832087788936739 114708453517248131683405109)
      ·
        refine ⟨10753917517242012345319229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 114708453517248131683405109 10753917517242012345319229)
        ·
          refine ⟨4032719068965754629494711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10753917517242012345319229 4032719068965754629494711)
          ·
            refine ⟨6049078603448631944242067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4032719068965754629494711 6049078603448631944242067)
            ·
              refine ⟨9073617905172947916363101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6049078603448631944242067 9073617905172947916363101)
              ·
                refine ⟨3402606714439855468636163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9073617905172947916363101 3402606714439855468636163)
                ·
                  refine ⟨5103910071659783202954245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3402606714439855468636163 5103910071659783202954245)
                  ·
                    refine ⟨956983138436209350553921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5103910071659783202954245 956983138436209350553921)
                    ·
                      rfl

theorem cell22_2795577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 3, 1, 4].length) (baseStart_2795577 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2795577 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2795577 prefixEnd_2795577 := by exact prefixLift 2795577
  have htrace : WordTrace (prefixWord ++ tailWord_2795577) baseStart_2795577 baseEnd_2795577 := by
    simpa [prefixWord, tailWord_2795577, baseEnd_2795577] using wordTrace_append hprefix tailTrace_2795577
  have hstable : (prefixWord ++ tailWord_2795577).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2795577).length < 2 ^ (prefixWord ++ tailWord_2795577).sum := by decide
  have hdescent : baseEnd_2795577 < baseStart_2795577 := by decide
  rcases family_descends (prefixWord ++ tailWord_2795577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2795620 : List Nat := [2, 3, 1, 1, 2, 1, 6, 6]
def baseStart_2795620 : Nat := 118140960795 + 2795620 * 2 ^ 59
def prefixEnd_2795620 : Nat := 4983230072969 + 3 ^ 40 * 2795620 * 2
def baseEnd_2795620 : Nat := 106333095357219063525421

theorem tailTrace_2795620 : CollatzResearch.WordTrace tailWord_2795620 prefixEnd_2795620 106333095357219063525421 := by
  unfold tailWord_2795620
  simp only [CollatzResearch.WordTrace]
  refine ⟨50982319065976834364532157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67976425421302445819376209 50982319065976834364532157)
  ·
    refine ⟨19118369649741312886699559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50982319065976834364532157 19118369649741312886699559)
    ·
      refine ⟨28677554474611969330049339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19118369649741312886699559 28677554474611969330049339)
      ·
        refine ⟨43016331711917953995074009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28677554474611969330049339 43016331711917953995074009)
        ·
          refine ⟨32262248783938465496305507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43016331711917953995074009 32262248783938465496305507)
          ·
            refine ⟨48393373175907698244458261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32262248783938465496305507 48393373175907698244458261)
            ·
              refine ⟨2268439367620673355208981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 48393373175907698244458261 2268439367620673355208981)
              ·
                refine ⟨106333095357219063525421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2268439367620673355208981 106333095357219063525421)
                ·
                  rfl

theorem cell22_2795620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 6, 6].length) (baseStart_2795620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2795620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2795620 prefixEnd_2795620 := by exact prefixLift 2795620
  have htrace : WordTrace (prefixWord ++ tailWord_2795620) baseStart_2795620 baseEnd_2795620 := by
    simpa [prefixWord, tailWord_2795620, baseEnd_2795620] using wordTrace_append hprefix tailTrace_2795620
  have hstable : (prefixWord ++ tailWord_2795620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2795620).length < 2 ^ (prefixWord ++ tailWord_2795620).sum := by decide
  have hdescent : baseEnd_2795620 < baseStart_2795620 := by decide
  rcases family_descends (prefixWord ++ tailWord_2795620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2795626 : List Nat := [3, 1, 3, 2, 4, 1, 1, 3, 4]
def baseStart_2795626 : Nat := 118140960795 + 2795626 * 2 ^ 59
def prefixEnd_2795626 : Nat := 4983230072969 + 3 ^ 40 * 2795626 * 2
def baseEnd_2795626 : Nat := 318999970712529852026257

theorem tailTrace_2795626 : CollatzResearch.WordTrace tailWord_2795626 prefixEnd_2795626 318999970712529852026257 := by
  unfold tailWord_2795626
  simp only [CollatzResearch.WordTrace]
  refine ⟨25491214242482982938445683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67976571313287954502521821 25491214242482982938445683)
  ·
    refine ⟨38236821363724474407668525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25491214242482982938445683 38236821363724474407668525)
    ·
      refine ⟨14338808011396677902875697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38236821363724474407668525 14338808011396677902875697)
      ·
        refine ⟨10754106008547508427156773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14338808011396677902875697 10754106008547508427156773)
        ·
          refine ⟨2016394876602657830091895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10754106008547508427156773 2016394876602657830091895)
          ·
            refine ⟨3024592314903986745137843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2016394876602657830091895 3024592314903986745137843)
            ·
              refine ⟨4536888472355980117706765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3024592314903986745137843 4536888472355980117706765)
              ·
                refine ⟨1701333177133492544140037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4536888472355980117706765 1701333177133492544140037)
                ·
                  refine ⟨318999970712529852026257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1701333177133492544140037 318999970712529852026257)
                  ·
                    rfl

theorem cell22_2795626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 1, 3, 4].length) (baseStart_2795626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2795626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2795626 prefixEnd_2795626 := by exact prefixLift 2795626
  have htrace : WordTrace (prefixWord ++ tailWord_2795626) baseStart_2795626 baseEnd_2795626 := by
    simpa [prefixWord, tailWord_2795626, baseEnd_2795626] using wordTrace_append hprefix tailTrace_2795626
  have hstable : (prefixWord ++ tailWord_2795626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2795626).length < 2 ^ (prefixWord ++ tailWord_2795626).sum := by decide
  have hdescent : baseEnd_2795626 < baseStart_2795626 := by decide
  rcases family_descends (prefixWord ++ tailWord_2795626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2795714 : List Nat := [3, 5, 1, 1, 1, 1, 1, 1, 1, 7]
def baseStart_2795714 : Nat := 118140960795 + 2795714 * 2 ^ 59
def prefixEnd_2795714 : Nat := 4983230072969 + 3 ^ 40 * 2795714 * 2
def baseEnd_2795714 : Nat := 957030036335986659878501

theorem tailTrace_2795714 : CollatzResearch.WordTrace tailWord_2795714 prefixEnd_2795714 957030036335986659878501 := by
  unfold tailWord_2795714
  simp only [CollatzResearch.WordTrace]
  refine ⟨25492016648403280695746549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67978711062408748521990797 25492016648403280695746549)
  ·
    refine ⟨2389876560787807565226239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 25492016648403280695746549 2389876560787807565226239)
    ·
      refine ⟨3584814841181711347839359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2389876560787807565226239 3584814841181711347839359)
      ·
        refine ⟨5377222261772567021759039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3584814841181711347839359 5377222261772567021759039)
        ·
          refine ⟨8065833392658850532638559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5377222261772567021759039 8065833392658850532638559)
          ·
            refine ⟨12098750088988275798957839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8065833392658850532638559 12098750088988275798957839)
            ·
              refine ⟨18148125133482413698436759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12098750088988275798957839 18148125133482413698436759)
              ·
                refine ⟨27222187700223620547655139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18148125133482413698436759 27222187700223620547655139)
                ·
                  refine ⟨40833281550335430821482709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27222187700223620547655139 40833281550335430821482709)
                  ·
                    refine ⟨957030036335986659878501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40833281550335430821482709 957030036335986659878501)
                    ·
                      rfl

theorem cell22_2795714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_2795714 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2795714 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2795714 prefixEnd_2795714 := by exact prefixLift 2795714
  have htrace : WordTrace (prefixWord ++ tailWord_2795714) baseStart_2795714 baseEnd_2795714 := by
    simpa [prefixWord, tailWord_2795714, baseEnd_2795714] using wordTrace_append hprefix tailTrace_2795714
  have hstable : (prefixWord ++ tailWord_2795714).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2795714).length < 2 ^ (prefixWord ++ tailWord_2795714).sum := by decide
  have hdescent : baseEnd_2795714 < baseStart_2795714 := by decide
  rcases family_descends (prefixWord ++ tailWord_2795714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2795759 : List Nat := [1, 1, 2, 1, 6, 1, 3, 2, 2, 3]
def baseStart_2795759 : Nat := 118140960795 + 2795759 * 2 ^ 59
def prefixEnd_2795759 : Nat := 4983230072969 + 3 ^ 40 * 2795759 * 2
def baseEnd_2795759 : Nat := 957045440755621542503363

theorem tailTrace_2795759 : CollatzResearch.WordTrace tailWord_2795759 prefixEnd_2795759 957045440755621542503363 := by
  unfold tailWord_2795759
  simp only [CollatzResearch.WordTrace]
  refine ⟨101969707878450095468374331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67979805252300063645582887 101969707878450095468374331)
  ·
    refine ⟨152954561817675143202561497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101969707878450095468374331 152954561817675143202561497)
    ·
      refine ⟨114715921363256357401921123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152954561817675143202561497 114715921363256357401921123)
      ·
        refine ⟨172073882044884536102881685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114715921363256357401921123 172073882044884536102881685)
        ·
          refine ⟨8065963220853962629822579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 172073882044884536102881685 8065963220853962629822579)
          ·
            refine ⟨12098944831280943944733869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8065963220853962629822579 12098944831280943944733869)
            ·
              refine ⟨4537104311730353979275201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12098944831280943944733869 4537104311730353979275201)
              ·
                refine ⟨3402828233797765484456401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4537104311730353979275201 3402828233797765484456401)
                ·
                  refine ⟨2552121175348324113342301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3402828233797765484456401 2552121175348324113342301)
                  ·
                    refine ⟨957045440755621542503363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2552121175348324113342301 957045440755621542503363)
                    ·
                      rfl

theorem cell22_2795759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 3, 2, 2, 3].length) (baseStart_2795759 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2795759 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2795759 prefixEnd_2795759 := by exact prefixLift 2795759
  have htrace : WordTrace (prefixWord ++ tailWord_2795759) baseStart_2795759 baseEnd_2795759 := by
    simpa [prefixWord, tailWord_2795759, baseEnd_2795759] using wordTrace_append hprefix tailTrace_2795759
  have hstable : (prefixWord ++ tailWord_2795759).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2795759).length < 2 ^ (prefixWord ++ tailWord_2795759).sum := by decide
  have hdescent : baseEnd_2795759 < baseStart_2795759 := by decide
  rcases family_descends (prefixWord ++ tailWord_2795759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2795787 : List Nat := [1, 1, 1, 1, 5, 2, 1, 4, 3, 3]
def baseStart_2795787 : Nat := 118140960795 + 2795787 * 2 ^ 59
def prefixEnd_2795787 : Nat := 4983230072969 + 3 ^ 40 * 2795787 * 2
def baseEnd_2795787 : Nat := 957055025727838802803277

theorem tailTrace_2795787 : CollatzResearch.WordTrace tailWord_2795787 prefixEnd_2795787 957055025727838802803277 := by
  unfold tailWord_2795787
  simp only [CollatzResearch.WordTrace]
  refine ⟨101970729122348656250393615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67980486081565770833595743 101970729122348656250393615)
  ·
    refine ⟨152956093683522984375590423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101970729122348656250393615 152956093683522984375590423)
    ·
      refine ⟨229434140525284476563385635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152956093683522984375590423 229434140525284476563385635)
      ·
        refine ⟨344151210787926714845078453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 229434140525284476563385635 344151210787926714845078453)
        ·
          refine ⟨32264176011368129516726105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 344151210787926714845078453 32264176011368129516726105)
          ·
            refine ⟨24198132008526097137544579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32264176011368129516726105 24198132008526097137544579)
            ·
              refine ⟨36297198012789145706316869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24198132008526097137544579 36297198012789145706316869)
              ·
                refine ⟨6805724627397964819934413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36297198012789145706316869 6805724627397964819934413)
                ·
                  refine ⟨2552146735274236807475405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6805724627397964819934413 2552146735274236807475405)
                  ·
                    refine ⟨957055025727838802803277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2552146735274236807475405 957055025727838802803277)
                    ·
                      rfl

theorem cell22_2795787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 4, 3, 3].length) (baseStart_2795787 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2795787 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2795787 prefixEnd_2795787 := by exact prefixLift 2795787
  have htrace : WordTrace (prefixWord ++ tailWord_2795787) baseStart_2795787 baseEnd_2795787 := by
    simpa [prefixWord, tailWord_2795787, baseEnd_2795787] using wordTrace_append hprefix tailTrace_2795787
  have hstable : (prefixWord ++ tailWord_2795787).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2795787).length < 2 ^ (prefixWord ++ tailWord_2795787).sum := by decide
  have hdescent : baseEnd_2795787 < baseStart_2795787 := by decide
  rcases family_descends (prefixWord ++ tailWord_2795787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2795800 : List Nat := [2, 1, 2, 3, 1, 2, 1, 1, 9]
def baseStart_2795800 : Nat := 118140960795 + 2795800 * 2 ^ 59
def prefixEnd_2795800 : Nat := 4983230072969 + 3 ^ 40 * 2795800 * 2
def baseEnd_2795800 : Nat := 319019825297837034076079

theorem tailTrace_2795800 : CollatzResearch.WordTrace tailWord_2795800 prefixEnd_2795800 319019825297837034076079 := by
  unfold tailWord_2795800
  simp only [CollatzResearch.WordTrace]
  refine ⟨50985601635650779735308427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67980802180867706313744569 50985601635650779735308427)
  ·
    refine ⟨76478402453476169602962641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50985601635650779735308427 76478402453476169602962641)
    ·
      refine ⟨57358801840107127202221981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76478402453476169602962641 57358801840107127202221981)
      ·
        refine ⟨21509550690040172700833243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57358801840107127202221981 21509550690040172700833243)
        ·
          refine ⟨32264326035060259051249865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21509550690040172700833243 32264326035060259051249865)
          ·
            refine ⟨24198244526295194288437399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32264326035060259051249865 24198244526295194288437399)
            ·
              refine ⟨36297366789442791432656099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24198244526295194288437399 36297366789442791432656099)
              ·
                refine ⟨54446050184164187148984149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36297366789442791432656099 54446050184164187148984149)
                ·
                  refine ⟨319019825297837034076079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 54446050184164187148984149 319019825297837034076079)
                  ·
                    rfl

theorem cell22_2795800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 1, 9].length) (baseStart_2795800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2795800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2795800 prefixEnd_2795800 := by exact prefixLift 2795800
  have htrace : WordTrace (prefixWord ++ tailWord_2795800) baseStart_2795800 baseEnd_2795800 := by
    simpa [prefixWord, tailWord_2795800, baseEnd_2795800] using wordTrace_append hprefix tailTrace_2795800
  have hstable : (prefixWord ++ tailWord_2795800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2795800).length < 2 ^ (prefixWord ++ tailWord_2795800).sum := by decide
  have hdescent : baseEnd_2795800 < baseStart_2795800 := by decide
  rcases family_descends (prefixWord ++ tailWord_2795800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2795834 : List Nat := [3, 1, 1, 1, 4, 2, 4, 1, 5]
def baseStart_2795834 : Nat := 118140960795 + 2795834 * 2 ^ 59
def prefixEnd_2795834 : Nat := 4983230072969 + 3 ^ 40 * 2795834 * 2
def baseEnd_2795834 : Nat := 319023704929448782292711

theorem tailTrace_2795834 : CollatzResearch.WordTrace tailWord_2795834 prefixEnd_2795834 319023704929448782292711 := by
  unfold tailWord_2795834
  simp only [CollatzResearch.WordTrace]
  refine ⟨25493110838294595819338639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67981628902118922184903037 25493110838294595819338639)
  ·
    refine ⟨38239666257441893729007959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25493110838294595819338639 38239666257441893729007959)
    ·
      refine ⟨57359499386162840593511939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38239666257441893729007959 57359499386162840593511939)
      ·
        refine ⟨86039249079244260890267909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57359499386162840593511939 86039249079244260890267909)
        ·
          refine ⟨16132359202358298916925233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 86039249079244260890267909 16132359202358298916925233)
          ·
            refine ⟨12099269401768724187693925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16132359202358298916925233 12099269401768724187693925)
            ·
              refine ⟨2268613012831635785192611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12099269401768724187693925 2268613012831635785192611)
              ·
                refine ⟨3402919519247453677788917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2268613012831635785192611 3402919519247453677788917)
                ·
                  refine ⟨319023704929448782292711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3402919519247453677788917 319023704929448782292711)
                  ·
                    rfl

theorem cell22_2795834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 4, 1, 5].length) (baseStart_2795834 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2795834 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2795834 prefixEnd_2795834 := by exact prefixLift 2795834
  have htrace : WordTrace (prefixWord ++ tailWord_2795834) baseStart_2795834 baseEnd_2795834 := by
    simpa [prefixWord, tailWord_2795834, baseEnd_2795834] using wordTrace_append hprefix tailTrace_2795834
  have hstable : (prefixWord ++ tailWord_2795834).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2795834).length < 2 ^ (prefixWord ++ tailWord_2795834).sum := by decide
  have hdescent : baseEnd_2795834 < baseStart_2795834 := by decide
  rcases family_descends (prefixWord ++ tailWord_2795834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2795847 : List Nat := [1, 1, 4, 1, 2, 2, 3, 1, 3, 4]
def baseStart_2795847 : Nat := 118140960795 + 2795847 * 2 ^ 59
def prefixEnd_2795847 : Nat := 4983230072969 + 3 ^ 40 * 2795847 * 2
def baseEnd_2795847 : Nat := 957075564954018646303093

theorem tailTrace_2795847 : CollatzResearch.WordTrace tailWord_2795847 prefixEnd_2795847 957075564954018646303093 := by
  unfold tailWord_2795847
  simp only [CollatzResearch.WordTrace]
  refine ⟨101972917502131286497577795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67981945001420857665051863 101972917502131286497577795)
  ·
    refine ⟨152959376253196929746366693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101972917502131286497577795 152959376253196929746366693)
    ·
      refine ⟨28679883047474424327443755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 152959376253196929746366693 28679883047474424327443755)
      ·
        refine ⟨43019824571211636491165633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28679883047474424327443755 43019824571211636491165633)
        ·
          refine ⟨32264868428408727368374225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43019824571211636491165633 32264868428408727368374225)
          ·
            refine ⟨24198651321306545526280669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32264868428408727368374225 24198651321306545526280669)
            ·
              refine ⟨9074494245489954572355251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24198651321306545526280669 9074494245489954572355251)
              ·
                refine ⟨13611741368234931858532877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9074494245489954572355251 13611741368234931858532877)
                ·
                  refine ⟨5104403013088099446949829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13611741368234931858532877 5104403013088099446949829)
                  ·
                    refine ⟨957075564954018646303093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5104403013088099446949829 957075564954018646303093)
                    ·
                      rfl

theorem cell22_2795847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 1, 3, 4].length) (baseStart_2795847 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2795847 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2795847 prefixEnd_2795847 := by exact prefixLift 2795847
  have htrace : WordTrace (prefixWord ++ tailWord_2795847) baseStart_2795847 baseEnd_2795847 := by
    simpa [prefixWord, tailWord_2795847, baseEnd_2795847] using wordTrace_append hprefix tailTrace_2795847
  have hstable : (prefixWord ++ tailWord_2795847).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2795847).length < 2 ^ (prefixWord ++ tailWord_2795847).sum := by decide
  have hdescent : baseEnd_2795847 < baseStart_2795847 := by decide
  rcases family_descends (prefixWord ++ tailWord_2795847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2795924 : List Nat := [2, 4, 2, 1, 3, 1, 9]
def baseStart_2795924 : Nat := 118140960795 + 2795924 * 2 ^ 59
def prefixEnd_2795924 : Nat := 4983230072969 + 3 ^ 40 * 2795924 * 2
def baseEnd_2795924 : Nat := 35448219393615411560291

theorem tailTrace_2795924 : CollatzResearch.WordTrace tailWord_2795924 prefixEnd_2795924 35448219393615411560291 := by
  unfold tailWord_2795924
  simp only [CollatzResearch.WordTrace]
  refine ⟨50987862961426164324065413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67983817281901552432087217 50987862961426164324065413)
  ·
    refine ⟨9560224305267405810762265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50987862961426164324065413 9560224305267405810762265)
    ·
      refine ⟨7170168228950554358071699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9560224305267405810762265 7170168228950554358071699)
      ·
        refine ⟨10755252343425831537107549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7170168228950554358071699 10755252343425831537107549)
        ·
          refine ⟨4033219628784686826415331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10755252343425831537107549 4033219628784686826415331)
          ·
            refine ⟨6049829443177030239622997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4033219628784686826415331 6049829443177030239622997)
            ·
              refine ⟨35448219393615411560291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6049829443177030239622997 35448219393615411560291)
              ·
                rfl

theorem cell22_2795924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 9].length) (baseStart_2795924 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2795924 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2795924 prefixEnd_2795924 := by exact prefixLift 2795924
  have htrace : WordTrace (prefixWord ++ tailWord_2795924) baseStart_2795924 baseEnd_2795924 := by
    simpa [prefixWord, tailWord_2795924, baseEnd_2795924] using wordTrace_append hprefix tailTrace_2795924
  have hstable : (prefixWord ++ tailWord_2795924).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2795924).length < 2 ^ (prefixWord ++ tailWord_2795924).sum := by decide
  have hdescent : baseEnd_2795924 < baseStart_2795924 := by decide
  rcases family_descends (prefixWord ++ tailWord_2795924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2795928 : List Nat := [2, 1, 2, 5, 1, 3, 1, 2, 2, 3]
def baseStart_2795928 : Nat := 118140960795 + 2795928 * 2 ^ 59
def prefixEnd_2795928 : Nat := 4983230072969 + 3 ^ 40 * 2795928 * 2
def baseEnd_2795928 : Nat := 957103292909361435027845

theorem tailTrace_2795928 : CollatzResearch.WordTrace tailWord_2795928 prefixEnd_2795928 957103292909361435027845 := by
  unfold tailWord_2795928
  simp only [CollatzResearch.WordTrace]
  refine ⟨50987935907418918665638219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67983914543225224887517625 50987935907418918665638219)
  ·
    refine ⟨76481903861128377998457329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50987935907418918665638219 76481903861128377998457329)
    ·
      refine ⟨57361427895846283498842997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76481903861128377998457329 57361427895846283498842997)
      ·
        refine ⟨5377633865235589078016531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 57361427895846283498842997 5377633865235589078016531)
        ·
          refine ⟨8066450797853383617024797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5377633865235589078016531 8066450797853383617024797)
          ·
            refine ⟨3024919049195018856384299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8066450797853383617024797 3024919049195018856384299)
            ·
              refine ⟨4537378573792528284576449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3024919049195018856384299 4537378573792528284576449)
              ·
                refine ⟨3403033930344396213432337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4537378573792528284576449 3403033930344396213432337)
                ·
                  refine ⟨2552275447758297160074253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3403033930344396213432337 2552275447758297160074253)
                  ·
                    refine ⟨957103292909361435027845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2552275447758297160074253 957103292909361435027845)
                    ·
                      rfl

theorem cell22_2795928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 1, 2, 2, 3].length) (baseStart_2795928 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2795928 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2795928 prefixEnd_2795928 := by exact prefixLift 2795928
  have htrace : WordTrace (prefixWord ++ tailWord_2795928) baseStart_2795928 baseEnd_2795928 := by
    simpa [prefixWord, tailWord_2795928, baseEnd_2795928] using wordTrace_append hprefix tailTrace_2795928
  have hstable : (prefixWord ++ tailWord_2795928).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2795928).length < 2 ^ (prefixWord ++ tailWord_2795928).sum := by decide
  have hdescent : baseEnd_2795928 < baseStart_2795928 := by decide
  rcases family_descends (prefixWord ++ tailWord_2795928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2795939 : List Nat := [1, 1, 1, 4, 1, 4, 1, 3, 3, 3]
def baseStart_2795939 : Nat := 118140960795 + 2795939 * 2 ^ 59
def prefixEnd_2795939 : Nat := 4983230072969 + 3 ^ 40 * 2795939 * 2
def baseEnd_2795939 : Nat := 957107058434161073002811

theorem tailTrace_2795939 : CollatzResearch.WordTrace tailWord_2795939 prefixEnd_2795939 957107058434161073002811 := by
  unfold tailWord_2795939
  simp only [CollatzResearch.WordTrace]
  refine ⟨101976273017797986209926871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67984182011865324139951247 101976273017797986209926871)
  ·
    refine ⟨152964409526696979314890307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101976273017797986209926871 152964409526696979314890307)
    ·
      refine ⟨229446614290045468972335461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152964409526696979314890307 229446614290045468972335461)
      ·
        refine ⟨43021240179383525432312899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 229446614290045468972335461 43021240179383525432312899)
        ·
          refine ⟨64531860269075288148469349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43021240179383525432312899 64531860269075288148469349)
          ·
            refine ⟨12099723800451616527838003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64531860269075288148469349 12099723800451616527838003)
            ·
              refine ⟨18149585700677424791757005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12099723800451616527838003 18149585700677424791757005)
              ·
                refine ⟨6806094637754034296908877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18149585700677424791757005 6806094637754034296908877)
                ·
                  refine ⟨2552285489157762861340829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6806094637754034296908877 2552285489157762861340829)
                  ·
                    refine ⟨957107058434161073002811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2552285489157762861340829 957107058434161073002811)
                    ·
                      rfl

theorem cell22_2795939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 3, 3, 3].length) (baseStart_2795939 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2795939 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2795939 prefixEnd_2795939 := by exact prefixLift 2795939
  have htrace : WordTrace (prefixWord ++ tailWord_2795939) baseStart_2795939 baseEnd_2795939 := by
    simpa [prefixWord, tailWord_2795939, baseEnd_2795939] using wordTrace_append hprefix tailTrace_2795939
  have hstable : (prefixWord ++ tailWord_2795939).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2795939).length < 2 ^ (prefixWord ++ tailWord_2795939).sum := by decide
  have hdescent : baseEnd_2795939 < baseStart_2795939 := by decide
  rcases family_descends (prefixWord ++ tailWord_2795939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2796003 : List Nat := [1, 1, 1, 6, 3, 2, 2, 1, 5]
def baseStart_2796003 : Nat := 118140960795 + 2796003 * 2 ^ 59
def prefixEnd_2796003 : Nat := 4983230072969 + 3 ^ 40 * 2796003 * 2
def baseEnd_2796003 : Nat := 319042988980695413134205

theorem tailTrace_2796003 : CollatzResearch.WordTrace tailWord_2796003 prefixEnd_2796003 319042988980695413134205 := by
  unfold tailWord_2796003
  simp only [CollatzResearch.WordTrace]
  refine ⟨101978607289566125140256663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67985738193044083426837775 101978607289566125140256663)
  ·
    refine ⟨152967910934349187710384995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101978607289566125140256663 152967910934349187710384995)
    ·
      refine ⟨229451866401523781565577493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152967910934349187710384995 229451866401523781565577493)
      ·
        refine ⟨10755556237571427260886445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 229451866401523781565577493 10755556237571427260886445)
        ·
          refine ⟨4033333589089285222832417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10755556237571427260886445 4033333589089285222832417)
          ·
            refine ⟨3025000191816963917124313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4033333589089285222832417 3025000191816963917124313)
            ·
              refine ⟨2268750143862722937843235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3025000191816963917124313 2268750143862722937843235)
              ·
                refine ⟨3403125215794084406764853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2268750143862722937843235 3403125215794084406764853)
                ·
                  refine ⟨319042988980695413134205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3403125215794084406764853 319042988980695413134205)
                  ·
                    rfl

theorem cell22_2796003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 2, 1, 5].length) (baseStart_2796003 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2796003 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2796003 prefixEnd_2796003 := by exact prefixLift 2796003
  have htrace : WordTrace (prefixWord ++ tailWord_2796003) baseStart_2796003 baseEnd_2796003 := by
    simpa [prefixWord, tailWord_2796003, baseEnd_2796003] using wordTrace_append hprefix tailTrace_2796003
  have hstable : (prefixWord ++ tailWord_2796003).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2796003).length < 2 ^ (prefixWord ++ tailWord_2796003).sum := by decide
  have hdescent : baseEnd_2796003 < baseStart_2796003 := by decide
  rcases family_descends (prefixWord ++ tailWord_2796003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2796029 : List Nat := [1, 4, 1, 1, 1, 3, 3, 2, 1, 5]
def baseStart_2796029 : Nat := 118140960795 + 2796029 * 2 ^ 59
def prefixEnd_2796029 : Nat := 4983230072969 + 3 ^ 40 * 2796029 * 2
def baseEnd_2796029 : Nat := 957137867273430838252535

theorem tailTrace_2796029 : CollatzResearch.WordTrace tailWord_2796029 prefixEnd_2796029 957137867273430838252535 := by
  unfold tailWord_2796029
  simp only [CollatzResearch.WordTrace]
  refine ⟨101979555587471931580703141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67986370391647954387135427 101979555587471931580703141)
  ·
    refine ⟨19121166672650987171381839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 101979555587471931580703141 19121166672650987171381839)
    ·
      refine ⟨28681750008976480757072759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19121166672650987171381839 28681750008976480757072759)
      ·
        refine ⟨43022625013464721135609139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28681750008976480757072759 43022625013464721135609139)
        ·
          refine ⟨64533937520197081703413709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43022625013464721135609139 64533937520197081703413709)
          ·
            refine ⟨24200226570073905638780141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64533937520197081703413709 24200226570073905638780141)
            ·
              refine ⟨9075084963777714614542553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24200226570073905638780141 9075084963777714614542553)
              ·
                refine ⟨6806313722833285960906915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9075084963777714614542553 6806313722833285960906915)
                ·
                  refine ⟨10209470584249928941360373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6806313722833285960906915 10209470584249928941360373)
                  ·
                    refine ⟨957137867273430838252535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10209470584249928941360373 957137867273430838252535)
                    ·
                      rfl

theorem cell22_2796029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 2, 1, 5].length) (baseStart_2796029 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2796029 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2796029 prefixEnd_2796029 := by exact prefixLift 2796029
  have htrace : WordTrace (prefixWord ++ tailWord_2796029) baseStart_2796029 baseEnd_2796029 := by
    simpa [prefixWord, tailWord_2796029, baseEnd_2796029] using wordTrace_append hprefix tailTrace_2796029
  have hstable : (prefixWord ++ tailWord_2796029).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2796029).length < 2 ^ (prefixWord ++ tailWord_2796029).sum := by decide
  have hdescent : baseEnd_2796029 < baseStart_2796029 := by decide
  rcases family_descends (prefixWord ++ tailWord_2796029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2796033 : List Nat := [1, 2, 4, 1, 3, 2, 3, 1, 1, 4]
def baseStart_2796033 : Nat := 118140960795 + 2796033 * 2 ^ 59
def prefixEnd_2796033 : Nat := 4983230072969 + 3 ^ 40 * 2796033 * 2
def baseEnd_2796033 : Nat := 957139236555176161152523

theorem tailTrace_2796033 : CollatzResearch.WordTrace tailWord_2796033 prefixEnd_2796033 957139236555176161152523 := by
  unfold tailWord_2796033
  simp only [CollatzResearch.WordTrace]
  refine ⟨101979701479457440263848753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67986467652971626842565835 101979701479457440263848753)
  ·
    refine ⟨76484776109593080197886565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101979701479457440263848753 76484776109593080197886565)
    ·
      refine ⟨14340895520548702537103731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 76484776109593080197886565 14340895520548702537103731)
      ·
        refine ⟨21511343280823053805655597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14340895520548702537103731 21511343280823053805655597)
        ·
          refine ⟨8066753730308645177120849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21511343280823053805655597 8066753730308645177120849)
          ·
            refine ⟨6050065297731483882840637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8066753730308645177120849 6050065297731483882840637)
            ·
              refine ⟨2268774486649306456065239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6050065297731483882840637 2268774486649306456065239)
              ·
                refine ⟨3403161729973959684097859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2268774486649306456065239 3403161729973959684097859)
                ·
                  refine ⟨5104742594960939526146789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3403161729973959684097859 5104742594960939526146789)
                  ·
                    refine ⟨957139236555176161152523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5104742594960939526146789 957139236555176161152523)
                    ·
                      rfl

theorem cell22_2796033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 3, 1, 1, 4].length) (baseStart_2796033 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2796033 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2796033 prefixEnd_2796033 := by exact prefixLift 2796033
  have htrace : WordTrace (prefixWord ++ tailWord_2796033) baseStart_2796033 baseEnd_2796033 := by
    simpa [prefixWord, tailWord_2796033, baseEnd_2796033] using wordTrace_append hprefix tailTrace_2796033
  have hstable : (prefixWord ++ tailWord_2796033).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2796033).length < 2 ^ (prefixWord ++ tailWord_2796033).sum := by decide
  have hdescent : baseEnd_2796033 < baseStart_2796033 := by decide
  rcases family_descends (prefixWord ++ tailWord_2796033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2796084 : List Nat := [2, 5, 1, 3, 2, 1, 2, 1, 1, 4]
def baseStart_2796084 : Nat := 118140960795 + 2796084 * 2 ^ 59
def prefixEnd_2796084 : Nat := 4983230072969 + 3 ^ 40 * 2796084 * 2
def baseEnd_2796084 : Nat := 957156694897429028127367

theorem tailTrace_2796084 : CollatzResearch.WordTrace tailWord_2796084 prefixEnd_2796084 957156694897429028127367 := by
  unfold tailWord_2796084
  simp only [CollatzResearch.WordTrace]
  refine ⟨50990780801136337986977653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67987707734848450649303537 50990780801136337986977653)
  ·
    refine ⟨4780385700106531686279155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 50990780801136337986977653 4780385700106531686279155)
    ·
      refine ⟨7170578550159797529418733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4780385700106531686279155 7170578550159797529418733)
      ·
        refine ⟨2688966956309924073532025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7170578550159797529418733 2688966956309924073532025)
        ·
          refine ⟨2016725217232443055149019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2688966956309924073532025 2016725217232443055149019)
          ·
            refine ⟨3025087825848664582723529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2016725217232443055149019 3025087825848664582723529)
            ·
              refine ⟨2268815869386498437042647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3025087825848664582723529 2268815869386498437042647)
              ·
                refine ⟨3403223804079747655563971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2268815869386498437042647 3403223804079747655563971)
                ·
                  refine ⟨5104835706119621483345957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3403223804079747655563971 5104835706119621483345957)
                  ·
                    refine ⟨957156694897429028127367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5104835706119621483345957 957156694897429028127367)
                    ·
                      rfl

theorem cell22_2796084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 2, 1, 1, 4].length) (baseStart_2796084 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2796084 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2796084 prefixEnd_2796084 := by exact prefixLift 2796084
  have htrace : WordTrace (prefixWord ++ tailWord_2796084) baseStart_2796084 baseEnd_2796084 := by
    simpa [prefixWord, tailWord_2796084, baseEnd_2796084] using wordTrace_append hprefix tailTrace_2796084
  have hstable : (prefixWord ++ tailWord_2796084).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2796084).length < 2 ^ (prefixWord ++ tailWord_2796084).sum := by decide
  have hdescent : baseEnd_2796084 < baseStart_2796084 := by decide
  rcases family_descends (prefixWord ++ tailWord_2796084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2796108 : List Nat := [2, 2, 1, 3, 1, 2, 1, 6, 1, 3]
def baseStart_2796108 : Nat := 118140960795 + 2796108 * 2 ^ 59
def prefixEnd_2796108 : Nat := 4983230072969 + 3 ^ 40 * 2796108 * 2
def baseEnd_2796108 : Nat := 957164910587900965527293

theorem tailTrace_2796108 : CollatzResearch.WordTrace tailWord_2796108 prefixEnd_2796108 957164910587900965527293 := by
  unfold tailWord_2796108
  simp only [CollatzResearch.WordTrace]
  refine ⟨50991218477092864036414489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67988291302790485381885985 50991218477092864036414489)
  ·
    refine ⟨38243413857819648027310867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50991218477092864036414489 38243413857819648027310867)
    ·
      refine ⟨57365120786729472040966301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38243413857819648027310867 57365120786729472040966301)
      ·
        refine ⟨21511920295023552015362363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57365120786729472040966301 21511920295023552015362363)
        ·
          refine ⟨32267880442535328023043545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21511920295023552015362363 32267880442535328023043545)
          ·
            refine ⟨24200910331901496017282659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32267880442535328023043545 24200910331901496017282659)
            ·
              refine ⟨36301365497852244025923989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24200910331901496017282659 36301365497852244025923989)
              ·
                refine ⟨1701626507711823938715187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 36301365497852244025923989 1701626507711823938715187)
                ·
                  refine ⟨2552439761567735908072781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1701626507711823938715187 2552439761567735908072781)
                  ·
                    refine ⟨957164910587900965527293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2552439761567735908072781 957164910587900965527293)
                    ·
                      rfl

theorem cell22_2796108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 6, 1, 3].length) (baseStart_2796108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2796108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2796108 prefixEnd_2796108 := by exact prefixLift 2796108
  have htrace : WordTrace (prefixWord ++ tailWord_2796108) baseStart_2796108 baseEnd_2796108 := by
    simpa [prefixWord, tailWord_2796108, baseEnd_2796108] using wordTrace_append hprefix tailTrace_2796108
  have hstable : (prefixWord ++ tailWord_2796108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2796108).length < 2 ^ (prefixWord ++ tailWord_2796108).sum := by decide
  have hdescent : baseEnd_2796108 < baseStart_2796108 := by decide
  rcases family_descends (prefixWord ++ tailWord_2796108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2796119 : List Nat := [1, 1, 3, 2, 2, 2, 1, 3, 2, 5]
def baseStart_2796119 : Nat := 118140960795 + 2796119 * 2 ^ 59
def prefixEnd_2796119 : Nat := 4983230072969 + 3 ^ 40 * 2796119 * 2
def baseEnd_2796119 : Nat := 957168676112700603502259

theorem tailTrace_2796119 : CollatzResearch.WordTrace tailWord_2796119 prefixEnd_2796119 957168676112700603502259 := by
  unfold tailWord_2796119
  simp only [CollatzResearch.WordTrace]
  refine ⟨101982838157145876951479411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67988558771430584634319607 101982838157145876951479411)
  ·
    refine ⟨152974257235718815427219117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101982838157145876951479411 152974257235718815427219117)
    ·
      refine ⟨57365346463394555785207169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 152974257235718815427219117 57365346463394555785207169)
      ·
        refine ⟨43024009847545916838905377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57365346463394555785207169 43024009847545916838905377)
        ·
          refine ⟨32268007385659437629179033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43024009847545916838905377 32268007385659437629179033)
          ·
            refine ⟨24201005539244578221884275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32268007385659437629179033 24201005539244578221884275)
            ·
              refine ⟨36301508308866867332826413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24201005539244578221884275 36301508308866867332826413)
              ·
                refine ⟨13613065615825075249809905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36301508308866867332826413 13613065615825075249809905)
                ·
                  refine ⟨10209799211868806437357429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13613065615825075249809905 10209799211868806437357429)
                  ·
                    refine ⟨957168676112700603502259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10209799211868806437357429 957168676112700603502259)
                    ·
                      rfl

theorem cell22_2796119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 3, 2, 5].length) (baseStart_2796119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2796119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2796119 prefixEnd_2796119 := by exact prefixLift 2796119
  have htrace : WordTrace (prefixWord ++ tailWord_2796119) baseStart_2796119 baseEnd_2796119 := by
    simpa [prefixWord, tailWord_2796119, baseEnd_2796119] using wordTrace_append hprefix tailTrace_2796119
  have hstable : (prefixWord ++ tailWord_2796119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2796119).length < 2 ^ (prefixWord ++ tailWord_2796119).sum := by decide
  have hdescent : baseEnd_2796119 < baseStart_2796119 := by decide
  rcases family_descends (prefixWord ++ tailWord_2796119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2796142 : List Nat := [4, 1, 2, 2, 2, 3, 1, 3, 1, 3]
def baseStart_2796142 : Nat := 118140960795 + 2796142 * 2 ^ 59
def prefixEnd_2796142 : Nat := 4983230072969 + 3 ^ 40 * 2796142 * 2
def baseEnd_2796142 : Nat := 957176549482736210177189

theorem tailTrace_2796142 : CollatzResearch.WordTrace tailWord_2796142 prefixEnd_2796142 957176549482736210177189 := by
  unfold tailWord_2796142
  simp only [CollatzResearch.WordTrace]
  refine ⟨12747959629507818984945835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67989118024041701253044453 12747959629507818984945835)
  ·
    refine ⟨19121939444261728477418753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12747959629507818984945835 19121939444261728477418753)
    ·
      refine ⟨14341454583196296358064065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19121939444261728477418753 14341454583196296358064065)
      ·
        refine ⟨10756090937397222268548049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14341454583196296358064065 10756090937397222268548049)
        ·
          refine ⟨8067068203047916701411037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10756090937397222268548049 8067068203047916701411037)
          ·
            refine ⟨3025150576142968763029139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8067068203047916701411037 3025150576142968763029139)
            ·
              refine ⟨4537725864214453144543709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3025150576142968763029139 4537725864214453144543709)
              ·
                refine ⟨1701647199080419929203891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4537725864214453144543709 1701647199080419929203891)
                ·
                  refine ⟨2552470798620629893805837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1701647199080419929203891 2552470798620629893805837)
                  ·
                    refine ⟨957176549482736210177189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2552470798620629893805837 957176549482736210177189)
                    ·
                      rfl

theorem cell22_2796142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 1, 3, 1, 3].length) (baseStart_2796142 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2796142 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2796142 prefixEnd_2796142 := by exact prefixLift 2796142
  have htrace : WordTrace (prefixWord ++ tailWord_2796142) baseStart_2796142 baseEnd_2796142 := by
    simpa [prefixWord, tailWord_2796142, baseEnd_2796142] using wordTrace_append hprefix tailTrace_2796142
  have hstable : (prefixWord ++ tailWord_2796142).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2796142).length < 2 ^ (prefixWord ++ tailWord_2796142).sum := by decide
  have hdescent : baseEnd_2796142 < baseStart_2796142 := by decide
  rcases family_descends (prefixWord ++ tailWord_2796142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2796151 : List Nat := [1, 1, 3, 1, 1, 3, 4, 3, 1, 4]
def baseStart_2796151 : Nat := 118140960795 + 2796151 * 2 ^ 59
def prefixEnd_2796151 : Nat := 4983230072969 + 3 ^ 40 * 2796151 * 2
def baseEnd_2796151 : Nat := 957179630366663186702161

theorem tailTrace_2796151 : CollatzResearch.WordTrace tailWord_2796151 prefixEnd_2796151 957179630366663186702161 := by
  unfold tailWord_2796151
  simp only [CollatzResearch.WordTrace]
  refine ⟨101984005293029946416644307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67989336862019964277762871 101984005293029946416644307)
  ·
    refine ⟨152976007939544919624966461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101984005293029946416644307 152976007939544919624966461)
    ·
      refine ⟨57366002977329344859362423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 152976007939544919624966461 57366002977329344859362423)
      ·
        refine ⟨86049004465994017289043635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57366002977329344859362423 86049004465994017289043635)
        ·
          refine ⟨129073506698991025933565453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86049004465994017289043635 129073506698991025933565453)
          ·
            refine ⟨48402565012121634725087045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 129073506698991025933565453 48402565012121634725087045)
            ·
              refine ⟨9075480939772806510953821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48402565012121634725087045 9075480939772806510953821)
              ·
                refine ⟨3403305352414802441607683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9075480939772806510953821 3403305352414802441607683)
                ·
                  refine ⟨5104958028622203662411525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3403305352414802441607683 5104958028622203662411525)
                  ·
                    refine ⟨957179630366663186702161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5104958028622203662411525 957179630366663186702161)
                    ·
                      rfl

theorem cell22_2796151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 3, 1, 4].length) (baseStart_2796151 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2796151 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2796151 prefixEnd_2796151 := by exact prefixLift 2796151
  have htrace : WordTrace (prefixWord ++ tailWord_2796151) baseStart_2796151 baseEnd_2796151 := by
    simpa [prefixWord, tailWord_2796151, baseEnd_2796151] using wordTrace_append hprefix tailTrace_2796151
  have hstable : (prefixWord ++ tailWord_2796151).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2796151).length < 2 ^ (prefixWord ++ tailWord_2796151).sum := by decide
  have hdescent : baseEnd_2796151 < baseStart_2796151 := by decide
  rcases family_descends (prefixWord ++ tailWord_2796151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2796213 : List Nat := [1, 3, 3, 3, 1, 1, 2, 2, 2, 4]
def baseStart_2796213 : Nat := 118140960795 + 2796213 * 2 ^ 59
def prefixEnd_2796213 : Nat := 4983230072969 + 3 ^ 40 * 2796213 * 2
def baseEnd_2796213 : Nat := 957200854233715691651971

theorem tailTrace_2796213 : CollatzResearch.WordTrace tailWord_2796213 prefixEnd_2796213 957200854233715691651971 := by
  unfold tailWord_2796213
  simp only [CollatzResearch.WordTrace]
  refine ⟨101986266618805331005401293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67990844412536887336934195 101986266618805331005401293)
  ·
    refine ⟨38244849982051999127025485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101986266618805331005401293 38244849982051999127025485)
    ·
      refine ⟨14341818743269499672634557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38244849982051999127025485 14341818743269499672634557)
      ·
        refine ⟨5378182028726062377237959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14341818743269499672634557 5378182028726062377237959)
        ·
          refine ⟨8067273043089093565856939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5378182028726062377237959 8067273043089093565856939)
          ·
            refine ⟨12100909564633640348785409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8067273043089093565856939 12100909564633640348785409)
            ·
              refine ⟨9075682173475230261589057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12100909564633640348785409 9075682173475230261589057)
              ·
                refine ⟨6806761630106422696191793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9075682173475230261589057 6806761630106422696191793)
                ·
                  refine ⟨5105071222579817022143845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6806761630106422696191793 5105071222579817022143845)
                  ·
                    refine ⟨957200854233715691651971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5105071222579817022143845 957200854233715691651971)
                    ·
                      rfl

theorem cell22_2796213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 2, 2, 4].length) (baseStart_2796213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2796213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2796213 prefixEnd_2796213 := by exact prefixLift 2796213
  have htrace : WordTrace (prefixWord ++ tailWord_2796213) baseStart_2796213 baseEnd_2796213 := by
    simpa [prefixWord, tailWord_2796213, baseEnd_2796213] using wordTrace_append hprefix tailTrace_2796213
  have hstable : (prefixWord ++ tailWord_2796213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2796213).length < 2 ^ (prefixWord ++ tailWord_2796213).sum := by decide
  have hdescent : baseEnd_2796213 < baseStart_2796213 := by decide
  rcases family_descends (prefixWord ++ tailWord_2796213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2796215 : List Nat := [1, 1, 3, 1, 6, 1, 2, 2, 2, 3]
def baseStart_2796215 : Nat := 118140960795 + 2796215 * 2 ^ 59
def prefixEnd_2796215 : Nat := 4983230072969 + 3 ^ 40 * 2796215 * 2
def baseEnd_2796215 : Nat := 957201538874588353101965

theorem tailTrace_2796215 : CollatzResearch.WordTrace tailWord_2796215 prefixEnd_2796215 957201538874588353101965 := by
  unfold tailWord_2796215
  simp only [CollatzResearch.WordTrace]
  refine ⟨101986339564798085346974099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67990893043198723564649399 101986339564798085346974099)
  ·
    refine ⟨152979509347197128020461149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101986339564798085346974099 152979509347197128020461149)
    ·
      refine ⟨57367316005198923007672931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 152979509347197128020461149 57367316005198923007672931)
      ·
        refine ⟨86050974007798384511509397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57367316005198923007672931 86050974007798384511509397)
        ·
          refine ⟨4033639406615549273977003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 86050974007798384511509397 4033639406615549273977003)
          ·
            refine ⟨6050459109923323910965505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4033639406615549273977003 6050459109923323910965505)
            ·
              refine ⟨4537844332442492933224129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6050459109923323910965505 4537844332442492933224129)
              ·
                refine ⟨3403383249331869699918097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4537844332442492933224129 3403383249331869699918097)
                ·
                  refine ⟨2552537436998902274938573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3403383249331869699918097 2552537436998902274938573)
                  ·
                    refine ⟨957201538874588353101965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2552537436998902274938573 957201538874588353101965)
                    ·
                      rfl

theorem cell22_2796215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 2, 2, 2, 3].length) (baseStart_2796215 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2796215 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2796215 prefixEnd_2796215 := by exact prefixLift 2796215
  have htrace : WordTrace (prefixWord ++ tailWord_2796215) baseStart_2796215 baseEnd_2796215 := by
    simpa [prefixWord, tailWord_2796215, baseEnd_2796215] using wordTrace_append hprefix tailTrace_2796215
  have hstable : (prefixWord ++ tailWord_2796215).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2796215).length < 2 ^ (prefixWord ++ tailWord_2796215).sum := by decide
  have hdescent : baseEnd_2796215 < baseStart_2796215 := by decide
  rcases family_descends (prefixWord ++ tailWord_2796215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2796228 : List Nat := [2, 3, 3, 1, 1, 4, 1, 7]
def baseStart_2796228 : Nat := 118140960795 + 2796228 * 2 ^ 59
def prefixEnd_2796228 : Nat := 4983230072969 + 3 ^ 40 * 2796228 * 2
def baseEnd_2796228 : Nat := 106356221004473405836325

theorem tailTrace_2796228 : CollatzResearch.WordTrace tailWord_2796228 prefixEnd_2796228 106356221004473405836325 := by
  unfold tailWord_2796228
  simp only [CollatzResearch.WordTrace]
  refine ⟨50993406856875494283598669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67991209142500659044798225 50993406856875494283598669)
  ·
    refine ⟨19122527571328310356349501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50993406856875494283598669 19122527571328310356349501)
    ·
      refine ⟨7170947839248116383631063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19122527571328310356349501 7170947839248116383631063)
      ·
        refine ⟨10756421758872174575446595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7170947839248116383631063 10756421758872174575446595)
        ·
          refine ⟨16134632638308261863169893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10756421758872174575446595 16134632638308261863169893)
          ·
            refine ⟨3025243619682799099344355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16134632638308261863169893 3025243619682799099344355)
            ·
              refine ⟨4537865429524198649016533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3025243619682799099344355 4537865429524198649016533)
              ·
                refine ⟨106356221004473405836325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4537865429524198649016533 106356221004473405836325)
                ·
                  rfl

theorem cell22_2796228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 1, 7].length) (baseStart_2796228 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2796228 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2796228 prefixEnd_2796228 := by exact prefixLift 2796228
  have htrace : WordTrace (prefixWord ++ tailWord_2796228) baseStart_2796228 baseEnd_2796228 := by
    simpa [prefixWord, tailWord_2796228, baseEnd_2796228] using wordTrace_append hprefix tailTrace_2796228
  have hstable : (prefixWord ++ tailWord_2796228).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2796228).length < 2 ^ (prefixWord ++ tailWord_2796228).sum := by decide
  have hdescent : baseEnd_2796228 < baseStart_2796228 := by decide
  rcases family_descends (prefixWord ++ tailWord_2796228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2796239 : List Nat := [1, 1, 2, 1, 1, 3, 1, 1, 11]
def baseStart_2796239 : Nat := 118140960795 + 2796239 * 2 ^ 59
def prefixEnd_2796239 : Nat := 4983230072969 + 3 ^ 40 * 2796239 * 2
def baseEnd_2796239 : Nat := 319069918188353430167297

theorem tailTrace_2796239 : CollatzResearch.WordTrace tailWord_2796239 prefixEnd_2796239 319069918188353430167297 := by
  unfold tailWord_2796239
  simp only [CollatzResearch.WordTrace]
  refine ⟨101987214916711137445847771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67991476611140758297231847 101987214916711137445847771)
  ·
    refine ⟨152980822375066706168771657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101987214916711137445847771 152980822375066706168771657)
    ·
      refine ⟨114735616781300029626578743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152980822375066706168771657 114735616781300029626578743)
      ·
        refine ⟨172103425171950044439868115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114735616781300029626578743 172103425171950044439868115)
        ·
          refine ⟨258155137757925066659802173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172103425171950044439868115 258155137757925066659802173)
          ·
            refine ⟨96808176659221899997425815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 258155137757925066659802173 96808176659221899997425815)
            ·
              refine ⟨145212264988832849996138723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96808176659221899997425815 145212264988832849996138723)
              ·
                refine ⟨217818397483249274994208085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 145212264988832849996138723 217818397483249274994208085)
                ·
                  refine ⟨319069918188353430167297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 217818397483249274994208085 319069918188353430167297)
                  ·
                    rfl

theorem cell22_2796239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 11].length) (baseStart_2796239 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2796239 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2796239 prefixEnd_2796239 := by exact prefixLift 2796239
  have htrace : WordTrace (prefixWord ++ tailWord_2796239) baseStart_2796239 baseEnd_2796239 := by
    simpa [prefixWord, tailWord_2796239, baseEnd_2796239] using wordTrace_append hprefix tailTrace_2796239
  have hstable : (prefixWord ++ tailWord_2796239).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2796239).length < 2 ^ (prefixWord ++ tailWord_2796239).sum := by decide
  have hdescent : baseEnd_2796239 < baseStart_2796239 := by decide
  rcases family_descends (prefixWord ++ tailWord_2796239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2796245 : List Nat := [1, 3, 2, 5, 1, 1, 3, 6]
def baseStart_2796245 : Nat := 118140960795 + 2796245 * 2 ^ 59
def prefixEnd_2796245 : Nat := 4983230072969 + 3 ^ 40 * 2796245 * 2
def baseEnd_2796245 : Nat := 106356867609742030539097

theorem tailTrace_2796245 : CollatzResearch.WordTrace tailWord_2796245 prefixEnd_2796245 106356867609742030539097 := by
  unfold tailWord_2796245
  simp only [CollatzResearch.WordTrace]
  refine ⟨101987433754689400470566189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67991622503126266980377459 101987433754689400470566189)
  ·
    refine ⟨38245287658008525176462321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101987433754689400470566189 38245287658008525176462321)
    ·
      refine ⟨28683965743506393882346741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38245287658008525176462321 28683965743506393882346741)
      ·
        refine ⟨2689121788453724426470007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 28683965743506393882346741 2689121788453724426470007)
        ·
          refine ⟨4033682682680586639705011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2689121788453724426470007 4033682682680586639705011)
          ·
            refine ⟨6050524024020879959557517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4033682682680586639705011 6050524024020879959557517)
            ·
              refine ⟨2268946509007829984834069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6050524024020879959557517 2268946509007829984834069)
              ·
                refine ⟨106356867609742030539097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2268946509007829984834069 106356867609742030539097)
                ·
                  rfl

theorem cell22_2796245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 3, 6].length) (baseStart_2796245 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2796245 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2796245 prefixEnd_2796245 := by exact prefixLift 2796245
  have htrace : WordTrace (prefixWord ++ tailWord_2796245) baseStart_2796245 baseEnd_2796245 := by
    simpa [prefixWord, tailWord_2796245, baseEnd_2796245] using wordTrace_append hprefix tailTrace_2796245
  have hstable : (prefixWord ++ tailWord_2796245).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2796245).length < 2 ^ (prefixWord ++ tailWord_2796245).sum := by decide
  have hdescent : baseEnd_2796245 < baseStart_2796245 := by decide
  rcases family_descends (prefixWord ++ tailWord_2796245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2796260 : List Nat := [2, 3, 1, 1, 1, 4, 1, 5, 1, 3]
def baseStart_2796260 : Nat := 118140960795 + 2796260 * 2 ^ 59
def prefixEnd_2796260 : Nat := 4983230072969 + 3 ^ 40 * 2796260 * 2
def baseEnd_2796260 : Nat := 957216943294223235726827

theorem tailTrace_2796260 : CollatzResearch.WordTrace tailWord_2796260 prefixEnd_2796260 957216943294223235726827 := by
  unfold tailWord_2796260
  simp only [CollatzResearch.WordTrace]
  refine ⟨50993990424817529016181117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67991987233090038688241489 50993990424817529016181117)
  ·
    refine ⟨19122746409306573381067919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50993990424817529016181117 19122746409306573381067919)
    ·
      refine ⟨28684119613959860071601879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19122746409306573381067919 28684119613959860071601879)
      ·
        refine ⟨43026179420939790107402819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28684119613959860071601879 43026179420939790107402819)
        ·
          refine ⟨64539269131409685161104229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43026179420939790107402819 64539269131409685161104229)
          ·
            refine ⟨12101112962139315967707043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64539269131409685161104229 12101112962139315967707043)
            ·
              refine ⟨18151669443208973951560565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12101112962139315967707043 18151669443208973951560565)
              ·
                refine ⟨1701719010300841307958803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18151669443208973951560565 1701719010300841307958803)
                ·
                  refine ⟨2552578515451261961938205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1701719010300841307958803 2552578515451261961938205)
                  ·
                    refine ⟨957216943294223235726827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2552578515451261961938205 957216943294223235726827)
                    ·
                      rfl

theorem cell22_2796260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 5, 1, 3].length) (baseStart_2796260 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2796260 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2796260 prefixEnd_2796260 := by exact prefixLift 2796260
  have htrace : WordTrace (prefixWord ++ tailWord_2796260) baseStart_2796260 baseEnd_2796260 := by
    simpa [prefixWord, tailWord_2796260, baseEnd_2796260] using wordTrace_append hprefix tailTrace_2796260
  have hstable : (prefixWord ++ tailWord_2796260).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2796260).length < 2 ^ (prefixWord ++ tailWord_2796260).sum := by decide
  have hdescent : baseEnd_2796260 < baseStart_2796260 := by decide
  rcases family_descends (prefixWord ++ tailWord_2796260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2796271 : List Nat := [1, 1, 2, 1, 5, 2, 1, 2, 2, 5]
def baseStart_2796271 : Nat := 118140960795 + 2796271 * 2 ^ 59
def prefixEnd_2796271 : Nat := 4983230072969 + 3 ^ 40 * 2796271 * 2
def baseEnd_2796271 : Nat := 957220708819022873701793

theorem tailTrace_2796271 : CollatzResearch.WordTrace tailWord_2796271 prefixEnd_2796271 957220708819022873701793 := by
  unfold tailWord_2796271
  simp only [CollatzResearch.WordTrace]
  refine ⟨101988382052595206911012667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67992254701730137940675111 101988382052595206911012667)
  ·
    refine ⟨152982573078892810366519001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101988382052595206911012667 152982573078892810366519001)
    ·
      refine ⟨114736929809169607774889251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152982573078892810366519001 114736929809169607774889251)
      ·
        refine ⟨172105394713754411662333877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114736929809169607774889251 172105394713754411662333877)
        ·
          refine ⟨16134880754414476093343801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 172105394713754411662333877 16134880754414476093343801)
          ·
            refine ⟨12101160565810857070007851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16134880754414476093343801 12101160565810857070007851)
            ·
              refine ⟨18151740848716285605011777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12101160565810857070007851 18151740848716285605011777)
              ·
                refine ⟨13613805636537214203758833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18151740848716285605011777 13613805636537214203758833)
                ·
                  refine ⟨10210354227402910652819125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13613805636537214203758833 10210354227402910652819125)
                  ·
                    refine ⟨957220708819022873701793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10210354227402910652819125 957220708819022873701793)
                    ·
                      rfl

theorem cell22_2796271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 2, 2, 5].length) (baseStart_2796271 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2796271 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2796271 prefixEnd_2796271 := by exact prefixLift 2796271
  have htrace : WordTrace (prefixWord ++ tailWord_2796271) baseStart_2796271 baseEnd_2796271 := by
    simpa [prefixWord, tailWord_2796271, baseEnd_2796271] using wordTrace_append hprefix tailTrace_2796271
  have hstable : (prefixWord ++ tailWord_2796271).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2796271).length < 2 ^ (prefixWord ++ tailWord_2796271).sum := by decide
  have hdescent : baseEnd_2796271 < baseStart_2796271 := by decide
  rcases family_descends (prefixWord ++ tailWord_2796271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2796303 : List Nat := [1, 1, 2, 1, 1, 1, 8, 2, 1, 4]
def baseStart_2796303 : Nat := 118140960795 + 2796303 * 2 ^ 59
def prefixEnd_2796303 : Nat := 4983230072969 + 3 ^ 40 * 2796303 * 2
def baseEnd_2796303 : Nat := 957231663072985456901695

theorem tailTrace_2796303 : CollatzResearch.WordTrace tailWord_2796303 prefixEnd_2796303 957231663072985456901695 := by
  unfold tailWord_2796303
  simp only [CollatzResearch.WordTrace]
  refine ⟨101989549188479276376177563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67993032792319517584118375 101989549188479276376177563)
  ·
    refine ⟨152984323782718914564266345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101989549188479276376177563 152984323782718914564266345)
    ·
      refine ⟨114738242837039185923199759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152984323782718914564266345 114738242837039185923199759)
      ·
        refine ⟨172107364255558778884799639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114738242837039185923199759 172107364255558778884799639)
        ·
          refine ⟨258161046383338168327199459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172107364255558778884799639 258161046383338168327199459)
          ·
            refine ⟨387241569575007252490799189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 258161046383338168327199459 387241569575007252490799189)
            ·
              refine ⟨4537987143457116240126553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 387241569575007252490799189 4537987143457116240126553)
              ·
                refine ⟨3403490357592837180094915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4537987143457116240126553 3403490357592837180094915)
                ·
                  refine ⟨5105235536389255770142373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3403490357592837180094915 5105235536389255770142373)
                  ·
                    refine ⟨957231663072985456901695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5105235536389255770142373 957231663072985456901695)
                    ·
                      rfl

theorem cell22_2796303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 8, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 8, 2, 1, 4].length) (baseStart_2796303 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2796303 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2796303 prefixEnd_2796303 := by exact prefixLift 2796303
  have htrace : WordTrace (prefixWord ++ tailWord_2796303) baseStart_2796303 baseEnd_2796303 := by
    simpa [prefixWord, tailWord_2796303, baseEnd_2796303] using wordTrace_append hprefix tailTrace_2796303
  have hstable : (prefixWord ++ tailWord_2796303).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2796303).length < 2 ^ (prefixWord ++ tailWord_2796303).sum := by decide
  have hdescent : baseEnd_2796303 < baseStart_2796303 := by decide
  rcases family_descends (prefixWord ++ tailWord_2796303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2796331 : List Nat := [1, 1, 1, 1, 2, 1, 2, 5, 4, 4]
def baseStart_2796331 : Nat := 118140960795 + 2796331 * 2 ^ 59
def prefixEnd_2796331 : Nat := 4983230072969 + 3 ^ 40 * 2796331 * 2
def baseEnd_2796331 : Nat := 957241248045202717201609

theorem tailTrace_2796331 : CollatzResearch.WordTrace tailWord_2796331 prefixEnd_2796331 957241248045202717201609 := by
  unfold tailWord_2796331
  simp only [CollatzResearch.WordTrace]
  refine ⟨101990570432377837158196847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67993713621585224772131231 101990570432377837158196847)
  ·
    refine ⟨152985855648566755737295271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101990570432377837158196847 152985855648566755737295271)
    ·
      refine ⟨229478783472850133605942907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152985855648566755737295271 229478783472850133605942907)
      ·
        refine ⟨344218175209275200408914361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 229478783472850133605942907 344218175209275200408914361)
        ·
          refine ⟨258163631406956400306685771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 344218175209275200408914361 258163631406956400306685771)
          ·
            refine ⟨387245447110434600460028657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 258163631406956400306685771 387245447110434600460028657)
            ·
              refine ⟨290434085332825950345021493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 387245447110434600460028657 290434085332825950345021493)
              ·
                refine ⟨27228195499952432844845765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 290434085332825950345021493 27228195499952432844845765)
                ·
                  refine ⟨5105286656241081158408581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27228195499952432844845765 5105286656241081158408581)
                  ·
                    refine ⟨957241248045202717201609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5105286656241081158408581 957241248045202717201609)
                    ·
                      rfl

theorem cell22_2796331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 5, 4, 4].length) (baseStart_2796331 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2796331 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2796331 prefixEnd_2796331 := by exact prefixLift 2796331
  have htrace : WordTrace (prefixWord ++ tailWord_2796331) baseStart_2796331 baseEnd_2796331 := by
    simpa [prefixWord, tailWord_2796331, baseEnd_2796331] using wordTrace_append hprefix tailTrace_2796331
  have hstable : (prefixWord ++ tailWord_2796331).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2796331).length < 2 ^ (prefixWord ++ tailWord_2796331).sum := by decide
  have hdescent : baseEnd_2796331 < baseStart_2796331 := by decide
  rcases family_descends (prefixWord ++ tailWord_2796331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2796376 : List Nat := [2, 1, 2, 2, 1, 1, 1, 2, 4, 6]
def baseStart_2796376 : Nat := 118140960795 + 2796376 * 2 ^ 59
def prefixEnd_2796376 : Nat := 4983230072969 + 3 ^ 40 * 2796376 * 2
def baseEnd_2796376 : Nat := 957256652464837599826471

theorem tailTrace_2796376 : CollatzResearch.WordTrace tailWord_2796376 prefixEnd_2796376 957256652464837599826471 := by
  unfold tailWord_2796376
  simp only [CollatzResearch.WordTrace]
  refine ⟨50996105858607404921792491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67994807811476539895723321 50996105858607404921792491)
  ·
    refine ⟨76494158787911107382688737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50996105858607404921792491 76494158787911107382688737)
    ·
      refine ⟨57370619090933330537016553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76494158787911107382688737 57370619090933330537016553)
      ·
        refine ⟨43027964318199997902762415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57370619090933330537016553 43027964318199997902762415)
        ·
          refine ⟨64541946477299996854143623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43027964318199997902762415 64541946477299996854143623)
          ·
            refine ⟨96812919715949995281215435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64541946477299996854143623 96812919715949995281215435)
            ·
              refine ⟨145219379573924992921823153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96812919715949995281215435 145219379573924992921823153)
              ·
                refine ⟨108914534680443744691367365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 145219379573924992921823153 108914534680443744691367365)
                ·
                  refine ⟨20421475252583202129631381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 108914534680443744691367365 20421475252583202129631381)
                  ·
                    refine ⟨957256652464837599826471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20421475252583202129631381 957256652464837599826471)
                    ·
                      rfl

theorem cell22_2796376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 4, 6].length) (baseStart_2796376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2796376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2796376 prefixEnd_2796376 := by exact prefixLift 2796376
  have htrace : WordTrace (prefixWord ++ tailWord_2796376) baseStart_2796376 baseEnd_2796376 := by
    simpa [prefixWord, tailWord_2796376, baseEnd_2796376] using wordTrace_append hprefix tailTrace_2796376
  have hstable : (prefixWord ++ tailWord_2796376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2796376).length < 2 ^ (prefixWord ++ tailWord_2796376).sum := by decide
  have hdescent : baseEnd_2796376 < baseStart_2796376 := by decide
  rcases family_descends (prefixWord ++ tailWord_2796376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2796386 : List Nat := [3, 3, 2, 1, 4, 1, 2, 2, 4]
def baseStart_2796386 : Nat := 118140960795 + 2796386 * 2 ^ 59
def prefixEnd_2796386 : Nat := 4983230072969 + 3 ^ 40 * 2796386 * 2
def baseEnd_2796386 : Nat := 319086691889733635692147

theorem tailTrace_2796386 : CollatzResearch.WordTrace tailWord_2796386 prefixEnd_2796386 319086691889733635692147 := by
  unfold tailWord_2796386
  simp only [CollatzResearch.WordTrace]
  refine ⟨25498144111794645387862253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67995050964785721034299341 25498144111794645387862253)
  ·
    refine ⟨9561804041922992020448345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25498144111794645387862253 9561804041922992020448345)
    ·
      refine ⟨7171353031442244015336259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9561804041922992020448345 7171353031442244015336259)
      ·
        refine ⟨10757029547163366023004389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7171353031442244015336259 10757029547163366023004389)
        ·
          refine ⟨2016943040093131129313323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10757029547163366023004389 2016943040093131129313323)
          ·
            refine ⟨3025414560139696693969985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2016943040093131129313323 3025414560139696693969985)
            ·
              refine ⟨2269060920104772520477489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3025414560139696693969985 2269060920104772520477489)
              ·
                refine ⟨1701795690078579390358117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2269060920104772520477489 1701795690078579390358117)
                ·
                  refine ⟨319086691889733635692147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1701795690078579390358117 319086691889733635692147)
                  ·
                    rfl

theorem cell22_2796386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 2, 2, 4].length) (baseStart_2796386 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2796386 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2796386 prefixEnd_2796386 := by exact prefixLift 2796386
  have htrace : WordTrace (prefixWord ++ tailWord_2796386) baseStart_2796386 baseEnd_2796386 := by
    simpa [prefixWord, tailWord_2796386, baseEnd_2796386] using wordTrace_append hprefix tailTrace_2796386
  have hstable : (prefixWord ++ tailWord_2796386).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2796386).length < 2 ^ (prefixWord ++ tailWord_2796386).sum := by decide
  have hdescent : baseEnd_2796386 < baseStart_2796386 := by decide
  rcases family_descends (prefixWord ++ tailWord_2796386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2796442 : List Nat := [3, 1, 1, 4, 3, 2, 1, 2, 5]
def baseStart_2796442 : Nat := 118140960795 + 2796442 * 2 ^ 59
def prefixEnd_2796442 : Nat := 4983230072969 + 3 ^ 40 * 2796442 * 2
def baseEnd_2796442 : Nat := 319093081871211809225423

theorem tailTrace_2796442 : CollatzResearch.WordTrace tailWord_2796442 prefixEnd_2796442 319093081871211809225423 := by
  unfold tailWord_2796442
  simp only [CollatzResearch.WordTrace]
  refine ⟨25498654733743925778871895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67996412623317135410325053 25498654733743925778871895)
  ·
    refine ⟨38247982100615888668307843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25498654733743925778871895 38247982100615888668307843)
    ·
      refine ⟨57371973150923833002461765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38247982100615888668307843 57371973150923833002461765)
      ·
        refine ⟨10757244965798218687961581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57371973150923833002461765 10757244965798218687961581)
        ·
          refine ⟨4033966862174332007985593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10757244965798218687961581 4033966862174332007985593)
          ·
            refine ⟨3025475146630749005989195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4033966862174332007985593 3025475146630749005989195)
            ·
              refine ⟨4538212719946123508983793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3025475146630749005989195 4538212719946123508983793)
              ·
                refine ⟨3403659539959592631737845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4538212719946123508983793 3403659539959592631737845)
                ·
                  refine ⟨319093081871211809225423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3403659539959592631737845 319093081871211809225423)
                  ·
                    rfl

theorem cell22_2796442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 1, 2, 5].length) (baseStart_2796442 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2796442 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2796442 prefixEnd_2796442 := by exact prefixLift 2796442
  have htrace : WordTrace (prefixWord ++ tailWord_2796442) baseStart_2796442 baseEnd_2796442 := by
    simpa [prefixWord, tailWord_2796442, baseEnd_2796442] using wordTrace_append hprefix tailTrace_2796442
  have hstable : (prefixWord ++ tailWord_2796442).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2796442).length < 2 ^ (prefixWord ++ tailWord_2796442).sum := by decide
  have hdescent : baseEnd_2796442 < baseStart_2796442 := by decide
  rcases family_descends (prefixWord ++ tailWord_2796442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2796500 : List Nat := [2, 4, 1, 2, 1, 2, 1, 1, 4, 4]
def baseStart_2796500 : Nat := 118140960795 + 2796500 * 2 ^ 59
def prefixEnd_2796500 : Nat := 4983230072969 + 3 ^ 40 * 2796500 * 2
def baseEnd_2796500 : Nat := 957299100198942609726091

theorem tailTrace_2796500 : CollatzResearch.WordTrace tailWord_2796500 prefixEnd_2796500 957299100198942609726091 := by
  unfold tailWord_2796500
  simp only [CollatzResearch.WordTrace]
  refine ⟨50998367184382789510549477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67997822912510386014065969 50998367184382789510549477)
  ·
    refine ⟨9562193847071773033228027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50998367184382789510549477 9562193847071773033228027)
    ·
      refine ⟨14343290770607659549842041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9562193847071773033228027 14343290770607659549842041)
      ·
        refine ⟨10757468077955744662381531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14343290770607659549842041 10757468077955744662381531)
        ·
          refine ⟨16136202116933616993572297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10757468077955744662381531 16136202116933616993572297)
          ·
            refine ⟨12102151587700212745179223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16136202116933616993572297 12102151587700212745179223)
            ·
              refine ⟨18153227381550319117768835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12102151587700212745179223 18153227381550319117768835)
              ·
                refine ⟨27229841072325478676653253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18153227381550319117768835 27229841072325478676653253)
                ·
                  refine ⟨5105595201061027251872485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27229841072325478676653253 5105595201061027251872485)
                  ·
                    refine ⟨957299100198942609726091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5105595201061027251872485 957299100198942609726091)
                    ·
                      rfl

theorem cell22_2796500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 1, 4, 4].length) (baseStart_2796500 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2796500 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2796500 prefixEnd_2796500 := by exact prefixLift 2796500
  have htrace : WordTrace (prefixWord ++ tailWord_2796500) baseStart_2796500 baseEnd_2796500 := by
    simpa [prefixWord, tailWord_2796500, baseEnd_2796500] using wordTrace_append hprefix tailTrace_2796500
  have hstable : (prefixWord ++ tailWord_2796500).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2796500).length < 2 ^ (prefixWord ++ tailWord_2796500).sum := by decide
  have hdescent : baseEnd_2796500 < baseStart_2796500 := by decide
  rcases family_descends (prefixWord ++ tailWord_2796500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2796519 : List Nat := [1, 1, 5, 2, 2, 1, 4, 1, 2, 3]
def baseStart_2796519 : Nat := 118140960795 + 2796519 * 2 ^ 59
def prefixEnd_2796519 : Nat := 4983230072969 + 3 ^ 40 * 2796519 * 2
def baseEnd_2796519 : Nat := 957305604287232893501033

theorem tailTrace_2796519 : CollatzResearch.WordTrace tailWord_2796519 prefixEnd_2796519 957305604287232893501033 := by
  unfold tailWord_2796519
  simp only [CollatzResearch.WordTrace]
  refine ⟨101997427355696745266040611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67998284903797830177360407 101997427355696745266040611)
  ·
    refine ⟨152996141033545117899060917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101997427355696745266040611 152996141033545117899060917)
    ·
      refine ⟨14343388221894854803036961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 152996141033545117899060917 14343388221894854803036961)
      ·
        refine ⟨10757541166421141102277721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14343388221894854803036961 10757541166421141102277721)
        ·
          refine ⟨8068155874815855826708291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10757541166421141102277721 8068155874815855826708291)
          ·
            refine ⟨12102233812223783740062437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8068155874815855826708291 12102233812223783740062437)
            ·
              refine ⟨2269168839791959451261707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12102233812223783740062437 2269168839791959451261707)
              ·
                refine ⟨3403753259687939176892561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2269168839791959451261707 3403753259687939176892561)
                ·
                  refine ⟨2552814944765954382669421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3403753259687939176892561 2552814944765954382669421)
                  ·
                    refine ⟨957305604287232893501033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2552814944765954382669421 957305604287232893501033)
                    ·
                      rfl

theorem cell22_2796519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 4, 1, 2, 3].length) (baseStart_2796519 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2796519 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2796519 prefixEnd_2796519 := by exact prefixLift 2796519
  have htrace : WordTrace (prefixWord ++ tailWord_2796519) baseStart_2796519 baseEnd_2796519 := by
    simpa [prefixWord, tailWord_2796519, baseEnd_2796519] using wordTrace_append hprefix tailTrace_2796519
  have hstable : (prefixWord ++ tailWord_2796519).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2796519).length < 2 ^ (prefixWord ++ tailWord_2796519).sum := by decide
  have hdescent : baseEnd_2796519 < baseStart_2796519 := by decide
  rcases family_descends (prefixWord ++ tailWord_2796519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2796575 : List Nat := [1, 1, 2, 4, 1, 4, 1, 1, 2, 5]
def baseStart_2796575 : Nat := 118140960795 + 2796575 * 2 ^ 59
def prefixEnd_2796575 : Nat := 4983230072969 + 3 ^ 40 * 2796575 * 2
def baseEnd_2796575 : Nat := 957324774231667414100861

theorem tailTrace_2796575 : CollatzResearch.WordTrace tailWord_2796575 prefixEnd_2796575 957324774231667414100861 := by
  unfold tailWord_2796575
  simp only [CollatzResearch.WordTrace]
  refine ⟨101999469843493866830079179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67999646562329244553386119 101999469843493866830079179)
  ·
    refine ⟨152999204765240800245118769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101999469843493866830079179 152999204765240800245118769)
    ·
      refine ⟨114749403573930600183839077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152999204765240800245118769 114749403573930600183839077)
      ·
        refine ⟨21515513170111987534469827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 114749403573930600183839077 21515513170111987534469827)
        ·
          refine ⟨32273269755167981301704741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21515513170111987534469827 32273269755167981301704741)
          ·
            refine ⟨6051238079093996494069639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32273269755167981301704741 6051238079093996494069639)
            ·
              refine ⟨9076857118640994741104459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6051238079093996494069639 9076857118640994741104459)
              ·
                refine ⟨13615285677961492111656689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9076857118640994741104459 13615285677961492111656689)
                ·
                  refine ⟨10211464258471119083742517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13615285677961492111656689 10211464258471119083742517)
                  ·
                    refine ⟨957324774231667414100861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10211464258471119083742517 957324774231667414100861)
                    ·
                      rfl

theorem cell22_2796575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 1, 2, 5].length) (baseStart_2796575 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2796575 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2796575 prefixEnd_2796575 := by exact prefixLift 2796575
  have htrace : WordTrace (prefixWord ++ tailWord_2796575) baseStart_2796575 baseEnd_2796575 := by
    simpa [prefixWord, tailWord_2796575, baseEnd_2796575] using wordTrace_append hprefix tailTrace_2796575
  have hstable : (prefixWord ++ tailWord_2796575).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2796575).length < 2 ^ (prefixWord ++ tailWord_2796575).sum := by decide
  have hdescent : baseEnd_2796575 < baseStart_2796575 := by decide
  rcases family_descends (prefixWord ++ tailWord_2796575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2796622 : List Nat := [4, 1, 1, 1, 1, 3, 1, 6, 4]
def baseStart_2796622 : Nat := 118140960795 + 2796622 * 2 ^ 59
def prefixEnd_2796622 : Nat := 4983230072969 + 3 ^ 40 * 2796622 * 2
def baseEnd_2796622 : Nat := 319113621097391652725239

theorem tailTrace_2796622 : CollatzResearch.WordTrace tailWord_2796622 prefixEnd_2796622 319113621097391652725239 := by
  unfold tailWord_2796622
  simp only [CollatzResearch.WordTrace]
  refine ⟨12750148009290449232130015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68000789382882395904693413 12750148009290449232130015)
  ·
    refine ⟨19125222013935673848195023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12750148009290449232130015 19125222013935673848195023)
    ·
      refine ⟨28687833020903510772292535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19125222013935673848195023 28687833020903510772292535)
      ·
        refine ⟨43031749531355266158438803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28687833020903510772292535 43031749531355266158438803)
        ·
          refine ⟨64547624297032899237658205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43031749531355266158438803 64547624297032899237658205)
          ·
            refine ⟨24205359111387337214121827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64547624297032899237658205 24205359111387337214121827)
            ·
              refine ⟨36308038667081005821182741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24205359111387337214121827 36308038667081005821182741)
              ·
                refine ⟨1701939312519422147867941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 36308038667081005821182741 1701939312519422147867941)
                ·
                  refine ⟨319113621097391652725239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1701939312519422147867941 319113621097391652725239)
                  ·
                    rfl

theorem cell22_2796622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 6, 4].length) (baseStart_2796622 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2796622 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2796622 prefixEnd_2796622 := by exact prefixLift 2796622
  have htrace : WordTrace (prefixWord ++ tailWord_2796622) baseStart_2796622 baseEnd_2796622 := by
    simpa [prefixWord, tailWord_2796622, baseEnd_2796622] using wordTrace_append hprefix tailTrace_2796622
  have hstable : (prefixWord ++ tailWord_2796622).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2796622).length < 2 ^ (prefixWord ++ tailWord_2796622).sum := by decide
  have hdescent : baseEnd_2796622 < baseStart_2796622 := by decide
  rcases family_descends (prefixWord ++ tailWord_2796622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2796755 : List Nat := [1, 1, 1, 2, 1, 1, 1, 4, 5, 5]
def baseStart_2796755 : Nat := 118140960795 + 2796755 * 2 ^ 59
def prefixEnd_2796755 : Nat := 4983230072969 + 3 ^ 40 * 2796755 * 2
def baseEnd_2796755 : Nat := 957386391910206944600309

theorem tailTrace_2796755 : CollatzResearch.WordTrace tailWord_2796755 prefixEnd_2796755 957386391910206944600309 := by
  unfold tailWord_2796755
  simp only [CollatzResearch.WordTrace]
  refine ⟨102006034982841757571631719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68004023321894505047754479 102006034982841757571631719)
  ·
    refine ⟨153009052474262636357447579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102006034982841757571631719 153009052474262636357447579)
    ·
      refine ⟨229513578711393954536171369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153009052474262636357447579 229513578711393954536171369)
      ·
        refine ⟨172135184033545465902128527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 229513578711393954536171369 172135184033545465902128527)
        ·
          refine ⟨258202776050318198853192791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172135184033545465902128527 258202776050318198853192791)
          ·
            refine ⟨387304164075477298279789187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 258202776050318198853192791 387304164075477298279789187)
            ·
              refine ⟨580956246113215947419683781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 387304164075477298279789187 580956246113215947419683781)
              ·
                refine ⟨108929296146227990141190709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 580956246113215947419683781 108929296146227990141190709)
                ·
                  refine ⟨10212121513708874075736629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 108929296146227990141190709 10212121513708874075736629)
                  ·
                    refine ⟨957386391910206944600309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10212121513708874075736629 957386391910206944600309)
                    ·
                      rfl

theorem cell22_2796755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 5, 5].length) (baseStart_2796755 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2796755 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2796755 prefixEnd_2796755 := by exact prefixLift 2796755
  have htrace : WordTrace (prefixWord ++ tailWord_2796755) baseStart_2796755 baseEnd_2796755 := by
    simpa [prefixWord, tailWord_2796755, baseEnd_2796755] using wordTrace_append hprefix tailTrace_2796755
  have hstable : (prefixWord ++ tailWord_2796755).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2796755).length < 2 ^ (prefixWord ++ tailWord_2796755).sum := by decide
  have hdescent : baseEnd_2796755 < baseStart_2796755 := by decide
  rcases family_descends (prefixWord ++ tailWord_2796755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2796757 : List Nat := [1, 3, 2, 4, 1, 1, 1, 1, 8]
def baseStart_2796757 : Nat := 118140960795 + 2796757 * 2 ^ 59
def prefixEnd_2796757 : Nat := 4983230072969 + 3 ^ 40 * 2796757 * 2
def baseEnd_2796757 : Nat := 319129025517026535350101

theorem tailTrace_2796757 : CollatzResearch.WordTrace tailWord_2796757 prefixEnd_2796757 319129025517026535350101 := by
  unfold tailWord_2796757
  simp only [CollatzResearch.WordTrace]
  refine ⟨102006107928834511913204525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68004071952556341275469683 102006107928834511913204525)
  ·
    refine ⟨38252290473312941967451697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102006107928834511913204525 38252290473312941967451697)
    ·
      refine ⟨28689217854984706475588773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38252290473312941967451697 28689217854984706475588773)
      ·
        refine ⟨5379228347809632464172895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28689217854984706475588773 5379228347809632464172895)
        ·
          refine ⟨8068842521714448696259343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5379228347809632464172895 8068842521714448696259343)
          ·
            refine ⟨12103263782571673044389015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8068842521714448696259343 12103263782571673044389015)
            ·
              refine ⟨18154895673857509566583523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12103263782571673044389015 18154895673857509566583523)
              ·
                refine ⟨27232343510786264349875285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18154895673857509566583523 27232343510786264349875285)
                ·
                  refine ⟨319129025517026535350101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27232343510786264349875285 319129025517026535350101)
                  ·
                    rfl

theorem cell22_2796757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 1, 8].length) (baseStart_2796757 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2796757 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2796757 prefixEnd_2796757 := by exact prefixLift 2796757
  have htrace : WordTrace (prefixWord ++ tailWord_2796757) baseStart_2796757 baseEnd_2796757 := by
    simpa [prefixWord, tailWord_2796757, baseEnd_2796757] using wordTrace_append hprefix tailTrace_2796757
  have hstable : (prefixWord ++ tailWord_2796757).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2796757).length < 2 ^ (prefixWord ++ tailWord_2796757).sum := by decide
  have hdescent : baseEnd_2796757 < baseStart_2796757 := by decide
  rcases family_descends (prefixWord ++ tailWord_2796757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2796772 : List Nat := [2, 3, 1, 1, 1, 2, 4, 2, 1, 5]
def baseStart_2796772 : Nat := 118140960795 + 2796772 * 2 ^ 59
def prefixEnd_2796772 : Nat := 4983230072969 + 3 ^ 40 * 2796772 * 2
def baseEnd_2796772 : Nat := 957392211357624566925257

theorem tailTrace_2796772 : CollatzResearch.WordTrace tailWord_2796772 prefixEnd_2796772 957392211357624566925257 := by
  unfold tailWord_2796772
  simp only [CollatzResearch.WordTrace]
  refine ⟨51003327511890084737500285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68004436682520112983333713 51003327511890084737500285)
  ·
    refine ⟨19126247816958781776562607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51003327511890084737500285 19126247816958781776562607)
    ·
      refine ⟨28689371725438172664843911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19126247816958781776562607 28689371725438172664843911)
      ·
        refine ⟨43034057588157258997265867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28689371725438172664843911 43034057588157258997265867)
        ·
          refine ⟨64551086382235888495898801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43034057588157258997265867 64551086382235888495898801)
          ·
            refine ⟨48413314786676916371924101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64551086382235888495898801 48413314786676916371924101)
            ·
              refine ⟨9077496522501921819735769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48413314786676916371924101 9077496522501921819735769)
              ·
                refine ⟨6808122391876441364801827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9077496522501921819735769 6808122391876441364801827)
                ·
                  refine ⟨10212183587814662047202741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6808122391876441364801827 10212183587814662047202741)
                  ·
                    refine ⟨957392211357624566925257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10212183587814662047202741 957392211357624566925257)
                    ·
                      rfl

theorem cell22_2796772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 2, 1, 5].length) (baseStart_2796772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2796772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2796772 prefixEnd_2796772 := by exact prefixLift 2796772
  have htrace : WordTrace (prefixWord ++ tailWord_2796772) baseStart_2796772 baseEnd_2796772 := by
    simpa [prefixWord, tailWord_2796772, baseEnd_2796772] using wordTrace_append hprefix tailTrace_2796772
  have hstable : (prefixWord ++ tailWord_2796772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2796772).length < 2 ^ (prefixWord ++ tailWord_2796772).sum := by decide
  have hdescent : baseEnd_2796772 < baseStart_2796772 := by decide
  rcases family_descends (prefixWord ++ tailWord_2796772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2796847 : List Nat := [1, 1, 2, 1, 2, 1, 3, 6, 5]
def baseStart_2796847 : Nat := 118140960795 + 2796847 * 2 ^ 59
def prefixEnd_2796847 : Nat := 4983230072969 + 3 ^ 40 * 2796847 * 2
def baseEnd_2796847 : Nat := 319139295130116457100009

theorem tailTrace_2796847 : CollatzResearch.WordTrace tailWord_2796847 prefixEnd_2796847 319139295130116457100009 := by
  unfold tailWord_2796847
  simp only [CollatzResearch.WordTrace]
  refine ⟨102009390498508457283980795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68006260332338971522653863 102009390498508457283980795)
  ·
    refine ⟨153014085747762685925971193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102009390498508457283980795 153014085747762685925971193)
    ·
      refine ⟨114760564310822014444478395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153014085747762685925971193 114760564310822014444478395)
      ·
        refine ⟨172140846466233021666717593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114760564310822014444478395 172140846466233021666717593)
        ·
          refine ⟨129105634849674766250038195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 172140846466233021666717593 129105634849674766250038195)
          ·
            refine ⟨193658452274512149375057293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129105634849674766250038195 193658452274512149375057293)
            ·
              refine ⟨72621919602942056015646485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 193658452274512149375057293 72621919602942056015646485)
              ·
                refine ⟨3404152481387908875733429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 72621919602942056015646485 3404152481387908875733429)
                ·
                  refine ⟨319139295130116457100009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3404152481387908875733429 319139295130116457100009)
                  ·
                    rfl

theorem cell22_2796847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 6, 5].length) (baseStart_2796847 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2796847 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2796847 prefixEnd_2796847 := by exact prefixLift 2796847
  have htrace : WordTrace (prefixWord ++ tailWord_2796847) baseStart_2796847 baseEnd_2796847 := by
    simpa [prefixWord, tailWord_2796847, baseEnd_2796847] using wordTrace_append hprefix tailTrace_2796847
  have hstable : (prefixWord ++ tailWord_2796847).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2796847).length < 2 ^ (prefixWord ++ tailWord_2796847).sum := by decide
  have hdescent : baseEnd_2796847 < baseStart_2796847 := by decide
  rcases family_descends (prefixWord ++ tailWord_2796847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2796851 : List Nat := [1, 1, 1, 2, 5, 4, 1, 1, 3, 3]
def baseStart_2796851 : Nat := 118140960795 + 2796851 * 2 ^ 59
def prefixEnd_2796851 : Nat := 4983230072969 + 3 ^ 40 * 2796851 * 2
def baseEnd_2796851 : Nat := 957419254672094694200015

theorem tailTrace_2796851 : CollatzResearch.WordTrace tailWord_2796851 prefixEnd_2796851 957419254672094694200015 := by
  unfold tailWord_2796851
  simp only [CollatzResearch.WordTrace]
  refine ⟨102009536390493965967126407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68006357593662643978084271 102009536390493965967126407)
  ·
    refine ⟨153014304585740948950689611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102009536390493965967126407 153014304585740948950689611)
    ·
      refine ⟨229521456878611423426034417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153014304585740948950689611 229521456878611423426034417)
      ·
        refine ⟨172141092658958567569525813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 229521456878611423426034417 172141092658958567569525813)
        ·
          refine ⟨16138227436777365709643045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 172141092658958567569525813 16138227436777365709643045)
          ·
            refine ⟨3025917644395756070558071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16138227436777365709643045 3025917644395756070558071)
            ·
              refine ⟨4538876466593634105837107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3025917644395756070558071 4538876466593634105837107)
              ·
                refine ⟨6808314699890451158755661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4538876466593634105837107 6808314699890451158755661)
                ·
                  refine ⟨2553118012458919184533373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6808314699890451158755661 2553118012458919184533373)
                  ·
                    refine ⟨957419254672094694200015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2553118012458919184533373 957419254672094694200015)
                    ·
                      rfl

theorem cell22_2796851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 1, 1, 3, 3].length) (baseStart_2796851 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2796851 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2796851 prefixEnd_2796851 := by exact prefixLift 2796851
  have htrace : WordTrace (prefixWord ++ tailWord_2796851) baseStart_2796851 baseEnd_2796851 := by
    simpa [prefixWord, tailWord_2796851, baseEnd_2796851] using wordTrace_append hprefix tailTrace_2796851
  have hstable : (prefixWord ++ tailWord_2796851).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2796851).length < 2 ^ (prefixWord ++ tailWord_2796851).sum := by decide
  have hdescent : baseEnd_2796851 < baseStart_2796851 := by decide
  rcases family_descends (prefixWord ++ tailWord_2796851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2796922 : List Nat := [3, 1, 1, 1, 1, 1, 2, 3, 3, 6]
def baseStart_2796922 : Nat := 118140960795 + 2796922 * 2 ^ 59
def prefixEnd_2796922 : Nat := 4983230072969 + 3 ^ 40 * 2796922 * 2
def baseEnd_2796922 : Nat := 957443559423074175674797

theorem tailTrace_2796922 : CollatzResearch.WordTrace tailWord_2796922 prefixEnd_2796922 957443559423074175674797 := by
  unfold tailWord_2796922
  simp only [CollatzResearch.WordTrace]
  refine ⟨25503031493309186273240255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68008083982157830061974013 25503031493309186273240255)
  ·
    refine ⟨38254547239963779409860383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25503031493309186273240255 38254547239963779409860383)
    ·
      refine ⟨57381820859945669114790575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38254547239963779409860383 57381820859945669114790575)
      ·
        refine ⟨86072731289918503672185863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57381820859945669114790575 86072731289918503672185863)
        ·
          refine ⟨129109096934877755508278795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86072731289918503672185863 129109096934877755508278795)
          ·
            refine ⟨193663645402316633262418193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129109096934877755508278795 193663645402316633262418193)
            ·
              refine ⟨145247734051737474946813645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 193663645402316633262418193 145247734051737474946813645)
              ·
                refine ⟨54467900269401553105055117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 145247734051737474946813645 54467900269401553105055117)
                ·
                  refine ⟨20425462601025582414395669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54467900269401553105055117 20425462601025582414395669)
                  ·
                    refine ⟨957443559423074175674797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20425462601025582414395669 957443559423074175674797)
                    ·
                      rfl

theorem cell22_2796922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 3, 3, 6].length) (baseStart_2796922 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2796922 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2796922 prefixEnd_2796922 := by exact prefixLift 2796922
  have htrace : WordTrace (prefixWord ++ tailWord_2796922) baseStart_2796922 baseEnd_2796922 := by
    simpa [prefixWord, tailWord_2796922, baseEnd_2796922] using wordTrace_append hprefix tailTrace_2796922
  have hstable : (prefixWord ++ tailWord_2796922).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2796922).length < 2 ^ (prefixWord ++ tailWord_2796922).sum := by decide
  have hdescent : baseEnd_2796922 < baseStart_2796922 := by decide
  rcases family_descends (prefixWord ++ tailWord_2796922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2796924 : List Nat := [2, 2, 2, 1, 1, 1, 6, 1, 1, 5]
def baseStart_2796924 : Nat := 118140960795 + 2796924 * 2 ^ 59
def prefixEnd_2796924 : Nat := 4983230072969 + 3 ^ 40 * 2796924 * 2
def baseEnd_2796924 : Nat := 957444244063946837124791

theorem tailTrace_2796924 : CollatzResearch.WordTrace tailWord_2796924 prefixEnd_2796924 957444244063946837124791 := by
  unfold tailWord_2796924
  simp only [CollatzResearch.WordTrace]
  refine ⟨51006099459614749717266913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68008132612819666289689217 51006099459614749717266913)
  ·
    refine ⟨38254574594711062287950185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51006099459614749717266913 38254574594711062287950185)
    ·
      refine ⟨28690930946033296715962639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38254574594711062287950185 28690930946033296715962639)
      ·
        refine ⟨43036396419049945073943959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28690930946033296715962639 43036396419049945073943959)
        ·
          refine ⟨64554594628574917610915939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43036396419049945073943959 64554594628574917610915939)
          ·
            refine ⟨96831891942862376416373909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64554594628574917610915939 96831891942862376416373909)
            ·
              refine ⟨4538994934821673894517527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 96831891942862376416373909 4538994934821673894517527)
              ·
                refine ⟨6808492402232510841776291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4538994934821673894517527 6808492402232510841776291)
                ·
                  refine ⟨10212738603348766262664437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6808492402232510841776291 10212738603348766262664437)
                  ·
                    refine ⟨957444244063946837124791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10212738603348766262664437 957444244063946837124791)
                    ·
                      rfl

theorem cell22_2796924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 6, 1, 1, 5].length) (baseStart_2796924 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2796924 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2796924 prefixEnd_2796924 := by exact prefixLift 2796924
  have htrace : WordTrace (prefixWord ++ tailWord_2796924) baseStart_2796924 baseEnd_2796924 := by
    simpa [prefixWord, tailWord_2796924, baseEnd_2796924] using wordTrace_append hprefix tailTrace_2796924
  have hstable : (prefixWord ++ tailWord_2796924).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2796924).length < 2 ^ (prefixWord ++ tailWord_2796924).sum := by decide
  have hdescent : baseEnd_2796924 < baseStart_2796924 := by decide
  rcases family_descends (prefixWord ++ tailWord_2796924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2796988 : List Nat := [2, 2, 2, 4, 2, 2, 2, 6]
def baseStart_2796988 : Nat := 118140960795 + 2796988 * 2 ^ 59
def prefixEnd_2796988 : Nat := 4983230072969 + 3 ^ 40 * 2796988 * 2
def baseEnd_2796988 : Nat := 106385128063541333724955

theorem tailTrace_2796988 : CollatzResearch.WordTrace tailWord_2796988 prefixEnd_2796988 106385128063541333724955 := by
  unfold tailWord_2796988
  simp only [CollatzResearch.WordTrace]
  refine ⟨51007266595498819182431809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68009688793998425576575745 51007266595498819182431809)
  ·
    refine ⟨38255449946624114386823857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51007266595498819182431809 38255449946624114386823857)
    ·
      refine ⟨28691587459968085790117893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38255449946624114386823857 28691587459968085790117893)
      ·
        refine ⟨5379672648744016085647105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28691587459968085790117893 5379672648744016085647105)
        ·
          refine ⟨4034754486558012064235329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5379672648744016085647105 4034754486558012064235329)
          ·
            refine ⟨3026065864918509048176497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4034754486558012064235329 3026065864918509048176497)
            ·
              refine ⟨2269549398688881786132373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3026065864918509048176497 2269549398688881786132373)
              ·
                refine ⟨106385128063541333724955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2269549398688881786132373 106385128063541333724955)
                ·
                  rfl

theorem cell22_2796988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 2, 6].length) (baseStart_2796988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2796988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2796988 prefixEnd_2796988 := by exact prefixLift 2796988
  have htrace : WordTrace (prefixWord ++ tailWord_2796988) baseStart_2796988 baseEnd_2796988 := by
    simpa [prefixWord, tailWord_2796988, baseEnd_2796988] using wordTrace_append hprefix tailTrace_2796988
  have hstable : (prefixWord ++ tailWord_2796988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2796988).length < 2 ^ (prefixWord ++ tailWord_2796988).sum := by decide
  have hdescent : baseEnd_2796988 < baseStart_2796988 := by decide
  rcases family_descends (prefixWord ++ tailWord_2796988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2797003 : List Nat := [1, 1, 1, 1, 3, 3, 5, 3, 1, 3]
def baseStart_2797003 : Nat := 118140960795 + 2797003 * 2 ^ 59
def prefixEnd_2797003 : Nat := 4983230072969 + 3 ^ 40 * 2797003 * 2
def baseEnd_2797003 : Nat := 957471287378416964399549

theorem tailTrace_2797003 : CollatzResearch.WordTrace tailWord_2797003 prefixEnd_2797003 957471287378416964399549 := by
  unfold tailWord_2797003
  simp only [CollatzResearch.WordTrace]
  refine ⟨102015080285943295926659663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68010053523962197284439775 102015080285943295926659663)
  ·
    refine ⟨153022620428914943889989495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102015080285943295926659663 153022620428914943889989495)
    ·
      refine ⟨229533930643372415834984243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153022620428914943889989495 229533930643372415834984243)
      ·
        refine ⟨344300895965058623752476365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 229533930643372415834984243 344300895965058623752476365)
        ·
          refine ⟨129112835986896983907178637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 344300895965058623752476365 129112835986896983907178637)
          ·
            refine ⟨48417313495086368965191989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 129112835986896983907178637 48417313495086368965191989)
            ·
              refine ⟨4539123140164347090486749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 48417313495086368965191989 4539123140164347090486749)
              ·
                refine ⟨1702171177561630158932531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4539123140164347090486749 1702171177561630158932531)
                ·
                  refine ⟨2553256766342445238398797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1702171177561630158932531 2553256766342445238398797)
                  ·
                    refine ⟨957471287378416964399549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2553256766342445238398797 957471287378416964399549)
                    ·
                      rfl

theorem cell22_2797003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 5, 3, 1, 3].length) (baseStart_2797003 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2797003 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2797003 prefixEnd_2797003 := by exact prefixLift 2797003
  have htrace : WordTrace (prefixWord ++ tailWord_2797003) baseStart_2797003 baseEnd_2797003 := by
    simpa [prefixWord, tailWord_2797003, baseEnd_2797003] using wordTrace_append hprefix tailTrace_2797003
  have hstable : (prefixWord ++ tailWord_2797003).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2797003).length < 2 ^ (prefixWord ++ tailWord_2797003).sum := by decide
  have hdescent : baseEnd_2797003 < baseStart_2797003 := by decide
  rcases family_descends (prefixWord ++ tailWord_2797003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2797061 : List Nat := [1, 3, 1, 1, 2, 2, 1, 7, 4]
def baseStart_2797061 : Nat := 118140960795 + 2797061 * 2 ^ 59
def prefixEnd_2797061 : Nat := 4983230072969 + 3 ^ 40 * 2797061 * 2
def baseEnd_2797061 : Nat := 319163713987908048816457

theorem tailTrace_2797061 : CollatzResearch.WordTrace tailWord_2797061 prefixEnd_2797061 319163713987908048816457 := by
  unfold tailWord_2797061
  simp only [CollatzResearch.WordTrace]
  refine ⟨102017195719733171832271037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68011463813155447888180691 102017195719733171832271037)
  ·
    refine ⟨38256448394899939437101639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102017195719733171832271037 38256448394899939437101639)
    ·
      refine ⟨57384672592349909155652459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38256448394899939437101639 57384672592349909155652459)
      ·
        refine ⟨86077008888524863733478689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57384672592349909155652459 86077008888524863733478689)
        ·
          refine ⟨64557756666393647800109017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86077008888524863733478689 64557756666393647800109017)
          ·
            refine ⟨48418317499795235850081763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64557756666393647800109017 48418317499795235850081763)
            ·
              refine ⟨72627476249692853775122645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48418317499795235850081763 72627476249692853775122645)
              ·
                refine ⟨1702206474602176260354437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 72627476249692853775122645 1702206474602176260354437)
                ·
                  refine ⟨319163713987908048816457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1702206474602176260354437 319163713987908048816457)
                  ·
                    rfl

theorem cell22_2797061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 7, 4].length) (baseStart_2797061 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2797061 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2797061 prefixEnd_2797061 := by exact prefixLift 2797061
  have htrace : WordTrace (prefixWord ++ tailWord_2797061) baseStart_2797061 baseEnd_2797061 := by
    simpa [prefixWord, tailWord_2797061, baseEnd_2797061] using wordTrace_append hprefix tailTrace_2797061
  have hstable : (prefixWord ++ tailWord_2797061).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2797061).length < 2 ^ (prefixWord ++ tailWord_2797061).sum := by decide
  have hdescent : baseEnd_2797061 < baseStart_2797061 := by decide
  rcases family_descends (prefixWord ++ tailWord_2797061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2797127 : List Nat := [1, 1, 4, 1, 6, 1, 1, 2, 2, 3]
def baseStart_2797127 : Nat := 118140960795 + 2797127 * 2 ^ 59
def prefixEnd_2797127 : Nat := 4983230072969 + 3 ^ 40 * 2797127 * 2
def baseEnd_2797127 : Nat := 957513735112521974299169

theorem tailTrace_2797127 : CollatzResearch.WordTrace tailWord_2797127 prefixEnd_2797127 957513735112521974299169 := by
  unfold tailWord_2797127
  simp only [CollatzResearch.WordTrace]
  refine ⟨102019602937494065104173635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68013068624996043402782423 102019602937494065104173635)
  ·
    refine ⟨153029404406241097656260453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102019602937494065104173635 153029404406241097656260453)
    ·
      refine ⟨28693013326170205810548835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 153029404406241097656260453 28693013326170205810548835)
      ·
        refine ⟨43039519989255308715823253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28693013326170205810548835 43039519989255308715823253)
        ·
          refine ⟨2017477499496342596054215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 43039519989255308715823253 2017477499496342596054215)
          ·
            refine ⟨3026216249244513894081323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2017477499496342596054215 3026216249244513894081323)
            ·
              refine ⟨4539324373866770841121985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3026216249244513894081323 4539324373866770841121985)
              ·
                refine ⟨3404493280400078130841489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4539324373866770841121985 3404493280400078130841489)
                ·
                  refine ⟨2553369960300058598131117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3404493280400078130841489 2553369960300058598131117)
                  ·
                    refine ⟨957513735112521974299169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2553369960300058598131117 957513735112521974299169)
                    ·
                      rfl

theorem cell22_2797127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 1, 2, 2, 3].length) (baseStart_2797127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2797127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2797127 prefixEnd_2797127 := by exact prefixLift 2797127
  have htrace : WordTrace (prefixWord ++ tailWord_2797127) baseStart_2797127 baseEnd_2797127 := by
    simpa [prefixWord, tailWord_2797127, baseEnd_2797127] using wordTrace_append hprefix tailTrace_2797127
  have hstable : (prefixWord ++ tailWord_2797127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2797127).length < 2 ^ (prefixWord ++ tailWord_2797127).sum := by decide
  have hdescent : baseEnd_2797127 < baseStart_2797127 := by decide
  rcases family_descends (prefixWord ++ tailWord_2797127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2797138 : List Nat := [3, 2, 2, 1, 2, 2, 1, 3, 3, 3]
def baseStart_2797138 : Nat := 118140960795 + 2797138 * 2 ^ 59
def prefixEnd_2797138 : Nat := 4983230072969 + 3 ^ 40 * 2797138 * 2
def baseEnd_2797138 : Nat := 957517500637321612274135

theorem tailTrace_2797138 : CollatzResearch.WordTrace tailWord_2797138 prefixEnd_2797138 957517500637321612274135 := by
  unfold tailWord_2797138
  simp only [CollatzResearch.WordTrace]
  refine ⟨25505001035113553495706017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68013336093636142655216045 25505001035113553495706017)
  ·
    refine ⟨19128750776335165121779513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25505001035113553495706017 19128750776335165121779513)
    ·
      refine ⟨14346563082251373841334635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19128750776335165121779513 14346563082251373841334635)
      ·
        refine ⟨21519844623377060762001953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14346563082251373841334635 21519844623377060762001953)
        ·
          refine ⟨16139883467532795571501465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21519844623377060762001953 16139883467532795571501465)
          ·
            refine ⟨12104912600649596678626099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16139883467532795571501465 12104912600649596678626099)
            ·
              refine ⟨18157368900974395017939149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12104912600649596678626099 18157368900974395017939149)
              ·
                refine ⟨6809013337865398131727181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18157368900974395017939149 6809013337865398131727181)
                ·
                  refine ⟨2553380001699524299397693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6809013337865398131727181 2553380001699524299397693)
                  ·
                    refine ⟨957517500637321612274135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2553380001699524299397693 957517500637321612274135)
                    ·
                      rfl

theorem cell22_2797138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 3, 3, 3].length) (baseStart_2797138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2797138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2797138 prefixEnd_2797138 := by exact prefixLift 2797138
  have htrace : WordTrace (prefixWord ++ tailWord_2797138) baseStart_2797138 baseEnd_2797138 := by
    simpa [prefixWord, tailWord_2797138, baseEnd_2797138] using wordTrace_append hprefix tailTrace_2797138
  have hstable : (prefixWord ++ tailWord_2797138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2797138).length < 2 ^ (prefixWord ++ tailWord_2797138).sum := by decide
  have hdescent : baseEnd_2797138 < baseStart_2797138 := by decide
  rcases family_descends (prefixWord ++ tailWord_2797138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2797202 : List Nat := [3, 2, 3, 1, 3, 2, 2, 1, 5]
def baseStart_2797202 : Nat := 118140960795 + 2797202 * 2 ^ 59
def prefixEnd_2797202 : Nat := 4983230072969 + 3 ^ 40 * 2797202 * 2
def baseEnd_2797202 : Nat := 319179803048415592891313

theorem tailTrace_2797202 : CollatzResearch.WordTrace tailWord_2797202 prefixEnd_2797202 319179803048415592891313 := by
  unfold tailWord_2797202
  simp only [CollatzResearch.WordTrace]
  refine ⟨25505584603055588228288465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68014892274814901942102573 25505584603055588228288465)
  ·
    refine ⟨19129188452291691171216349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25505584603055588228288465 19129188452291691171216349)
    ·
      refine ⟨7173445669609384189206131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19129188452291691171216349 7173445669609384189206131)
      ·
        refine ⟨10760168504414076283809197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7173445669609384189206131 10760168504414076283809197)
        ·
          refine ⟨4035063189155278606428449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10760168504414076283809197 4035063189155278606428449)
          ·
            refine ⟨3026297391866458954821337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4035063189155278606428449 3026297391866458954821337)
            ·
              refine ⟨2269723043899844216116003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3026297391866458954821337 2269723043899844216116003)
              ·
                refine ⟨3404584565849766324174005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2269723043899844216116003 3404584565849766324174005)
                ·
                  refine ⟨319179803048415592891313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3404584565849766324174005 319179803048415592891313)
                  ·
                    rfl

theorem cell22_2797202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 2, 1, 5].length) (baseStart_2797202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2797202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2797202 prefixEnd_2797202 := by exact prefixLift 2797202
  have htrace : WordTrace (prefixWord ++ tailWord_2797202) baseStart_2797202 baseEnd_2797202 := by
    simpa [prefixWord, tailWord_2797202, baseEnd_2797202] using wordTrace_append hprefix tailTrace_2797202
  have hstable : (prefixWord ++ tailWord_2797202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2797202).length < 2 ^ (prefixWord ++ tailWord_2797202).sum := by decide
  have hdescent : baseEnd_2797202 < baseStart_2797202 := by decide
  rcases family_descends (prefixWord ++ tailWord_2797202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2797215 : List Nat := [1, 1, 2, 7, 1, 1, 1, 1, 3, 4]
def baseStart_2797215 : Nat := 118140960795 + 2797215 * 2 ^ 59
def prefixEnd_2797215 : Nat := 4983230072969 + 3 ^ 40 * 2797215 * 2
def baseEnd_2797215 : Nat := 957543859310919078098899

theorem tailTrace_2797215 : CollatzResearch.WordTrace tailWord_2797215 prefixEnd_2797215 957543859310919078098899 := by
  unfold tailWord_2797215
  simp only [CollatzResearch.WordTrace]
  refine ⟨102022812561175256133377099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68015208374116837422251399 102022812561175256133377099)
  ·
    refine ⟨153034218841762884200065649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102022812561175256133377099 153034218841762884200065649)
    ·
      refine ⟨114775664131322163150049237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153034218841762884200065649 114775664131322163150049237)
      ·
        refine ⟨2690054628077863198829279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 114775664131322163150049237 2690054628077863198829279)
        ·
          refine ⟨4035081942116794798243919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2690054628077863198829279 4035081942116794798243919)
          ·
            refine ⟨6052622913175192197365879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4035081942116794798243919 6052622913175192197365879)
            ·
              refine ⟨9078934369762788296048819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6052622913175192197365879 9078934369762788296048819)
              ·
                refine ⟨13618401554644182444073229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9078934369762788296048819 13618401554644182444073229)
                ·
                  refine ⟨5106900582991568416527461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13618401554644182444073229 5106900582991568416527461)
                  ·
                    refine ⟨957543859310919078098899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5106900582991568416527461 957543859310919078098899)
                    ·
                      rfl

theorem cell22_2797215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 1, 3, 4].length) (baseStart_2797215 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2797215 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2797215 prefixEnd_2797215 := by exact prefixLift 2797215
  have htrace : WordTrace (prefixWord ++ tailWord_2797215) baseStart_2797215 baseEnd_2797215 := by
    simpa [prefixWord, tailWord_2797215, baseEnd_2797215] using wordTrace_append hprefix tailTrace_2797215
  have hstable : (prefixWord ++ tailWord_2797215).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2797215).length < 2 ^ (prefixWord ++ tailWord_2797215).sum := by decide
  have hdescent : baseEnd_2797215 < baseStart_2797215 := by decide
  rcases family_descends (prefixWord ++ tailWord_2797215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2797245 : List Nat := [1, 4, 1, 2, 1, 2, 4, 2, 2, 3]
def baseStart_2797245 : Nat := 118140960795 + 2797245 * 2 ^ 59
def prefixEnd_2797245 : Nat := 4983230072969 + 3 ^ 40 * 2797245 * 2
def baseEnd_2797245 : Nat := 957554128924008999848807

theorem tailTrace_2797245 : CollatzResearch.WordTrace tailWord_2797245 prefixEnd_2797245 957554128924008999848807 := by
  unfold tailWord_2797245
  simp only [CollatzResearch.WordTrace]
  refine ⟨102023906751066571256969189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68015937834044380837979459 102023906751066571256969189)
  ·
    refine ⟨19129482515824982110681723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 102023906751066571256969189 19129482515824982110681723)
    ·
      refine ⟨28694223773737473166022585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19129482515824982110681723 28694223773737473166022585)
      ·
        refine ⟨21520667830303104874516939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28694223773737473166022585 21520667830303104874516939)
        ·
          refine ⟨32281001745454657311775409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21520667830303104874516939 32281001745454657311775409)
          ·
            refine ⟨24210751309090992983831557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32281001745454657311775409 24210751309090992983831557)
            ·
              refine ⟨4539515870454561184468417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24210751309090992983831557 4539515870454561184468417)
              ·
                refine ⟨3404636902840920888351313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4539515870454561184468417 3404636902840920888351313)
                ·
                  refine ⟨2553477677130690666263485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3404636902840920888351313 2553477677130690666263485)
                  ·
                    refine ⟨957554128924008999848807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2553477677130690666263485 957554128924008999848807)
                    ·
                      rfl

theorem cell22_2797245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 4, 2, 2, 3].length) (baseStart_2797245 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2797245 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2797245 prefixEnd_2797245 := by exact prefixLift 2797245
  have htrace : WordTrace (prefixWord ++ tailWord_2797245) baseStart_2797245 baseEnd_2797245 := by
    simpa [prefixWord, tailWord_2797245, baseEnd_2797245] using wordTrace_append hprefix tailTrace_2797245
  have hstable : (prefixWord ++ tailWord_2797245).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2797245).length < 2 ^ (prefixWord ++ tailWord_2797245).sum := by decide
  have hdescent : baseEnd_2797245 < baseStart_2797245 := by decide
  rcases family_descends (prefixWord ++ tailWord_2797245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2797271 : List Nat := [1, 1, 3, 2, 1, 3, 1, 2, 2, 6]
def baseStart_2797271 : Nat := 118140960795 + 2797271 * 2 ^ 59
def prefixEnd_2797271 : Nat := 4983230072969 + 3 ^ 40 * 2797271 * 2
def baseEnd_2797271 : Nat := 957563029255353598698727

theorem tailTrace_2797271 : CollatzResearch.WordTrace tailWord_2797271 prefixEnd_2797271 957563029255353598698727 := by
  unfold tailWord_2797271
  simp only [CollatzResearch.WordTrace]
  refine ⟨102024855048972377697415667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68016570032648251798277111 102024855048972377697415667)
  ·
    refine ⟨153037282573458566546123501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102024855048972377697415667 153037282573458566546123501)
    ·
      refine ⟨57388980965046962454796313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 153037282573458566546123501 57388980965046962454796313)
      ·
        refine ⟨43041735723785221841097235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57388980965046962454796313 43041735723785221841097235)
        ·
          refine ⟨64562603585677832761645853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43041735723785221841097235 64562603585677832761645853)
          ·
            refine ⟨24210976344629187285617195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64562603585677832761645853 24210976344629187285617195)
            ·
              refine ⟨36316464516943780928425793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24210976344629187285617195 36316464516943780928425793)
              ·
                refine ⟨27237348387707835696319345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36316464516943780928425793 27237348387707835696319345)
                ·
                  refine ⟨20428011290780876772239509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27237348387707835696319345 20428011290780876772239509)
                  ·
                    refine ⟨957563029255353598698727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20428011290780876772239509 957563029255353598698727)
                    ·
                      rfl

theorem cell22_2797271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 2, 2, 6].length) (baseStart_2797271 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2797271 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2797271 prefixEnd_2797271 := by exact prefixLift 2797271
  have htrace : WordTrace (prefixWord ++ tailWord_2797271) baseStart_2797271 baseEnd_2797271 := by
    simpa [prefixWord, tailWord_2797271, baseEnd_2797271] using wordTrace_append hprefix tailTrace_2797271
  have hstable : (prefixWord ++ tailWord_2797271).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2797271).length < 2 ^ (prefixWord ++ tailWord_2797271).sum := by decide
  have hdescent : baseEnd_2797271 < baseStart_2797271 := by decide
  rcases family_descends (prefixWord ++ tailWord_2797271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2797273 : List Nat := [1, 2, 1, 2, 3, 3, 1, 1, 5, 3]
def baseStart_2797273 : Nat := 118140960795 + 2797273 * 2 ^ 59
def prefixEnd_2797273 : Nat := 4983230072969 + 3 ^ 40 * 2797273 * 2
def baseEnd_2797273 : Nat := 957563713896226260148721

theorem tailTrace_2797273 : CollatzResearch.WordTrace tailWord_2797273 prefixEnd_2797273 957563713896226260148721 := by
  unfold tailWord_2797273
  simp only [CollatzResearch.WordTrace]
  refine ⟨102024927994965132038988473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68016618663310088025992315 102024927994965132038988473)
  ·
    refine ⟨76518695996223849029241355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102024927994965132038988473 76518695996223849029241355)
    ·
      refine ⟨114778043994335773543862033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76518695996223849029241355 114778043994335773543862033)
      ·
        refine ⟨86083532995751830157896525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114778043994335773543862033 86083532995751830157896525)
        ·
          refine ⟨32281324873406936309211197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86083532995751830157896525 32281324873406936309211197)
          ·
            refine ⟨12105496827527601115954199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32281324873406936309211197 12105496827527601115954199)
            ·
              refine ⟨18158245241291401673931299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12105496827527601115954199 18158245241291401673931299)
              ·
                refine ⟨27237367861937102510896949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18158245241291401673931299 27237367861937102510896949)
                ·
                  refine ⟨2553503237056603360396589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27237367861937102510896949 2553503237056603360396589)
                  ·
                    refine ⟨957563713896226260148721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2553503237056603360396589 957563713896226260148721)
                    ·
                      rfl

theorem cell22_2797273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 1, 5, 3].length) (baseStart_2797273 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2797273 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2797273 prefixEnd_2797273 := by exact prefixLift 2797273
  have htrace : WordTrace (prefixWord ++ tailWord_2797273) baseStart_2797273 baseEnd_2797273 := by
    simpa [prefixWord, tailWord_2797273, baseEnd_2797273] using wordTrace_append hprefix tailTrace_2797273
  have hstable : (prefixWord ++ tailWord_2797273).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2797273).length < 2 ^ (prefixWord ++ tailWord_2797273).sum := by decide
  have hdescent : baseEnd_2797273 < baseStart_2797273 := by decide
  rcases family_descends (prefixWord ++ tailWord_2797273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2797303 : List Nat := [1, 1, 3, 1, 1, 1, 7, 2, 5]
def baseStart_2797303 : Nat := 118140960795 + 2797303 * 2 ^ 59
def prefixEnd_2797303 : Nat := 4983230072969 + 3 ^ 40 * 2797303 * 2
def baseEnd_2797303 : Nat := 319191327836438727299543

theorem tailTrace_2797303 : CollatzResearch.WordTrace tailWord_2797303 prefixEnd_2797303 319191327836438727299543 := by
  unfold tailWord_2797303
  simp only [CollatzResearch.WordTrace]
  refine ⟨102026022184856447162580563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68017348123237631441720375 102026022184856447162580563)
  ·
    refine ⟨153039033277284670743870845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102026022184856447162580563 153039033277284670743870845)
    ·
      refine ⟨57389637478981751528951567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 153039033277284670743870845 57389637478981751528951567)
      ·
        refine ⟨86084456218472627293427351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57389637478981751528951567 86084456218472627293427351)
        ·
          refine ⟨129126684327708940940141027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86084456218472627293427351 129126684327708940940141027)
          ·
            refine ⟨193690026491563411410211541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129126684327708940940141027 193690026491563411410211541)
            ·
              refine ⟨4539609995896017454926833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 193690026491563411410211541 4539609995896017454926833)
              ·
                refine ⟨3404707496922013091195125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4539609995896017454926833 3404707496922013091195125)
                ·
                  refine ⟨319191327836438727299543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3404707496922013091195125 319191327836438727299543)
                  ·
                    rfl

theorem cell22_2797303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 7, 2, 5].length) (baseStart_2797303 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2797303 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2797303 prefixEnd_2797303 := by exact prefixLift 2797303
  have htrace : WordTrace (prefixWord ++ tailWord_2797303) baseStart_2797303 baseEnd_2797303 := by
    simpa [prefixWord, tailWord_2797303, baseEnd_2797303] using wordTrace_append hprefix tailTrace_2797303
  have hstable : (prefixWord ++ tailWord_2797303).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2797303).length < 2 ^ (prefixWord ++ tailWord_2797303).sum := by decide
  have hdescent : baseEnd_2797303 < baseStart_2797303 := by decide
  rcases family_descends (prefixWord ++ tailWord_2797303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2797320 : List Nat := [2, 1, 3, 2, 2, 1, 5, 1, 5]
def baseStart_2797320 : Nat := 118140960795 + 2797320 * 2 ^ 59
def prefixEnd_2797320 : Nat := 4983230072969 + 3 ^ 40 * 2797320 * 2
def baseEnd_2797320 : Nat := 319193267652244601407859

theorem tailTrace_2797320 : CollatzResearch.WordTrace tailWord_2797320 prefixEnd_2797320 319193267652244601407859 := by
  unfold tailWord_2797320
  simp only [CollatzResearch.WordTrace]
  refine ⟨51013321112897429532974707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68017761483863239377299609 51013321112897429532974707)
  ·
    refine ⟨76519981669346144299462061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51013321112897429532974707 76519981669346144299462061)
    ·
      refine ⟨28694993126004804112298273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76519981669346144299462061 28694993126004804112298273)
      ·
        refine ⟨21521244844503603084223705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28694993126004804112298273 21521244844503603084223705)
        ·
          refine ⟨16140933633377702313167779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21521244844503603084223705 16140933633377702313167779)
          ·
            refine ⟨24211400450066553469751669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16140933633377702313167779 24211400450066553469751669)
            ·
              refine ⟨2269818792193739387789219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24211400450066553469751669 2269818792193739387789219)
              ·
                refine ⟨3404728188290609081683829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2269818792193739387789219 3404728188290609081683829)
                ·
                  refine ⟨319193267652244601407859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3404728188290609081683829 319193267652244601407859)
                  ·
                    rfl

theorem cell22_2797320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 5, 1, 5].length) (baseStart_2797320 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2797320 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2797320 prefixEnd_2797320 := by exact prefixLift 2797320
  have htrace : WordTrace (prefixWord ++ tailWord_2797320) baseStart_2797320 baseEnd_2797320 := by
    simpa [prefixWord, tailWord_2797320, baseEnd_2797320] using wordTrace_append hprefix tailTrace_2797320
  have hstable : (prefixWord ++ tailWord_2797320).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2797320).length < 2 ^ (prefixWord ++ tailWord_2797320).sum := by decide
  have hdescent : baseEnd_2797320 < baseStart_2797320 := by decide
  rcases family_descends (prefixWord ++ tailWord_2797320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2797331 : List Nat := [1, 1, 1, 2, 1, 3, 2, 3, 8]
def baseStart_2797331 : Nat := 118140960795 + 2797331 * 2 ^ 59
def prefixEnd_2797331 : Nat := 4983230072969 + 3 ^ 40 * 2797331 * 2
def baseEnd_2797331 : Nat := 319194522827177814066181

theorem tailTrace_2797331 : CollatzResearch.WordTrace tailWord_2797331 prefixEnd_2797331 319194522827177814066181 := by
  unfold tailWord_2797331
  simp only [CollatzResearch.WordTrace]
  refine ⟨102027043428755007944599847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68018028952503338629733231 102027043428755007944599847)
  ·
    refine ⟨153040565143132511916899771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102027043428755007944599847 153040565143132511916899771)
    ·
      refine ⟨229560847714698767875349657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153040565143132511916899771 229560847714698767875349657)
      ·
        refine ⟨172170635786024075906512243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 229560847714698767875349657 172170635786024075906512243)
        ·
          refine ⟨258255953679036113859768365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172170635786024075906512243 258255953679036113859768365)
          ·
            refine ⟨96845982629638542697413137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 258255953679036113859768365 96845982629638542697413137)
            ·
              refine ⟨72634486972228907023059853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96845982629638542697413137 72634486972228907023059853)
              ·
                refine ⟨27237932614585840133647445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72634486972228907023059853 27237932614585840133647445)
                ·
                  refine ⟨319194522827177814066181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27237932614585840133647445 319194522827177814066181)
                  ·
                    rfl

theorem cell22_2797331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 3, 8].length) (baseStart_2797331 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2797331 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2797331 prefixEnd_2797331 := by exact prefixLift 2797331
  have htrace : WordTrace (prefixWord ++ tailWord_2797331) baseStart_2797331 baseEnd_2797331 := by
    simpa [prefixWord, tailWord_2797331, baseEnd_2797331] using wordTrace_append hprefix tailTrace_2797331
  have hstable : (prefixWord ++ tailWord_2797331).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2797331).length < 2 ^ (prefixWord ++ tailWord_2797331).sum := by decide
  have hdescent : baseEnd_2797331 < baseStart_2797331 := by decide
  rcases family_descends (prefixWord ++ tailWord_2797331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2797393 : List Nat := [1, 2, 2, 1, 5, 1, 2, 8]
def baseStart_2797393 : Nat := 118140960795 + 2797393 * 2 ^ 59
def prefixEnd_2797393 : Nat := 4983230072969 + 3 ^ 40 * 2797393 * 2
def baseEnd_2797393 : Nat := 106400532483176216349817

theorem tailTrace_2797393 : CollatzResearch.WordTrace tailWord_2797393 prefixEnd_2797393 106400532483176216349817 := by
  unfold tailWord_2797393
  simp only [CollatzResearch.WordTrace]
  refine ⟨102029304754530392533356833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68019536503020261688904555 102029304754530392533356833)
  ·
    refine ⟨76521978565897794400017625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102029304754530392533356833 76521978565897794400017625)
    ·
      refine ⟨57391483924423345800013219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76521978565897794400017625 57391483924423345800013219)
      ·
        refine ⟨86087225886635018700019829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57391483924423345800013219 86087225886635018700019829)
        ·
          refine ⟨8070677426872033003126859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 86087225886635018700019829 8070677426872033003126859)
          ·
            refine ⟨12106016140308049504690289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8070677426872033003126859 12106016140308049504690289)
            ·
              refine ⟨9079512105231037128517717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12106016140308049504690289 9079512105231037128517717)
              ·
                refine ⟨106400532483176216349817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9079512105231037128517717 106400532483176216349817)
                ·
                  rfl

theorem cell22_2797393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 8].length) (baseStart_2797393 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2797393 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2797393 prefixEnd_2797393 := by exact prefixLift 2797393
  have htrace : WordTrace (prefixWord ++ tailWord_2797393) baseStart_2797393 baseEnd_2797393 := by
    simpa [prefixWord, tailWord_2797393, baseEnd_2797393] using wordTrace_append hprefix tailTrace_2797393
  have hstable : (prefixWord ++ tailWord_2797393).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2797393).length < 2 ^ (prefixWord ++ tailWord_2797393).sum := by decide
  have hdescent : baseEnd_2797393 < baseStart_2797393 := by decide
  rcases family_descends (prefixWord ++ tailWord_2797393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2797425 : List Nat := [1, 2, 2, 2, 1, 3, 2, 3, 3, 3]
def baseStart_2797425 : Nat := 118140960795 + 2797425 * 2 ^ 59
def prefixEnd_2797425 : Nat := 4983230072969 + 3 ^ 40 * 2797425 * 2
def baseEnd_2797425 : Nat := 957615746602548530348255

theorem tailTrace_2797425 : CollatzResearch.WordTrace tailWord_2797425 prefixEnd_2797425 957615746602548530348255 := by
  unfold tailWord_2797425
  simp only [CollatzResearch.WordTrace]
  refine ⟨102030471890414461998521729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68020314593609641332347819 102030471890414461998521729)
  ·
    refine ⟨76522853917810846498891297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102030471890414461998521729 76522853917810846498891297)
    ·
      refine ⟨57392140438358134874168473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76522853917810846498891297 57392140438358134874168473)
      ·
        refine ⟨43044105328768601155626355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57392140438358134874168473 43044105328768601155626355)
        ·
          refine ⟨64566157993152901733439533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43044105328768601155626355 64566157993152901733439533)
          ·
            refine ⟨24212309247432338150039825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64566157993152901733439533 24212309247432338150039825)
            ·
              refine ⟨18159231935574253612529869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24212309247432338150039825 18159231935574253612529869)
              ·
                refine ⟨6809711975840345104698701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18159231935574253612529869 6809711975840345104698701)
                ·
                  refine ⟨2553641990940129414262013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6809711975840345104698701 2553641990940129414262013)
                  ·
                    refine ⟨957615746602548530348255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2553641990940129414262013 957615746602548530348255)
                    ·
                      rfl

theorem cell22_2797425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 3, 3, 3].length) (baseStart_2797425 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2797425 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2797425 prefixEnd_2797425 := by exact prefixLift 2797425
  have htrace : WordTrace (prefixWord ++ tailWord_2797425) baseStart_2797425 baseEnd_2797425 := by
    simpa [prefixWord, tailWord_2797425, baseEnd_2797425] using wordTrace_append hprefix tailTrace_2797425
  have hstable : (prefixWord ++ tailWord_2797425).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2797425).length < 2 ^ (prefixWord ++ tailWord_2797425).sum := by decide
  have hdescent : baseEnd_2797425 < baseStart_2797425 := by decide
  rcases family_descends (prefixWord ++ tailWord_2797425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2797502 : List Nat := [4, 2, 1, 1, 1, 3, 1, 4, 1, 4]
def baseStart_2797502 : Nat := 118140960795 + 2797502 * 2 ^ 59
def prefixEnd_2797502 : Nat := 4983230072969 + 3 ^ 40 * 2797502 * 2
def baseEnd_2797502 : Nat := 957642105276145996173019

theorem tailTrace_2797502 : CollatzResearch.WordTrace tailWord_2797502 prefixEnd_2797502 957642105276145996173019 := by
  unfold tailWord_2797502
  simp only [CollatzResearch.WordTrace]
  refine ⟨12754160038891938018634345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68022186874090336099383173 12754160038891938018634345)
  ·
    refine ⟨9565620029168953513975759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12754160038891938018634345 9565620029168953513975759)
    ·
      refine ⟨14348430043753430270963639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9565620029168953513975759 14348430043753430270963639)
      ·
        refine ⟨21522645065630145406445459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14348430043753430270963639 21522645065630145406445459)
        ·
          refine ⟨32283967598445218109668189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21522645065630145406445459 32283967598445218109668189)
          ·
            refine ⟨12106487849416956791125571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32283967598445218109668189 12106487849416956791125571)
            ·
              refine ⟨18159731774125435186688357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12106487849416956791125571 18159731774125435186688357)
              ·
                refine ⟨3404949707648519097504067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18159731774125435186688357 3404949707648519097504067)
                ·
                  refine ⟨5107424561472778646256101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3404949707648519097504067 5107424561472778646256101)
                  ·
                    refine ⟨957642105276145996173019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5107424561472778646256101 957642105276145996173019)
                    ·
                      rfl

theorem cell22_2797502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 4, 1, 4].length) (baseStart_2797502 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2797502 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2797502 prefixEnd_2797502 := by exact prefixLift 2797502
  have htrace : WordTrace (prefixWord ++ tailWord_2797502) baseStart_2797502 baseEnd_2797502 := by
    simpa [prefixWord, tailWord_2797502, baseEnd_2797502] using wordTrace_append hprefix tailTrace_2797502
  have hstable : (prefixWord ++ tailWord_2797502).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2797502).length < 2 ^ (prefixWord ++ tailWord_2797502).sum := by decide
  have hdescent : baseEnd_2797502 < baseStart_2797502 := by decide
  rcases family_descends (prefixWord ++ tailWord_2797502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2797515 : List Nat := [1, 1, 1, 1, 3, 4, 1, 1, 6, 3]
def baseStart_2797515 : Nat := 118140960795 + 2797515 * 2 ^ 59
def prefixEnd_2797515 : Nat := 4983230072969 + 3 ^ 40 * 2797515 * 2
def baseEnd_2797515 : Nat := 957646555441818295597979

theorem tailTrace_2797515 : CollatzResearch.WordTrace tailWord_2797515 prefixEnd_2797515 957646555441818295597979 := by
  unfold tailWord_2797515
  simp only [CollatzResearch.WordTrace]
  refine ⟨102033754460088407369297999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68022502973392271579531999 102033754460088407369297999)
  ·
    refine ⟨153050631690132611053946999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102033754460088407369297999 153050631690132611053946999)
    ·
      refine ⟨229575947535198916580920499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153050631690132611053946999 229575947535198916580920499)
      ·
        refine ⟨344363921302798374871380749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 229575947535198916580920499 344363921302798374871380749)
        ·
          refine ⟨129136470488549390576767781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 344363921302798374871380749 129136470488549390576767781)
          ·
            refine ⟨24213088216603010733143959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 129136470488549390576767781 24213088216603010733143959)
            ·
              refine ⟨36319632324904516099715939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24213088216603010733143959 36319632324904516099715939)
              ·
                refine ⟨54479448487356774149573909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36319632324904516099715939 54479448487356774149573909)
                ·
                  refine ⟨2553724147844848788261277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 54479448487356774149573909 2553724147844848788261277)
                  ·
                    refine ⟨957646555441818295597979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2553724147844848788261277 957646555441818295597979)
                    ·
                      rfl

theorem cell22_2797515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 1, 6, 3].length) (baseStart_2797515 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2797515 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2797515 prefixEnd_2797515 := by exact prefixLift 2797515
  have htrace : WordTrace (prefixWord ++ tailWord_2797515) baseStart_2797515 baseEnd_2797515 := by
    simpa [prefixWord, tailWord_2797515, baseEnd_2797515] using wordTrace_append hprefix tailTrace_2797515
  have hstable : (prefixWord ++ tailWord_2797515).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2797515).length < 2 ^ (prefixWord ++ tailWord_2797515).sum := by decide
  have hdescent : baseEnd_2797515 < baseStart_2797515 := by decide
  rcases family_descends (prefixWord ++ tailWord_2797515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2797605 : List Nat := [1, 3, 1, 2, 2, 3, 1, 1, 1, 7]
def baseStart_2797605 : Nat := 118140960795 + 2797605 * 2 ^ 59
def prefixEnd_2797605 : Nat := 4983230072969 + 3 ^ 40 * 2797605 * 2
def baseEnd_2797605 : Nat := 957677364281088060847703

theorem tailTrace_2797605 : CollatzResearch.WordTrace tailWord_2797605 prefixEnd_2797605 957677364281088060847703 := by
  unfold tailWord_2797605
  simp only [CollatzResearch.WordTrace]
  refine ⟨102037037029762352740074269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68024691353174901826716179 102037037029762352740074269)
  ·
    refine ⟨38263888886160882277527851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102037037029762352740074269 38263888886160882277527851)
    ·
      refine ⟨57395833329241323416291777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38263888886160882277527851 57395833329241323416291777)
      ·
        refine ⟨43046874996930992562218833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57395833329241323416291777 43046874996930992562218833)
        ·
          refine ⟨32285156247698244421664125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43046874996930992562218833 32285156247698244421664125)
          ·
            refine ⟨12106933592886841658124047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32285156247698244421664125 12106933592886841658124047)
            ·
              refine ⟨18160400389330262487186071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12106933592886841658124047 18160400389330262487186071)
              ·
                refine ⟨27240600583995393730779107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18160400389330262487186071 27240600583995393730779107)
                ·
                  refine ⟨40860900875993090596168661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27240600583995393730779107 40860900875993090596168661)
                  ·
                    refine ⟨957677364281088060847703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40860900875993090596168661 957677364281088060847703)
                    ·
                      rfl

theorem cell22_2797605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 1, 1, 7].length) (baseStart_2797605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2797605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2797605 prefixEnd_2797605 := by exact prefixLift 2797605
  have htrace : WordTrace (prefixWord ++ tailWord_2797605) baseStart_2797605 baseEnd_2797605 := by
    simpa [prefixWord, tailWord_2797605, baseEnd_2797605] using wordTrace_append hprefix tailTrace_2797605
  have hstable : (prefixWord ++ tailWord_2797605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2797605).length < 2 ^ (prefixWord ++ tailWord_2797605).sum := by decide
  have hdescent : baseEnd_2797605 < baseStart_2797605 := by decide
  rcases family_descends (prefixWord ++ tailWord_2797605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2797622 : List Nat := [5, 1, 2, 1, 1, 1, 1, 2, 1, 7]
def baseStart_2797622 : Nat := 118140960795 + 2797622 * 2 ^ 59
def prefixEnd_2797622 : Nat := 4983230072969 + 3 ^ 40 * 2797622 * 2
def baseEnd_2797622 : Nat := 957683183728505683172651

theorem tailTrace_2797622 : CollatzResearch.WordTrace tailWord_2797622 prefixEnd_2797622 957683183728505683172651 := by
  unfold tailWord_2797622
  simp only [CollatzResearch.WordTrace]
  refine ⟨6377353566918797790215195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 68025104713800509762295413 6377353566918797790215195)
  ·
    refine ⟨9566030350378196685322793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6377353566918797790215195 9566030350378196685322793)
    ·
      refine ⟨7174522762783647513992095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9566030350378196685322793 7174522762783647513992095)
      ·
        refine ⟨10761784144175471270988143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7174522762783647513992095 10761784144175471270988143)
        ·
          refine ⟨16142676216263206906482215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10761784144175471270988143 16142676216263206906482215)
          ·
            refine ⟨24214014324394810359723323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16142676216263206906482215 24214014324394810359723323)
            ·
              refine ⟨36321021486592215539584985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24214014324394810359723323 36321021486592215539584985)
              ·
                refine ⟨27240766114944161654688739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36321021486592215539584985 27240766114944161654688739)
                ·
                  refine ⟨40861149172416242482033109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27240766114944161654688739 40861149172416242482033109)
                  ·
                    refine ⟨957683183728505683172651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40861149172416242482033109 957683183728505683172651)
                    ·
                      rfl

theorem cell22_2797622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 2, 1, 7].length) (baseStart_2797622 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2797622 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2797622 prefixEnd_2797622 := by exact prefixLift 2797622
  have htrace : WordTrace (prefixWord ++ tailWord_2797622) baseStart_2797622 baseEnd_2797622 := by
    simpa [prefixWord, tailWord_2797622, baseEnd_2797622] using wordTrace_append hprefix tailTrace_2797622
  have hstable : (prefixWord ++ tailWord_2797622).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2797622).length < 2 ^ (prefixWord ++ tailWord_2797622).sum := by decide
  have hdescent : baseEnd_2797622 < baseStart_2797622 := by decide
  rcases family_descends (prefixWord ++ tailWord_2797622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2797667 : List Nat := [1, 1, 1, 5, 1, 1, 5, 1, 1, 5]
def baseStart_2797667 : Nat := 118140960795 + 2797667 * 2 ^ 59
def prefixEnd_2797667 : Nat := 4983230072969 + 3 ^ 40 * 2797667 * 2
def baseEnd_2797667 : Nat := 957698588148140565797513

theorem tailTrace_2797667 : CollatzResearch.WordTrace tailWord_2797667 prefixEnd_2797667 957698588148140565797513 := by
  unfold tailWord_2797667
  simp only [CollatzResearch.WordTrace]
  refine ⟨102039298355537737328831255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68026198903691824885887503 102039298355537737328831255)
  ·
    refine ⟨153058947533306605993246883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102039298355537737328831255 153058947533306605993246883)
    ·
      refine ⟨229588421299959908989870325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153058947533306605993246883 229588421299959908989870325)
      ·
        refine ⟨21523914496871241467800343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 229588421299959908989870325 21523914496871241467800343)
        ·
          refine ⟨32285871745306862201700515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21523914496871241467800343 32285871745306862201700515)
          ·
            refine ⟨48428807617960293302550773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32285871745306862201700515 48428807617960293302550773)
            ·
              refine ⟨4540200714183777497114135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 48428807617960293302550773 4540200714183777497114135)
              ·
                refine ⟨6810301071275666245671203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4540200714183777497114135 6810301071275666245671203)
                ·
                  refine ⟨10215451606913499368506805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6810301071275666245671203 10215451606913499368506805)
                  ·
                    refine ⟨957698588148140565797513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10215451606913499368506805 957698588148140565797513)
                    ·
                      rfl

theorem cell22_2797667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 5, 1, 1, 5].length) (baseStart_2797667 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2797667 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2797667 prefixEnd_2797667 := by exact prefixLift 2797667
  have htrace : WordTrace (prefixWord ++ tailWord_2797667) baseStart_2797667 baseEnd_2797667 := by
    simpa [prefixWord, tailWord_2797667, baseEnd_2797667] using wordTrace_append hprefix tailTrace_2797667
  have hstable : (prefixWord ++ tailWord_2797667).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2797667).length < 2 ^ (prefixWord ++ tailWord_2797667).sum := by decide
  have hdescent : baseEnd_2797667 < baseStart_2797667 := by decide
  rcases family_descends (prefixWord ++ tailWord_2797667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2797682 : List Nat := [3, 2, 1, 2, 2, 2, 2, 1, 1, 6]
def baseStart_2797682 : Nat := 118140960795 + 2797682 * 2 ^ 59
def prefixEnd_2797682 : Nat := 4983230072969 + 3 ^ 40 * 2797682 * 2
def baseEnd_2797682 : Nat := 957703722954685526672467

theorem tailTrace_2797682 : CollatzResearch.WordTrace tailWord_2797682 prefixEnd_2797682 957703722954685526672467 := by
  unfold tailWord_2797682
  simp only [CollatzResearch.WordTrace]
  refine ⟨25509961362620848722656825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68026563633655596593751533 25509961362620848722656825)
  ·
    refine ⟨19132471021965636541992619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25509961362620848722656825 19132471021965636541992619)
    ·
      refine ⟨28698706532948454812988929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19132471021965636541992619 28698706532948454812988929)
      ·
        refine ⟨21524029899711341109741697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28698706532948454812988929 21524029899711341109741697)
        ·
          refine ⟨16143022424783505832306273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21524029899711341109741697 16143022424783505832306273)
          ·
            refine ⟨12107266818587629374229705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16143022424783505832306273 12107266818587629374229705)
            ·
              refine ⟨9080450113940722030672279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12107266818587629374229705 9080450113940722030672279)
              ·
                refine ⟨13620675170911083046008419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9080450113940722030672279 13620675170911083046008419)
                ·
                  refine ⟨20431012756366624569012629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13620675170911083046008419 20431012756366624569012629)
                  ·
                    refine ⟨957703722954685526672467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20431012756366624569012629 957703722954685526672467)
                    ·
                      rfl

theorem cell22_2797682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 1, 1, 6].length) (baseStart_2797682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2797682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2797682 prefixEnd_2797682 := by exact prefixLift 2797682
  have htrace : WordTrace (prefixWord ++ tailWord_2797682) baseStart_2797682 baseEnd_2797682 := by
    simpa [prefixWord, tailWord_2797682, baseEnd_2797682] using wordTrace_append hprefix tailTrace_2797682
  have hstable : (prefixWord ++ tailWord_2797682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2797682).length < 2 ^ (prefixWord ++ tailWord_2797682).sum := by decide
  have hdescent : baseEnd_2797682 < baseStart_2797682 := by decide
  rcases family_descends (prefixWord ++ tailWord_2797682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2797686 : List Nat := [5, 1, 1, 2, 1, 2, 3, 3, 4]
def baseStart_2797686 : Nat := 118140960795 + 2797686 * 2 ^ 59
def prefixEnd_2797686 : Nat := 4983230072969 + 3 ^ 40 * 2797686 * 2
def baseEnd_2797686 : Nat := 319235030745476949857485

theorem tailTrace_2797686 : CollatzResearch.WordTrace tailWord_2797686 prefixEnd_2797686 319235030745476949857485 := by
  unfold tailWord_2797686
  simp only [CollatzResearch.WordTrace]
  refine ⟨6377499458904306473360807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 68026660894979269049181941 6377499458904306473360807)
  ·
    refine ⟨9566249188356459710041211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6377499458904306473360807 9566249188356459710041211)
    ·
      refine ⟨14349373782534689565061817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9566249188356459710041211 14349373782534689565061817)
      ·
        refine ⟨10762030336901017173796363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14349373782534689565061817 10762030336901017173796363)
        ·
          refine ⟨16143045505351525760694545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10762030336901017173796363 16143045505351525760694545)
          ·
            refine ⟨12107284129013644320520909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16143045505351525760694545 12107284129013644320520909)
            ·
              refine ⟨4540231548380116620195341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12107284129013644320520909 4540231548380116620195341)
              ·
                refine ⟨1702586830642543732573253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4540231548380116620195341 1702586830642543732573253)
                ·
                  refine ⟨319235030745476949857485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1702586830642543732573253 319235030745476949857485)
                  ·
                    rfl

theorem cell22_2797686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 3, 3, 4].length) (baseStart_2797686 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2797686 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2797686 prefixEnd_2797686 := by exact prefixLift 2797686
  have htrace : WordTrace (prefixWord ++ tailWord_2797686) baseStart_2797686 baseEnd_2797686 := by
    simpa [prefixWord, tailWord_2797686, baseEnd_2797686] using wordTrace_append hprefix tailTrace_2797686
  have hstable : (prefixWord ++ tailWord_2797686).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2797686).length < 2 ^ (prefixWord ++ tailWord_2797686).sum := by decide
  have hdescent : baseEnd_2797686 < baseStart_2797686 := by decide
  rcases family_descends (prefixWord ++ tailWord_2797686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2797746 : List Nat := [3, 2, 1, 1, 1, 3, 2, 5, 1, 3]
def baseStart_2797746 : Nat := 118140960795 + 2797746 * 2 ^ 59
def prefixEnd_2797746 : Nat := 4983230072969 + 3 ^ 40 * 2797746 * 2
def baseEnd_2797746 : Nat := 957725631462610693072271

theorem tailTrace_2797746 : CollatzResearch.WordTrace tailWord_2797746 prefixEnd_2797746 957725631462610693072271 := by
  unfold tailWord_2797746
  simp only [CollatzResearch.WordTrace]
  refine ⟨25510544930562883455239273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68028119814834355880638061 25510544930562883455239273)
  ·
    refine ⟨19132908697922162591429455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25510544930562883455239273 19132908697922162591429455)
    ·
      refine ⟨28699363046883243887144183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19132908697922162591429455 28699363046883243887144183)
      ·
        refine ⟨43049044570324865830716275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28699363046883243887144183 43049044570324865830716275)
        ·
          refine ⟨64573566855487298746074413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43049044570324865830716275 64573566855487298746074413)
          ·
            refine ⟨24215087570807737029777905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64573566855487298746074413 24215087570807737029777905)
            ·
              refine ⟨18161315678105802772333429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24215087570807737029777905 18161315678105802772333429)
              ·
                refine ⟨1702623344822419009906259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18161315678105802772333429 1702623344822419009906259)
                ·
                  refine ⟨2553935017233628514859389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1702623344822419009906259 2553935017233628514859389)
                  ·
                    refine ⟨957725631462610693072271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2553935017233628514859389 957725631462610693072271)
                    ·
                      rfl

theorem cell22_2797746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 5, 1, 3].length) (baseStart_2797746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2797746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2797746 prefixEnd_2797746 := by exact prefixLift 2797746
  have htrace : WordTrace (prefixWord ++ tailWord_2797746) baseStart_2797746 baseEnd_2797746 := by
    simpa [prefixWord, tailWord_2797746, baseEnd_2797746] using wordTrace_append hprefix tailTrace_2797746
  have hstable : (prefixWord ++ tailWord_2797746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2797746).length < 2 ^ (prefixWord ++ tailWord_2797746).sum := by decide
  have hdescent : baseEnd_2797746 < baseStart_2797746 := by decide
  rcases family_descends (prefixWord ++ tailWord_2797746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2797748 : List Nat := [2, 5, 3, 1, 2, 9]
def baseStart_2797748 : Nat := 118140960795 + 2797748 * 2 ^ 59
def prefixEnd_2797748 : Nat := 4983230072969 + 3 ^ 40 * 2797748 * 2
def baseEnd_2797748 : Nat := 11823781680289917957065

theorem tailTrace_2797748 : CollatzResearch.WordTrace tailWord_2797748 prefixEnd_2797748 11823781680289917957065 := by
  unfold tailWord_2797748
  simp only [CollatzResearch.WordTrace]
  refine ⟨51021126334122144081264949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68028168445496192108353265 51021126334122144081264949)
  ·
    refine ⟨4783230593823951007618589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 51021126334122144081264949 4783230593823951007618589)
    ·
      refine ⟨1793711472683981627856971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4783230593823951007618589 1793711472683981627856971)
      ·
        refine ⟨2690567209025972441785457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1793711472683981627856971 2690567209025972441785457)
        ·
          refine ⟨2017925406769479331339093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2690567209025972441785457 2017925406769479331339093)
          ·
            refine ⟨11823781680289917957065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2017925406769479331339093 11823781680289917957065)
            ·
              rfl

theorem cell22_2797748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 9].length) (baseStart_2797748 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2797748 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2797748 prefixEnd_2797748 := by exact prefixLift 2797748
  have htrace : WordTrace (prefixWord ++ tailWord_2797748) baseStart_2797748 baseEnd_2797748 := by
    simpa [prefixWord, tailWord_2797748, baseEnd_2797748] using wordTrace_append hprefix tailTrace_2797748
  have hstable : (prefixWord ++ tailWord_2797748).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2797748).length < 2 ^ (prefixWord ++ tailWord_2797748).sum := by decide
  have hdescent : baseEnd_2797748 < baseStart_2797748 := by decide
  rcases family_descends (prefixWord ++ tailWord_2797748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2797757 : List Nat := [1, 4, 1, 2, 1, 1, 1, 4, 2, 5]
def baseStart_2797757 : Nat := 118140960795 + 2797757 * 2 ^ 59
def prefixEnd_2797757 : Nat := 4983230072969 + 3 ^ 40 * 2797757 * 2
def baseEnd_2797757 : Nat := 957729396987410331047237

theorem tailTrace_2797757 : CollatzResearch.WordTrace tailWord_2797757 prefixEnd_2797757 957729396987410331047237 := by
  unfold tailWord_2797757
  simp only [CollatzResearch.WordTrace]
  refine ⟨102042580925211682699607525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68028387283474455133071683 102042580925211682699607525)
  ·
    refine ⟨19132983923477190506176411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 102042580925211682699607525 19132983923477190506176411)
    ·
      refine ⟨28699475885215785759264617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19132983923477190506176411 28699475885215785759264617)
      ·
        refine ⟨21524606913911839319448463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28699475885215785759264617 21524606913911839319448463)
        ·
          refine ⟨32286910370867758979172695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21524606913911839319448463 32286910370867758979172695)
          ·
            refine ⟨48430365556301638468759043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32286910370867758979172695 48430365556301638468759043)
            ·
              refine ⟨72645548334452457703138565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48430365556301638468759043 72645548334452457703138565)
              ·
                refine ⟨13621040312709835819338481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 72645548334452457703138565 13621040312709835819338481)
                ·
                  refine ⟨10215780234532376864503861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13621040312709835819338481 10215780234532376864503861)
                  ·
                    refine ⟨957729396987410331047237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10215780234532376864503861 957729396987410331047237)
                    ·
                      rfl

theorem cell22_2797757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 4, 2, 5].length) (baseStart_2797757 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2797757 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2797757 prefixEnd_2797757 := by exact prefixLift 2797757
  have htrace : WordTrace (prefixWord ++ tailWord_2797757) baseStart_2797757 baseEnd_2797757 := by
    simpa [prefixWord, tailWord_2797757, baseEnd_2797757] using wordTrace_append hprefix tailTrace_2797757
  have hstable : (prefixWord ++ tailWord_2797757).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2797757).length < 2 ^ (prefixWord ++ tailWord_2797757).sum := by decide
  have hdescent : baseEnd_2797757 < baseStart_2797757 := by decide
  rcases family_descends (prefixWord ++ tailWord_2797757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2797774 : List Nat := [4, 1, 1, 1, 4, 2, 1, 1, 2, 5]
def baseStart_2797774 : Nat := 118140960795 + 2797774 * 2 ^ 59
def prefixEnd_2797774 : Nat := 4983230072969 + 3 ^ 40 * 2797774 * 2
def baseEnd_2797774 : Nat := 957735216434827953372185

theorem tailTrace_2797774 : CollatzResearch.WordTrace tailWord_2797774 prefixEnd_2797774 957735216434827953372185 := by
  unfold tailWord_2797774
  simp only [CollatzResearch.WordTrace]
  refine ⟨12755400120768761825372047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68028800644100063068650917 12755400120768761825372047)
  ·
    refine ⟨19133100181153142738058071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12755400120768761825372047 19133100181153142738058071)
    ·
      refine ⟨28699650271729714107087107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19133100181153142738058071 28699650271729714107087107)
      ·
        refine ⟨43049475407594571160630661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28699650271729714107087107 43049475407594571160630661)
        ·
          refine ⟨8071776638923982092618249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43049475407594571160630661 8071776638923982092618249)
          ·
            refine ⟨6053832479192986569463687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8071776638923982092618249 6053832479192986569463687)
            ·
              refine ⟨9080748718789479854195531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6053832479192986569463687 9080748718789479854195531)
              ·
                refine ⟨13621123078184219781293297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9080748718789479854195531 13621123078184219781293297)
                ·
                  refine ⟨10215842308638164835969973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13621123078184219781293297 10215842308638164835969973)
                  ·
                    refine ⟨957735216434827953372185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10215842308638164835969973 957735216434827953372185)
                    ·
                      rfl

theorem cell22_2797774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 1, 2, 5].length) (baseStart_2797774 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2797774 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2797774 prefixEnd_2797774 := by exact prefixLift 2797774
  have htrace : WordTrace (prefixWord ++ tailWord_2797774) baseStart_2797774 baseEnd_2797774 := by
    simpa [prefixWord, tailWord_2797774, baseEnd_2797774] using wordTrace_append hprefix tailTrace_2797774
  have hstable : (prefixWord ++ tailWord_2797774).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2797774).length < 2 ^ (prefixWord ++ tailWord_2797774).sum := by decide
  have hdescent : baseEnd_2797774 < baseStart_2797774 := by decide
  rcases family_descends (prefixWord ++ tailWord_2797774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2797866 : List Nat := [3, 1, 4, 2, 2, 2, 8]
def baseStart_2797866 : Nat := 118140960795 + 2797866 * 2 ^ 59
def prefixEnd_2797866 : Nat := 4983230072969 + 3 ^ 40 * 2797866 * 2
def baseEnd_2797866 : Nat := 35472841107961865928589

theorem tailTrace_2797866 : CollatzResearch.WordTrace tailWord_2797866 prefixEnd_2797866 35472841107961865928589 := by
  unfold tailWord_2797866
  simp only [CollatzResearch.WordTrace]
  refine ⟨25511639120454198578831363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68031037654544529543550301 25511639120454198578831363)
  ·
    refine ⟨38267458680681297868247045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25511639120454198578831363 38267458680681297868247045)
    ·
      refine ⟨7175148502627743350296321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38267458680681297868247045 7175148502627743350296321)
      ·
        refine ⟨5381361376970807512722241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7175148502627743350296321 5381361376970807512722241)
        ·
          refine ⟨4036021032728105634541681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5381361376970807512722241 4036021032728105634541681)
          ·
            refine ⟨3027015774546079225906261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4036021032728105634541681 3027015774546079225906261)
            ·
              refine ⟨35472841107961865928589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3027015774546079225906261 35472841107961865928589)
              ·
                rfl

theorem cell22_2797866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 8].length) (baseStart_2797866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2797866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2797866 prefixEnd_2797866 := by exact prefixLift 2797866
  have htrace : WordTrace (prefixWord ++ tailWord_2797866) baseStart_2797866 baseEnd_2797866 := by
    simpa [prefixWord, tailWord_2797866, baseEnd_2797866] using wordTrace_append hprefix tailTrace_2797866
  have hstable : (prefixWord ++ tailWord_2797866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2797866).length < 2 ^ (prefixWord ++ tailWord_2797866).sum := by decide
  have hdescent : baseEnd_2797866 < baseStart_2797866 := by decide
  rcases family_descends (prefixWord ++ tailWord_2797866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2797932 : List Nat := [2, 2, 1, 1, 6, 2, 2, 2, 1, 3]
def baseStart_2797932 : Nat := 118140960795 + 2797932 * 2 ^ 59
def prefixEnd_2797932 : Nat := 4983230072969 + 3 ^ 40 * 2797932 * 2
def baseEnd_2797932 : Nat := 957789303063768207921701

theorem tailTrace_2797932 : CollatzResearch.WordTrace tailWord_2797932 prefixEnd_2797932 957789303063768207921701 := by
  unfold tailWord_2797932
  simp only [CollatzResearch.WordTrace]
  refine ⟨51024481849788843793614025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68032642466385125058152033 51024481849788843793614025)
  ·
    refine ⟨38268361387341632845210519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51024481849788843793614025 38268361387341632845210519)
    ·
      refine ⟨57402542081012449267815779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38268361387341632845210519 57402542081012449267815779)
      ·
        refine ⟨86103813121518673901723669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57402542081012449267815779 86103813121518673901723669)
        ·
          refine ⟨4036116240071187839143297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 86103813121518673901723669 4036116240071187839143297)
          ·
            refine ⟨3027087180053390879357473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4036116240071187839143297 3027087180053390879357473)
            ·
              refine ⟨2270315385040043159518105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3027087180053390879357473 2270315385040043159518105)
              ·
                refine ⟨1702736538780032369638579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2270315385040043159518105 1702736538780032369638579)
                ·
                  refine ⟨2554104808170048554457869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1702736538780032369638579 2554104808170048554457869)
                  ·
                    refine ⟨957789303063768207921701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2554104808170048554457869 957789303063768207921701)
                    ·
                      rfl

theorem cell22_2797932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 2, 2, 1, 3].length) (baseStart_2797932 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2797932 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2797932 prefixEnd_2797932 := by exact prefixLift 2797932
  have htrace : WordTrace (prefixWord ++ tailWord_2797932) baseStart_2797932 baseEnd_2797932 := by
    simpa [prefixWord, tailWord_2797932, baseEnd_2797932] using wordTrace_append hprefix tailTrace_2797932
  have hstable : (prefixWord ++ tailWord_2797932).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2797932).length < 2 ^ (prefixWord ++ tailWord_2797932).sum := by decide
  have hdescent : baseEnd_2797932 < baseStart_2797932 := by decide
  rcases family_descends (prefixWord ++ tailWord_2797932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2797941 : List Nat := [1, 3, 4, 1, 2, 1, 1, 2, 3, 4]
def baseStart_2797941 : Nat := 118140960795 + 2797941 * 2 ^ 59
def prefixEnd_2797941 : Nat := 4983230072969 + 3 ^ 40 * 2797941 * 2
def baseEnd_2797941 : Nat := 957792383947695184446673

theorem tailTrace_2797941 : CollatzResearch.WordTrace tailWord_2797941 prefixEnd_2797941 957792383947695184446673 := by
  unfold tailWord_2797941
  simp only [CollatzResearch.WordTrace]
  refine ⟨102049291956545082124305677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68032861304363388082870451 102049291956545082124305677)
  ·
    refine ⟨38268484483704405796614629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102049291956545082124305677 38268484483704405796614629)
    ·
      refine ⟨7175340840694576086865243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38268484483704405796614629 7175340840694576086865243)
      ·
        refine ⟨10763011261041864130297865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7175340840694576086865243 10763011261041864130297865)
        ·
          refine ⟨8072258445781398097723399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10763011261041864130297865 8072258445781398097723399)
          ·
            refine ⟨12108387668672097146585099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8072258445781398097723399 12108387668672097146585099)
            ·
              refine ⟨18162581503008145719877649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12108387668672097146585099 18162581503008145719877649)
              ·
                refine ⟨13621936127256109289908237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18162581503008145719877649 13621936127256109289908237)
                ·
                  refine ⟨5108226047721040983715589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13621936127256109289908237 5108226047721040983715589)
                  ·
                    refine ⟨957792383947695184446673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5108226047721040983715589 957792383947695184446673)
                    ·
                      rfl

theorem cell22_2797941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 2, 3, 4].length) (baseStart_2797941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2797941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2797941 prefixEnd_2797941 := by exact prefixLift 2797941
  have htrace : WordTrace (prefixWord ++ tailWord_2797941) baseStart_2797941 baseEnd_2797941 := by
    simpa [prefixWord, tailWord_2797941, baseEnd_2797941] using wordTrace_append hprefix tailTrace_2797941
  have hstable : (prefixWord ++ tailWord_2797941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2797941).length < 2 ^ (prefixWord ++ tailWord_2797941).sum := by decide
  have hdescent : baseEnd_2797941 < baseStart_2797941 := by decide
  rcases family_descends (prefixWord ++ tailWord_2797941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2797984 : List Nat := [2, 1, 1, 4, 1, 4, 9]
def baseStart_2797984 : Nat := 118140960795 + 2797984 * 2 ^ 59
def prefixEnd_2797984 : Nat := 4983230072969 + 3 ^ 40 * 2797984 * 2
def baseEnd_2797984 : Nat := 35474337175053977985983

theorem tailTrace_2797984 : CollatzResearch.WordTrace tailWord_2797984 prefixEnd_2797984 35474337175053977985983 := by
  unfold tailWord_2797984
  simp only [CollatzResearch.WordTrace]
  refine ⟨51025430147694650234060503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68033906863592866978747337 51025430147694650234060503)
  ·
    refine ⟨76538145221541975351090755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51025430147694650234060503 76538145221541975351090755)
    ·
      refine ⟨114807217832312963026636133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76538145221541975351090755 114807217832312963026636133)
      ·
        refine ⟨21526353343558680567494275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 114807217832312963026636133 21526353343558680567494275)
        ·
          refine ⟨32289530015338020851241413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21526353343558680567494275 32289530015338020851241413)
          ·
            refine ⟨6054286877875878909607765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32289530015338020851241413 6054286877875878909607765)
            ·
              refine ⟨35474337175053977985983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6054286877875878909607765 35474337175053977985983)
              ·
                rfl

theorem cell22_2797984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 9].length) (baseStart_2797984 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2797984 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2797984 prefixEnd_2797984 := by exact prefixLift 2797984
  have htrace : WordTrace (prefixWord ++ tailWord_2797984) baseStart_2797984 baseEnd_2797984 := by
    simpa [prefixWord, tailWord_2797984, baseEnd_2797984] using wordTrace_append hprefix tailTrace_2797984
  have hstable : (prefixWord ++ tailWord_2797984).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2797984).length < 2 ^ (prefixWord ++ tailWord_2797984).sum := by decide
  have hdescent : baseEnd_2797984 < baseStart_2797984 := by decide
  rcases family_descends (prefixWord ++ tailWord_2797984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2797986 : List Nat := [3, 3, 1, 2, 1, 1, 2, 1, 4, 4]
def baseStart_2797986 : Nat := 118140960795 + 2797986 * 2 ^ 59
def prefixEnd_2797986 : Nat := 4983230072969 + 3 ^ 40 * 2797986 * 2
def baseEnd_2797986 : Nat := 957807788367330067071535

theorem tailTrace_2797986 : CollatzResearch.WordTrace tailWord_2797986 prefixEnd_2797986 957807788367330067071535 := by
  unfold tailWord_2797986
  simp only [CollatzResearch.WordTrace]
  refine ⟨25512733310345513702423453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68033955494254703206462541 25512733310345513702423453)
  ·
    refine ⟨9567274991379567638408795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25512733310345513702423453 9567274991379567638408795)
    ·
      refine ⟨14350912487069351457613193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9567274991379567638408795 14350912487069351457613193)
      ·
        refine ⟨10763184365302013593209895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14350912487069351457613193 10763184365302013593209895)
        ·
          refine ⟨16144776547953020389814843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10763184365302013593209895 16144776547953020389814843)
          ·
            refine ⟨24217164821929530584722265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16144776547953020389814843 24217164821929530584722265)
            ·
              refine ⟨18162873616447147938541699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24217164821929530584722265 18162873616447147938541699)
              ·
                refine ⟨27244310424670721907812549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18162873616447147938541699 27244310424670721907812549)
                ·
                  refine ⟨5108308204625760357714853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27244310424670721907812549 5108308204625760357714853)
                  ·
                    refine ⟨957807788367330067071535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5108308204625760357714853 957807788367330067071535)
                    ·
                      rfl

theorem cell22_2797986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 1, 4, 4].length) (baseStart_2797986 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2797986 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2797986 prefixEnd_2797986 := by exact prefixLift 2797986
  have htrace : WordTrace (prefixWord ++ tailWord_2797986) baseStart_2797986 baseEnd_2797986 := by
    simpa [prefixWord, tailWord_2797986, baseEnd_2797986] using wordTrace_append hprefix tailTrace_2797986
  have hstable : (prefixWord ++ tailWord_2797986).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2797986).length < 2 ^ (prefixWord ++ tailWord_2797986).sum := by decide
  have hdescent : baseEnd_2797986 < baseStart_2797986 := by decide
  rcases family_descends (prefixWord ++ tailWord_2797986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2797988 : List Nat := [2, 3, 1, 2, 1, 1, 5, 2, 2, 3]
def baseStart_2797988 : Nat := 118140960795 + 2797988 * 2 ^ 59
def prefixEnd_2797988 : Nat := 4983230072969 + 3 ^ 40 * 2797988 * 2
def baseEnd_2797988 : Nat := 957808473008202728521529

theorem tailTrace_2797988 : CollatzResearch.WordTrace tailWord_2797988 prefixEnd_2797988 957808473008202728521529 := by
  unfold tailWord_2797988
  simp only [CollatzResearch.WordTrace]
  refine ⟨51025503093687404575633309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68034004124916539434177745 51025503093687404575633309)
  ·
    refine ⟨19134563660132776715862491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51025503093687404575633309 19134563660132776715862491)
    ·
      refine ⟨28701845490199165073793737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19134563660132776715862491 28701845490199165073793737)
      ·
        refine ⟨21526384117649373805345303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28701845490199165073793737 21526384117649373805345303)
        ·
          refine ⟨32289576176474060708017955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21526384117649373805345303 32289576176474060708017955)
          ·
            refine ⟨48434364264711091062026933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32289576176474060708017955 48434364264711091062026933)
            ·
              refine ⟨4540721649816664787065025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 48434364264711091062026933 4540721649816664787065025)
              ·
                refine ⟨3405541237362498590298769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4540721649816664787065025 3405541237362498590298769)
                ·
                  refine ⟨2554155928021873942724077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3405541237362498590298769 2554155928021873942724077)
                  ·
                    refine ⟨957808473008202728521529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2554155928021873942724077 957808473008202728521529)
                    ·
                      rfl

theorem cell22_2797988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 5, 2, 2, 3].length) (baseStart_2797988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2797988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2797988 prefixEnd_2797988 := by exact prefixLift 2797988
  have htrace : WordTrace (prefixWord ++ tailWord_2797988) baseStart_2797988 baseEnd_2797988 := by
    simpa [prefixWord, tailWord_2797988, baseEnd_2797988] using wordTrace_append hprefix tailTrace_2797988
  have hstable : (prefixWord ++ tailWord_2797988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2797988).length < 2 ^ (prefixWord ++ tailWord_2797988).sum := by decide
  have hdescent : baseEnd_2797988 < baseStart_2797988 := by decide
  rcases family_descends (prefixWord ++ tailWord_2797988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2798005 : List Nat := [1, 3, 3, 2, 4, 1, 1, 1, 1, 5]
def baseStart_2798005 : Nat := 118140960795 + 2798005 * 2 ^ 59
def prefixEnd_2798005 : Nat := 4983230072969 + 3 ^ 40 * 2798005 * 2
def baseEnd_2798005 : Nat := 957814292455620350846477

theorem tailTrace_2798005 : CollatzResearch.WordTrace tailWord_2798005 prefixEnd_2798005 957814292455620350846477 := by
  unfold tailWord_2798005
  simp only [CollatzResearch.WordTrace]
  refine ⟨102051626228313221054635469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68034417485542147369756979 102051626228313221054635469)
  ·
    refine ⟨38269359835617457895488301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102051626228313221054635469 38269359835617457895488301)
    ·
      refine ⟨14351009938356546710808113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38269359835617457895488301 14351009938356546710808113)
      ·
        refine ⟨10763257453767410033106085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14351009938356546710808113 10763257453767410033106085)
        ·
          refine ⟨2018110772581389381207391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10763257453767410033106085 2018110772581389381207391)
          ·
            refine ⟨3027166158872084071811087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2018110772581389381207391 3027166158872084071811087)
            ·
              refine ⟨4540749238308126107716631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3027166158872084071811087 4540749238308126107716631)
              ·
                refine ⟨6811123857462189161574947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4540749238308126107716631 6811123857462189161574947)
                ·
                  refine ⟨10216685786193283742362421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6811123857462189161574947 10216685786193283742362421)
                  ·
                    refine ⟨957814292455620350846477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10216685786193283742362421 957814292455620350846477)
                    ·
                      rfl

theorem cell22_2798005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 1, 1, 1, 5].length) (baseStart_2798005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2798005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2798005 prefixEnd_2798005 := by exact prefixLift 2798005
  have htrace : WordTrace (prefixWord ++ tailWord_2798005) baseStart_2798005 baseEnd_2798005 := by
    simpa [prefixWord, tailWord_2798005, baseEnd_2798005] using wordTrace_append hprefix tailTrace_2798005
  have hstable : (prefixWord ++ tailWord_2798005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2798005).length < 2 ^ (prefixWord ++ tailWord_2798005).sum := by decide
  have hdescent : baseEnd_2798005 < baseStart_2798005 := by decide
  rcases family_descends (prefixWord ++ tailWord_2798005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2798138 : List Nat := [3, 1, 1, 1, 3, 3, 3, 1, 2, 4]
def baseStart_2798138 : Nat := 118140960795 + 2798138 * 2 ^ 59
def prefixEnd_2798138 : Nat := 4983230072969 + 3 ^ 40 * 2798138 * 2
def baseEnd_2798138 : Nat := 957859821073652337271069

theorem tailTrace_2798138 : CollatzResearch.WordTrace tailWord_2798138 prefixEnd_2798138 957859821073652337271069 := by
  unfold tailWord_2798138
  simp only [CollatzResearch.WordTrace]
  refine ⟨25514119284207846192306767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68037651424554256512818045 25514119284207846192306767)
  ·
    refine ⟨38271178926311769288460151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25514119284207846192306767 38271178926311769288460151)
    ·
      refine ⟨57406768389467653932690227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38271178926311769288460151 57406768389467653932690227)
      ·
        refine ⟨86110152584201480899035341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57406768389467653932690227 86110152584201480899035341)
        ·
          refine ⟨32291307219075555337138253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86110152584201480899035341 32291307219075555337138253)
          ·
            refine ⟨12109240207153333251426845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32291307219075555337138253 12109240207153333251426845)
            ·
              refine ⟨4540965077682499969285067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12109240207153333251426845 4540965077682499969285067)
              ·
                refine ⟨6811447616523749953927601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4540965077682499969285067 6811447616523749953927601)
                ·
                  refine ⟨5108585712392812465445701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6811447616523749953927601 5108585712392812465445701)
                  ·
                    refine ⟨957859821073652337271069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5108585712392812465445701 957859821073652337271069)
                    ·
                      rfl

theorem cell22_2798138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 3, 1, 2, 4].length) (baseStart_2798138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2798138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2798138 prefixEnd_2798138 := by exact prefixLift 2798138
  have htrace : WordTrace (prefixWord ++ tailWord_2798138) baseStart_2798138 baseEnd_2798138 := by
    simpa [prefixWord, tailWord_2798138, baseEnd_2798138] using wordTrace_append hprefix tailTrace_2798138
  have hstable : (prefixWord ++ tailWord_2798138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2798138).length < 2 ^ (prefixWord ++ tailWord_2798138).sum := by decide
  have hdescent : baseEnd_2798138 < baseStart_2798138 := by decide
  rcases family_descends (prefixWord ++ tailWord_2798138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2798157 : List Nat := [1, 6, 1, 1, 2, 1, 3, 2, 2, 3]
def baseStart_2798157 : Nat := 118140960795 + 2798157 * 2 ^ 59
def prefixEnd_2798157 : Nat := 4983230072969 + 3 ^ 40 * 2798157 * 2
def baseEnd_2798157 : Nat := 957866325161942621046011

theorem tailTrace_2798157 : CollatzResearch.WordTrace tailWord_2798157 prefixEnd_2798157 957866325161942621046011 := by
  unfold tailWord_2798157
  simp only [CollatzResearch.WordTrace]
  refine ⟨102057170123762551014168725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68038113415841700676112483 102057170123762551014168725)
  ·
    refine ⟨4783929849551369578789159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 102057170123762551014168725 4783929849551369578789159)
    ·
      refine ⟨7175894774327054368183739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4783929849551369578789159 7175894774327054368183739)
      ·
        refine ⟨10763842161490581552275609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7175894774327054368183739 10763842161490581552275609)
        ·
          refine ⟨8072881621117936164206707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10763842161490581552275609 8072881621117936164206707)
          ·
            refine ⟨12109322431676904246310061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8072881621117936164206707 12109322431676904246310061)
            ·
              refine ⟨4540995911878839092366273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12109322431676904246310061 4540995911878839092366273)
              ·
                refine ⟨3405746933909129319274705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4540995911878839092366273 3405746933909129319274705)
                ·
                  refine ⟨2554310200431846989456029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3405746933909129319274705 2554310200431846989456029)
                  ·
                    refine ⟨957866325161942621046011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2554310200431846989456029 957866325161942621046011)
                    ·
                      rfl

theorem cell22_2798157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 3, 2, 2, 3].length) (baseStart_2798157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2798157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2798157 prefixEnd_2798157 := by exact prefixLift 2798157
  have htrace : WordTrace (prefixWord ++ tailWord_2798157) baseStart_2798157 baseEnd_2798157 := by
    simpa [prefixWord, tailWord_2798157, baseEnd_2798157] using wordTrace_append hprefix tailTrace_2798157
  have hstable : (prefixWord ++ tailWord_2798157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2798157).length < 2 ^ (prefixWord ++ tailWord_2798157).sum := by decide
  have hdescent : baseEnd_2798157 < baseStart_2798157 := by decide
  rcases family_descends (prefixWord ++ tailWord_2798157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2798168 : List Nat := [2, 1, 2, 2, 1, 2, 3, 3, 3, 3]
def baseStart_2798168 : Nat := 118140960795 + 2798168 * 2 ^ 59
def prefixEnd_2798168 : Nat := 4983230072969 + 3 ^ 40 * 2798168 * 2
def baseEnd_2798168 : Nat := 957870090686742259020977

theorem tailTrace_2798168 : CollatzResearch.WordTrace tailWord_2798168 prefixEnd_2798168 957870090686742259020977 := by
  unfold tailWord_2798168
  simp only [CollatzResearch.WordTrace]
  refine ⟨51028785663361349946409579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68038380884481799928546105 51028785663361349946409579)
  ·
    refine ⟨76543178495042024919614369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51028785663361349946409579 76543178495042024919614369)
    ·
      refine ⟨57407383871281518689710777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76543178495042024919614369 57407383871281518689710777)
      ·
        refine ⟨43055537903461139017283083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57407383871281518689710777 43055537903461139017283083)
        ·
          refine ⟨64583306855191708525924625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43055537903461139017283083 64583306855191708525924625)
          ·
            refine ⟨48437480141393781394443469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64583306855191708525924625 48437480141393781394443469)
            ·
              refine ⟨18164055053022668022916301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48437480141393781394443469 18164055053022668022916301)
              ·
                refine ⟨6811520644883500508593613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18164055053022668022916301 6811520644883500508593613)
                ·
                  refine ⟨2554320241831312690722605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6811520644883500508593613 2554320241831312690722605)
                  ·
                    refine ⟨957870090686742259020977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2554320241831312690722605 957870090686742259020977)
                    ·
                      rfl

theorem cell22_2798168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 3, 3, 3].length) (baseStart_2798168 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2798168 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2798168 prefixEnd_2798168 := by exact prefixLift 2798168
  have htrace : WordTrace (prefixWord ++ tailWord_2798168) baseStart_2798168 baseEnd_2798168 := by
    simpa [prefixWord, tailWord_2798168, baseEnd_2798168] using wordTrace_append hprefix tailTrace_2798168
  have hstable : (prefixWord ++ tailWord_2798168).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2798168).length < 2 ^ (prefixWord ++ tailWord_2798168).sum := by decide
  have hdescent : baseEnd_2798168 < baseStart_2798168 := by decide
  rcases family_descends (prefixWord ++ tailWord_2798168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2798271 : List Nat := [1, 1, 2, 2, 2, 14]
def baseStart_2798271 : Nat := 118140960795 + 2798271 * 2 ^ 59
def prefixEnd_2798271 : Nat := 4983230072969 + 3 ^ 40 * 2798271 * 2
def baseEnd_2798271 : Nat := 11825991971502275601181

theorem tailTrace_2798271 : CollatzResearch.WordTrace tailWord_2798271 prefixEnd_2798271 11825991971502275601181 := by
  unfold tailWord_2798271
  simp only [CollatzResearch.WordTrace]
  refine ⟨102061328045349548483818667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68040885363566365655879111 102061328045349548483818667)
  ·
    refine ⟨153091992068024322725728001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102061328045349548483818667 153091992068024322725728001)
    ·
      refine ⟨114818994051018242044296001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153091992068024322725728001 114818994051018242044296001)
      ·
        refine ⟨86114245538263681533222001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114818994051018242044296001 86114245538263681533222001)
        ·
          refine ⟨64585684153697761149916501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86114245538263681533222001 64585684153697761149916501)
          ·
            refine ⟨11825991971502275601181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 14 64585684153697761149916501 11825991971502275601181)
            ·
              rfl

theorem cell22_2798271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 14].length) (baseStart_2798271 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2798271 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2798271 prefixEnd_2798271 := by exact prefixLift 2798271
  have htrace : WordTrace (prefixWord ++ tailWord_2798271) baseStart_2798271 baseEnd_2798271 := by
    simpa [prefixWord, tailWord_2798271, baseEnd_2798271] using wordTrace_append hprefix tailTrace_2798271
  have hstable : (prefixWord ++ tailWord_2798271).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2798271).length < 2 ^ (prefixWord ++ tailWord_2798271).sum := by decide
  have hdescent : baseEnd_2798271 < baseStart_2798271 := by decide
  rcases family_descends (prefixWord ++ tailWord_2798271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2798292 : List Nat := [2, 4, 1, 3, 2, 1, 2, 1, 1, 5]
def baseStart_2798292 : Nat := 118140960795 + 2798292 * 2 ^ 59
def prefixEnd_2798292 : Nat := 4983230072969 + 3 ^ 40 * 2798292 * 2
def baseEnd_2798292 : Nat := 957912538420847268920597

theorem tailTrace_2798292 : CollatzResearch.WordTrace tailWord_2798292 prefixEnd_2798292 957912538420847268920597 := by
  unfold tailWord_2798292
  simp only [CollatzResearch.WordTrace]
  refine ⟨51031046989136734535166565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68041395985515646046888753 51031046989136734535166565)
  ·
    refine ⟨9568321310463137725343731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51031046989136734535166565 9568321310463137725343731)
    ·
      refine ⟨14352481965694706588015597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9568321310463137725343731 14352481965694706588015597)
      ·
        refine ⟨5382180737135514970505849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14352481965694706588015597 5382180737135514970505849)
        ·
          refine ⟨4036635552851636227879387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5382180737135514970505849 4036635552851636227879387)
          ·
            refine ⟨6054953329277454341819081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4036635552851636227879387 6054953329277454341819081)
            ·
              refine ⟨4541214996958090756364311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6054953329277454341819081 4541214996958090756364311)
              ·
                refine ⟨6811822495437136134546467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4541214996958090756364311 6811822495437136134546467)
                ·
                  refine ⟨10217733743155704201819701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6811822495437136134546467 10217733743155704201819701)
                  ·
                    refine ⟨957912538420847268920597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10217733743155704201819701 957912538420847268920597)
                    ·
                      rfl

theorem cell22_2798292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 2, 1, 1, 5].length) (baseStart_2798292 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2798292 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2798292 prefixEnd_2798292 := by exact prefixLift 2798292
  have htrace : WordTrace (prefixWord ++ tailWord_2798292) baseStart_2798292 baseEnd_2798292 := by
    simpa [prefixWord, tailWord_2798292, baseEnd_2798292] using wordTrace_append hprefix tailTrace_2798292
  have hstable : (prefixWord ++ tailWord_2798292).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2798292).length < 2 ^ (prefixWord ++ tailWord_2798292).sum := by decide
  have hdescent : baseEnd_2798292 < baseStart_2798292 := by decide
  rcases family_descends (prefixWord ++ tailWord_2798292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2798305 : List Nat := [1, 2, 3, 1, 4, 2, 3, 6]
def baseStart_2798305 : Nat := 118140960795 + 2798305 * 2 ^ 59
def prefixEnd_2798305 : Nat := 4983230072969 + 3 ^ 40 * 2798305 * 2
def baseEnd_2798305 : Nat := 106435220954057729816173

theorem tailTrace_2798305 : CollatzResearch.WordTrace tailWord_2798305 prefixEnd_2798305 106435220954057729816173 := by
  unfold tailWord_2798305
  simp only [CollatzResearch.WordTrace]
  refine ⟨102062568127226372290556369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68041712084817581527037579 102062568127226372290556369)
  ·
    refine ⟨76546926095419779217917277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102062568127226372290556369 76546926095419779217917277)
    ·
      refine ⟨28705097285782417206718979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76546926095419779217917277 28705097285782417206718979)
      ·
        refine ⟨43057645928673625810078469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28705097285782417206718979 43057645928673625810078469)
        ·
          refine ⟨8073308611626304839389713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43057645928673625810078469 8073308611626304839389713)
          ·
            refine ⟨6054981458719728629542285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8073308611626304839389713 6054981458719728629542285)
            ·
              refine ⟨2270618047019898236078357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6054981458719728629542285 2270618047019898236078357)
              ·
                refine ⟨106435220954057729816173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2270618047019898236078357 106435220954057729816173)
                ·
                  rfl

theorem cell22_2798305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 3, 6].length) (baseStart_2798305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2798305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2798305 prefixEnd_2798305 := by exact prefixLift 2798305
  have htrace : WordTrace (prefixWord ++ tailWord_2798305) baseStart_2798305 baseEnd_2798305 := by
    simpa [prefixWord, tailWord_2798305, baseEnd_2798305] using wordTrace_append hprefix tailTrace_2798305
  have hstable : (prefixWord ++ tailWord_2798305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2798305).length < 2 ^ (prefixWord ++ tailWord_2798305).sum := by decide
  have hdescent : baseEnd_2798305 < baseStart_2798305 := by decide
  rcases family_descends (prefixWord ++ tailWord_2798305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2798307 : List Nat := [1, 1, 1, 7, 1, 3, 1, 1, 2, 4]
def baseStart_2798307 : Nat := 118140960795 + 2798307 * 2 ^ 59
def prefixEnd_2798307 : Nat := 4983230072969 + 3 ^ 40 * 2798307 * 2
def baseEnd_2798307 : Nat := 957917673227392229795551

theorem tailTrace_2798307 : CollatzResearch.WordTrace tailWord_2798307 prefixEnd_2798307 957917673227392229795551 := by
  unfold tailWord_2798307
  simp only [CollatzResearch.WordTrace]
  refine ⟨102062641073219126632129175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68041760715479417754752783 102062641073219126632129175)
  ·
    refine ⟨153093961609828689948193763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102062641073219126632129175 153093961609828689948193763)
    ·
      refine ⟨229640942414743034922290645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153093961609828689948193763 229640942414743034922290645)
      ·
        refine ⟨5382209587845539880991187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 229640942414743034922290645 5382209587845539880991187)
        ·
          refine ⟨8073314381768309821486781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5382209587845539880991187 8073314381768309821486781)
          ·
            refine ⟨3027492893163116183057543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8073314381768309821486781 3027492893163116183057543)
            ·
              refine ⟨4541239339744674274586315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3027492893163116183057543 4541239339744674274586315)
              ·
                refine ⟨6811859009617011411879473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4541239339744674274586315 6811859009617011411879473)
                ·
                  refine ⟨5108894257212758558909605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6811859009617011411879473 5108894257212758558909605)
                  ·
                    refine ⟨957917673227392229795551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5108894257212758558909605 957917673227392229795551)
                    ·
                      rfl

theorem cell22_2798307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 1, 1, 2, 4].length) (baseStart_2798307 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2798307 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2798307 prefixEnd_2798307 := by exact prefixLift 2798307
  have htrace : WordTrace (prefixWord ++ tailWord_2798307) baseStart_2798307 baseEnd_2798307 := by
    simpa [prefixWord, tailWord_2798307, baseEnd_2798307] using wordTrace_append hprefix tailTrace_2798307
  have hstable : (prefixWord ++ tailWord_2798307).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2798307).length < 2 ^ (prefixWord ++ tailWord_2798307).sum := by decide
  have hdescent : baseEnd_2798307 < baseStart_2798307 := by decide
  rcases family_descends (prefixWord ++ tailWord_2798307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2798333 : List Nat := [1, 4, 1, 1, 1, 1, 5, 1, 7]
def baseStart_2798333 : Nat := 118140960795 + 2798333 * 2 ^ 59
def prefixEnd_2798333 : Nat := 4983230072969 + 3 ^ 40 * 2798333 * 2
def baseEnd_2798333 : Nat := 319308857852912276215157

theorem tailTrace_2798333 : CollatzResearch.WordTrace tailWord_2798333 prefixEnd_2798333 319308857852912276215157 := by
  unfold tailWord_2798333
  simp only [CollatzResearch.WordTrace]
  refine ⟨102063589371124933072575653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68042392914083288715050435 102063589371124933072575653)
  ·
    refine ⟨19136923007085924951107935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 102063589371124933072575653 19136923007085924951107935)
    ·
      refine ⟨28705384510628887426661903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19136923007085924951107935 28705384510628887426661903)
      ·
        refine ⟨43058076765943331139992855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28705384510628887426661903 43058076765943331139992855)
        ·
          refine ⟨64587115148914996709989283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43058076765943331139992855 64587115148914996709989283)
          ·
            refine ⟨96880672723372495064983925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64587115148914996709989283 96880672723372495064983925)
            ·
              refine ⟨9082563067816171412342243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 96880672723372495064983925 9082563067816171412342243)
              ·
                refine ⟨13623844601724257118513365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9082563067816171412342243 13623844601724257118513365)
                ·
                  refine ⟨319308857852912276215157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13623844601724257118513365 319308857852912276215157)
                  ·
                    rfl

theorem cell22_2798333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 1, 7].length) (baseStart_2798333 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2798333 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2798333 prefixEnd_2798333 := by exact prefixLift 2798333
  have htrace : WordTrace (prefixWord ++ tailWord_2798333) baseStart_2798333 baseEnd_2798333 := by
    simpa [prefixWord, tailWord_2798333, baseEnd_2798333] using wordTrace_append hprefix tailTrace_2798333
  have hstable : (prefixWord ++ tailWord_2798333).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2798333).length < 2 ^ (prefixWord ++ tailWord_2798333).sum := by decide
  have hdescent : baseEnd_2798333 < baseStart_2798333 := by decide
  rcases family_descends (prefixWord ++ tailWord_2798333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2798380 : List Nat := [2, 2, 1, 1, 1, 4, 1, 5, 1, 4]
def baseStart_2798380 : Nat := 118140960795 + 2798380 * 2 ^ 59
def prefixEnd_2798380 : Nat := 4983230072969 + 3 ^ 40 * 2798380 * 2
def baseEnd_2798380 : Nat := 957942662619244372720327

theorem tailTrace_2798380 : CollatzResearch.WordTrace tailWord_2798380 prefixEnd_2798380 957942662619244372720327 := by
  unfold tailWord_2798380
  simp only [CollatzResearch.WordTrace]
  refine ⟨51032651800977330049768297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68043535734636440066357729 51032651800977330049768297)
  ·
    refine ⟨38274488850732997537326223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51032651800977330049768297 38274488850732997537326223)
    ·
      refine ⟨57411733276099496305989335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38274488850732997537326223 57411733276099496305989335)
      ·
        refine ⟨86117599914149244458984003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57411733276099496305989335 86117599914149244458984003)
        ·
          refine ⟨129176399871223866688476005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86117599914149244458984003 129176399871223866688476005)
          ·
            refine ⟨24220574975854475004089251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 129176399871223866688476005 24220574975854475004089251)
            ·
              refine ⟨36330862463781712506133877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24220574975854475004089251 36330862463781712506133877)
              ·
                refine ⟨3406018355979535547450051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36330862463781712506133877 3406018355979535547450051)
                ·
                  refine ⟨5109027533969303321175077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3406018355979535547450051 5109027533969303321175077)
                  ·
                    refine ⟨957942662619244372720327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5109027533969303321175077 957942662619244372720327)
                    ·
                      rfl

theorem cell22_2798380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 4].length) (baseStart_2798380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2798380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2798380 prefixEnd_2798380 := by exact prefixLift 2798380
  have htrace : WordTrace (prefixWord ++ tailWord_2798380) baseStart_2798380 baseEnd_2798380 := by
    simpa [prefixWord, tailWord_2798380, baseEnd_2798380] using wordTrace_append hprefix tailTrace_2798380
  have hstable : (prefixWord ++ tailWord_2798380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2798380).length < 2 ^ (prefixWord ++ tailWord_2798380).sum := by decide
  have hdescent : baseEnd_2798380 < baseStart_2798380 := by decide
  rcases family_descends (prefixWord ++ tailWord_2798380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2798388 : List Nat := [2, 5, 1, 1, 3, 1, 3, 2, 1, 3]
def baseStart_2798388 : Nat := 118140960795 + 2798388 * 2 ^ 59
def prefixEnd_2798388 : Nat := 4983230072969 + 3 ^ 40 * 2798388 * 2
def baseEnd_2798388 : Nat := 957945401182735018520303

theorem tailTrace_2798388 : CollatzResearch.WordTrace tailWord_2798388 prefixEnd_2798388 957945401182735018520303 := by
  unfold tailWord_2798388
  simp only [CollatzResearch.WordTrace]
  refine ⟨51032797692962838732913909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68043730257283784977218545 51032797692962838732913909)
  ·
    refine ⟨4784324783715266131210679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 51032797692962838732913909 4784324783715266131210679)
    ·
      refine ⟨7176487175572899196816019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4784324783715266131210679 7176487175572899196816019)
      ·
        refine ⟨10764730763359348795224029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7176487175572899196816019 10764730763359348795224029)
        ·
          refine ⟨4036774036259755798209011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10764730763359348795224029 4036774036259755798209011)
          ·
            refine ⟨6055161054389633697313517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4036774036259755798209011 6055161054389633697313517)
            ·
              refine ⟨2270685395396112636492569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6055161054389633697313517 2270685395396112636492569)
              ·
                refine ⟨1703014046547084477369427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2270685395396112636492569 1703014046547084477369427)
                ·
                  refine ⟨2554521069820626716054141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1703014046547084477369427 2554521069820626716054141)
                  ·
                    refine ⟨957945401182735018520303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2554521069820626716054141 957945401182735018520303)
                    ·
                      rfl

theorem cell22_2798388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 3, 2, 1, 3].length) (baseStart_2798388 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2798388 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2798388 prefixEnd_2798388 := by exact prefixLift 2798388
  have htrace : WordTrace (prefixWord ++ tailWord_2798388) baseStart_2798388 baseEnd_2798388 := by
    simpa [prefixWord, tailWord_2798388, baseEnd_2798388] using wordTrace_append hprefix tailTrace_2798388
  have hstable : (prefixWord ++ tailWord_2798388).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2798388).length < 2 ^ (prefixWord ++ tailWord_2798388).sum := by decide
  have hdescent : baseEnd_2798388 < baseStart_2798388 := by decide
  rcases family_descends (prefixWord ++ tailWord_2798388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2798401 : List Nat := [1, 2, 5, 3, 1, 2, 2, 1, 5]
def baseStart_2798401 : Nat := 118140960795 + 2798401 * 2 ^ 59
def prefixEnd_2798401 : Nat := 4983230072969 + 3 ^ 40 * 2798401 * 2
def baseEnd_2798401 : Nat := 319316617116135772648421

theorem tailTrace_2798401 : CollatzResearch.WordTrace tailWord_2798401 prefixEnd_2798401 319316617116135772648421 := by
  unfold tailWord_2798401
  simp only [CollatzResearch.WordTrace]
  refine ⟨102066069534878580686051057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68044046356585720457367371 102066069534878580686051057)
  ·
    refine ⟨76549552151158935514538293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102066069534878580686051057 76549552151158935514538293)
    ·
      refine ⟨7176520514171150204487965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 76549552151158935514538293 7176520514171150204487965)
      ·
        refine ⟨2691195192814181326682987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7176520514171150204487965 2691195192814181326682987)
        ·
          refine ⟨4036792789221271990024481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2691195192814181326682987 4036792789221271990024481)
          ·
            refine ⟨3027594591915953992518361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4036792789221271990024481 3027594591915953992518361)
            ·
              refine ⟨2270695943936965494388771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3027594591915953992518361 2270695943936965494388771)
              ·
                refine ⟨3406043915905448241583157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2270695943936965494388771 3406043915905448241583157)
                ·
                  refine ⟨319316617116135772648421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3406043915905448241583157 319316617116135772648421)
                  ·
                    rfl

theorem cell22_2798401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 2, 1, 5].length) (baseStart_2798401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2798401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2798401 prefixEnd_2798401 := by exact prefixLift 2798401
  have htrace : WordTrace (prefixWord ++ tailWord_2798401) baseStart_2798401 baseEnd_2798401 := by
    simpa [prefixWord, tailWord_2798401, baseEnd_2798401] using wordTrace_append hprefix tailTrace_2798401
  have hstable : (prefixWord ++ tailWord_2798401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2798401).length < 2 ^ (prefixWord ++ tailWord_2798401).sum := by decide
  have hdescent : baseEnd_2798401 < baseStart_2798401 := by decide
  rcases family_descends (prefixWord ++ tailWord_2798401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2798410 : List Nat := [3, 1, 2, 1, 1, 1, 2, 2, 6, 3]
def baseStart_2798410 : Nat := 118140960795 + 2798410 * 2 ^ 59
def prefixEnd_2798410 : Nat := 4983230072969 + 3 ^ 40 * 2798410 * 2
def baseEnd_2798410 : Nat := 957952932232334294470235

theorem tailTrace_2798410 : CollatzResearch.WordTrace tailWord_2798410 prefixEnd_2798410 957952932232334294470235 := by
  unfold tailWord_2798410
  simp only [CollatzResearch.WordTrace]
  refine ⟨25516599447961493805782171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68044265194563983482085789 25516599447961493805782171)
  ·
    refine ⟨38274899171942240708673257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25516599447961493805782171 38274899171942240708673257)
    ·
      refine ⟨28706174378956680531504943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38274899171942240708673257 28706174378956680531504943)
      ·
        refine ⟨43059261568435020797257415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28706174378956680531504943 43059261568435020797257415)
        ·
          refine ⟨64588892352652531195886123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43059261568435020797257415 64588892352652531195886123)
          ·
            refine ⟨96883338528978796793829185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64588892352652531195886123 96883338528978796793829185)
            ·
              refine ⟨72662503896734097595371889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96883338528978796793829185 72662503896734097595371889)
              ·
                refine ⟨54496877922550573196528917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72662503896734097595371889 54496877922550573196528917)
                ·
                  refine ⟨2554541152619558118587293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 54496877922550573196528917 2554541152619558118587293)
                  ·
                    refine ⟨957952932232334294470235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2554541152619558118587293 957952932232334294470235)
                    ·
                      rfl

theorem cell22_2798410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 2, 6, 3].length) (baseStart_2798410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2798410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2798410 prefixEnd_2798410 := by exact prefixLift 2798410
  have htrace : WordTrace (prefixWord ++ tailWord_2798410) baseStart_2798410 baseEnd_2798410 := by
    simpa [prefixWord, tailWord_2798410, baseEnd_2798410] using wordTrace_append hprefix tailTrace_2798410
  have hstable : (prefixWord ++ tailWord_2798410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2798410).length < 2 ^ (prefixWord ++ tailWord_2798410).sum := by decide
  have hdescent : baseEnd_2798410 < baseStart_2798410 := by decide
  rcases family_descends (prefixWord ++ tailWord_2798410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2798425 : List Nat := [1, 2, 1, 2, 2, 4, 1, 3, 2, 4]
def baseStart_2798425 : Nat := 118140960795 + 2798425 * 2 ^ 59
def prefixEnd_2798425 : Nat := 4983230072969 + 3 ^ 40 * 2798425 * 2
def baseEnd_2798425 : Nat := 957958067038879255345189

theorem tailTrace_2798425 : CollatzResearch.WordTrace tailWord_2798425 prefixEnd_2798425 957958067038879255345189 := by
  unfold tailWord_2798425
  simp only [CollatzResearch.WordTrace]
  refine ⟨102066944886791632784924729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68044629924527755189949819 102066944886791632784924729)
  ·
    refine ⟨76550208665093724588693547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102066944886791632784924729 76550208665093724588693547)
    ·
      refine ⟨114825312997640586883040321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76550208665093724588693547 114825312997640586883040321)
      ·
        refine ⟨86118984748230440162280241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114825312997640586883040321 86118984748230440162280241)
        ·
          refine ⟨64589238561172830121710181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86118984748230440162280241 64589238561172830121710181)
          ·
            refine ⟨12110482230219905647820659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64589238561172830121710181 12110482230219905647820659)
            ·
              refine ⟨18165723345329858471730989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12110482230219905647820659 18165723345329858471730989)
              ·
                refine ⟨6812146254498696926899121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18165723345329858471730989 6812146254498696926899121)
                ·
                  refine ⟨5109109690874022695174341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6812146254498696926899121 5109109690874022695174341)
                  ·
                    refine ⟨957958067038879255345189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5109109690874022695174341 957958067038879255345189)
                    ·
                      rfl

theorem cell22_2798425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 3, 2, 4].length) (baseStart_2798425 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2798425 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2798425 prefixEnd_2798425 := by exact prefixLift 2798425
  have htrace : WordTrace (prefixWord ++ tailWord_2798425) baseStart_2798425 baseEnd_2798425 := by
    simpa [prefixWord, tailWord_2798425, baseEnd_2798425] using wordTrace_append hprefix tailTrace_2798425
  have hstable : (prefixWord ++ tailWord_2798425).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2798425).length < 2 ^ (prefixWord ++ tailWord_2798425).sum := by decide
  have hdescent : baseEnd_2798425 < baseStart_2798425 := by decide
  rcases family_descends (prefixWord ++ tailWord_2798425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2798455 : List Nat := [1, 1, 3, 1, 1, 2, 1, 2, 7, 3]
def baseStart_2798455 : Nat := 118140960795 + 2798455 * 2 ^ 59
def prefixEnd_2798455 : Nat := 4983230072969 + 3 ^ 40 * 2798455 * 2
def baseEnd_2798455 : Nat := 957968336651969177095097

theorem tailTrace_2798455 : CollatzResearch.WordTrace tailWord_2798455 prefixEnd_2798455 957968336651969177095097 := by
  unfold tailWord_2798455
  simp only [CollatzResearch.WordTrace]
  refine ⟨102068039076682947908516819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68045359384455298605677879 102068039076682947908516819)
  ·
    refine ⟨153102058615024421862775229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102068039076682947908516819 153102058615024421862775229)
    ·
      refine ⟨57413271980634158198540711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 153102058615024421862775229 57413271980634158198540711)
      ·
        refine ⟨86119907970951237297811067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57413271980634158198540711 86119907970951237297811067)
        ·
          refine ⟨129179861956426855946716601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86119907970951237297811067 129179861956426855946716601)
          ·
            refine ⟨96884896467320141960037451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 129179861956426855946716601 96884896467320141960037451)
            ·
              refine ⟨145327344700980212940056177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96884896467320141960037451 145327344700980212940056177)
              ·
                refine ⟨108995508525735159705042133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 145327344700980212940056177 108995508525735159705042133)
                ·
                  refine ⟨2554582231071917805586925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 108995508525735159705042133 2554582231071917805586925)
                  ·
                    refine ⟨957968336651969177095097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2554582231071917805586925 957968336651969177095097)
                    ·
                      rfl

theorem cell22_2798455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 2, 7, 3].length) (baseStart_2798455 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2798455 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2798455 prefixEnd_2798455 := by exact prefixLift 2798455
  have htrace : WordTrace (prefixWord ++ tailWord_2798455) baseStart_2798455 baseEnd_2798455 := by
    simpa [prefixWord, tailWord_2798455, baseEnd_2798455] using wordTrace_append hprefix tailTrace_2798455
  have hstable : (prefixWord ++ tailWord_2798455).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2798455).length < 2 ^ (prefixWord ++ tailWord_2798455).sum := by decide
  have hdescent : baseEnd_2798455 < baseStart_2798455 := by decide
  rcases family_descends (prefixWord ++ tailWord_2798455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2798472 : List Nat := [2, 1, 3, 3, 2, 1, 1, 1, 5, 3]
def baseStart_2798472 : Nat := 118140960795 + 2798472 * 2 ^ 59
def prefixEnd_2798472 : Nat := 4983230072969 + 3 ^ 40 * 2798472 * 2
def baseEnd_2798472 : Nat := 957974156099386799420045

theorem tailTrace_2798472 : CollatzResearch.WordTrace tailWord_2798472 prefixEnd_2798472 957974156099386799420045 := by
  unfold tailWord_2798472
  simp only [CollatzResearch.WordTrace]
  refine ⟨51034329558810679905942835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68045772745080906541257113 51034329558810679905942835)
  ·
    refine ⟨76551494338216019858914253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51034329558810679905942835 76551494338216019858914253)
    ·
      refine ⟨28706810376831007447092845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76551494338216019858914253 28706810376831007447092845)
      ·
        refine ⟨10765053891311627792659817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28706810376831007447092845 10765053891311627792659817)
        ·
          refine ⟨8073790418483720844494863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10765053891311627792659817 8073790418483720844494863)
          ·
            refine ⟨12110685627725581266742295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8073790418483720844494863 12110685627725581266742295)
            ·
              refine ⟨18166028441588371900113443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12110685627725581266742295 18166028441588371900113443)
              ·
                refine ⟨27249042662382557850170165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18166028441588371900113443 27249042662382557850170165)
                ·
                  refine ⟨2554597749598364798453453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27249042662382557850170165 2554597749598364798453453)
                  ·
                    refine ⟨957974156099386799420045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2554597749598364798453453 957974156099386799420045)
                    ·
                      rfl

theorem cell22_2798472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 1, 5, 3].length) (baseStart_2798472 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2798472 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2798472 prefixEnd_2798472 := by exact prefixLift 2798472
  have htrace : WordTrace (prefixWord ++ tailWord_2798472) baseStart_2798472 baseEnd_2798472 := by
    simpa [prefixWord, tailWord_2798472, baseEnd_2798472] using wordTrace_append hprefix tailTrace_2798472
  have hstable : (prefixWord ++ tailWord_2798472).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2798472).length < 2 ^ (prefixWord ++ tailWord_2798472).sum := by decide
  have hdescent : baseEnd_2798472 < baseStart_2798472 := by decide
  rcases family_descends (prefixWord ++ tailWord_2798472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2798500 : List Nat := [2, 3, 1, 2, 1, 2, 1, 1, 4, 5]
def baseStart_2798500 : Nat := 118140960795 + 2798500 * 2 ^ 59
def prefixEnd_2798500 : Nat := 4983230072969 + 3 ^ 40 * 2798500 * 2
def baseEnd_2798500 : Nat := 957983741071604059719959

theorem tailTrace_2798500 : CollatzResearch.WordTrace tailWord_2798500 prefixEnd_2798500 957983741071604059719959 := by
  unfold tailWord_2798500
  simp only [CollatzResearch.WordTrace]
  refine ⟨51034840180759960296952477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68046453574346613729269969 51034840180759960296952477)
  ·
    refine ⟨19138065067784985111357179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51034840180759960296952477 19138065067784985111357179)
    ·
      refine ⟨28707097601677477667035769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19138065067784985111357179 28707097601677477667035769)
      ·
        refine ⟨21530323201258108250276827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28707097601677477667035769 21530323201258108250276827)
        ·
          refine ⟨32295484801887162375415241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21530323201258108250276827 32295484801887162375415241)
          ·
            refine ⟨24221613601415371781561431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32295484801887162375415241 24221613601415371781561431)
            ·
              refine ⟨36332420402123057672342147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24221613601415371781561431 36332420402123057672342147)
              ·
                refine ⟨54498630603184586508513221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36332420402123057672342147 54498630603184586508513221)
                ·
                  refine ⟨10218493238097109970346229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 54498630603184586508513221 10218493238097109970346229)
                  ·
                    refine ⟨957983741071604059719959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10218493238097109970346229 957983741071604059719959)
                    ·
                      rfl

theorem cell22_2798500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 1, 4, 5].length) (baseStart_2798500 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2798500 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2798500 prefixEnd_2798500 := by exact prefixLift 2798500
  have htrace : WordTrace (prefixWord ++ tailWord_2798500) baseStart_2798500 baseEnd_2798500 := by
    simpa [prefixWord, tailWord_2798500, baseEnd_2798500] using wordTrace_append hprefix tailTrace_2798500
  have hstable : (prefixWord ++ tailWord_2798500).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2798500).length < 2 ^ (prefixWord ++ tailWord_2798500).sum := by decide
  have hdescent : baseEnd_2798500 < baseStart_2798500 := by decide
  rcases family_descends (prefixWord ++ tailWord_2798500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2798515 : List Nat := [1, 1, 1, 2, 3, 1, 2, 4, 3, 4]
def baseStart_2798515 : Nat := 118140960795 + 2798515 * 2 ^ 59
def prefixEnd_2798515 : Nat := 4983230072969 + 3 ^ 40 * 2798515 * 2
def baseEnd_2798515 : Nat := 957988875878149020594913

theorem tailTrace_2798515 : CollatzResearch.WordTrace tailWord_2798515 prefixEnd_2798515 957988875878149020594913 := by
  unfold tailWord_2798515
  simp only [CollatzResearch.WordTrace]
  refine ⟨102070227456465578155700999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68046818304310385437133999 102070227456465578155700999)
  ·
    refine ⟨153105341184698367233551499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102070227456465578155700999 153105341184698367233551499)
    ·
      refine ⟨229658011777047550850327249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153105341184698367233551499 229658011777047550850327249)
      ·
        refine ⟨172243508832785663137745437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 229658011777047550850327249 172243508832785663137745437)
        ·
          refine ⟨64591315812294623676654539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 172243508832785663137745437 64591315812294623676654539)
          ·
            refine ⟨96886973718441935514981809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64591315812294623676654539 96886973718441935514981809)
            ·
              refine ⟨72665230288831451636236357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96886973718441935514981809 72665230288831451636236357)
              ·
                refine ⟨13624730679155897181794317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 72665230288831451636236357 13624730679155897181794317)
                ·
                  refine ⟨5109274004683461443172869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13624730679155897181794317 5109274004683461443172869)
                  ·
                    refine ⟨957988875878149020594913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5109274004683461443172869 957988875878149020594913)
                    ·
                      rfl

theorem cell22_2798515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 4, 3, 4].length) (baseStart_2798515 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2798515 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2798515 prefixEnd_2798515 := by exact prefixLift 2798515
  have htrace : WordTrace (prefixWord ++ tailWord_2798515) baseStart_2798515 baseEnd_2798515 := by
    simpa [prefixWord, tailWord_2798515, baseEnd_2798515] using wordTrace_append hprefix tailTrace_2798515
  have hstable : (prefixWord ++ tailWord_2798515).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2798515).length < 2 ^ (prefixWord ++ tailWord_2798515).sum := by decide
  have hdescent : baseEnd_2798515 < baseStart_2798515 := by decide
  rcases family_descends (prefixWord ++ tailWord_2798515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2798545 : List Nat := [1, 2, 2, 1, 2, 1, 4, 1, 3, 5]
def baseStart_2798545 : Nat := 118140960795 + 2798545 * 2 ^ 59
def prefixEnd_2798545 : Nat := 4983230072969 + 3 ^ 40 * 2798545 * 2
def baseEnd_2798545 : Nat := 957999145491238942344821

theorem tailTrace_2798545 : CollatzResearch.WordTrace tailWord_2798545 prefixEnd_2798545 957999145491238942344821 := by
  unfold tailWord_2798545
  simp only [CollatzResearch.WordTrace]
  refine ⟨102071321646356893279293089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68047547764237928852862059 102071321646356893279293089)
  ·
    refine ⟨76553491234767669959469817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102071321646356893279293089 76553491234767669959469817)
    ·
      refine ⟨57415118426075752469602363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76553491234767669959469817 57415118426075752469602363)
      ·
        refine ⟨86122677639113628704403545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57415118426075752469602363 86122677639113628704403545)
        ·
          refine ⟨64592008229335221528302659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86122677639113628704403545 64592008229335221528302659)
          ·
            refine ⟨96888012344002832292453989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64592008229335221528302659 96888012344002832292453989)
            ·
              refine ⟨18166502314500531054835123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 96888012344002832292453989 18166502314500531054835123)
              ·
                refine ⟨27249753471750796582252685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18166502314500531054835123 27249753471750796582252685)
                ·
                  refine ⟨10218657551906548718344757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27249753471750796582252685 10218657551906548718344757)
                  ·
                    refine ⟨957999145491238942344821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10218657551906548718344757 957999145491238942344821)
                    ·
                      rfl

theorem cell22_2798545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 1, 3, 5].length) (baseStart_2798545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2798545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2798545 prefixEnd_2798545 := by exact prefixLift 2798545
  have htrace : WordTrace (prefixWord ++ tailWord_2798545) baseStart_2798545 baseEnd_2798545 := by
    simpa [prefixWord, tailWord_2798545, baseEnd_2798545] using wordTrace_append hprefix tailTrace_2798545
  have hstable : (prefixWord ++ tailWord_2798545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2798545).length < 2 ^ (prefixWord ++ tailWord_2798545).sum := by decide
  have hdescent : baseEnd_2798545 < baseStart_2798545 := by decide
  rcases family_descends (prefixWord ++ tailWord_2798545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2798575 : List Nat := [1, 1, 2, 1, 4, 3, 1, 9]
def baseStart_2798575 : Nat := 118140960795 + 2798575 * 2 ^ 59
def prefixEnd_2798575 : Nat := 4983230072969 + 3 ^ 40 * 2798575 * 2
def baseEnd_2798575 : Nat := 106445490567147651566081

theorem tailTrace_2798575 : CollatzResearch.WordTrace tailWord_2798575 prefixEnd_2798575 106445490567147651566081 := by
  unfold tailWord_2798575
  simp only [CollatzResearch.WordTrace]
  refine ⟨102072415836248208402885179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68048277224165472268590119 102072415836248208402885179)
  ·
    refine ⟨153108623754372312604327769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102072415836248208402885179 153108623754372312604327769)
    ·
      refine ⟨114831467815779234453245827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153108623754372312604327769 114831467815779234453245827)
      ·
        refine ⟨172247201723668851679868741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114831467815779234453245827 172247201723668851679868741)
        ·
          refine ⟨32296350323187909689975389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 172247201723668851679868741 32296350323187909689975389)
          ·
            refine ⟨12111131371195466133740771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32296350323187909689975389 12111131371195466133740771)
            ·
              refine ⟨18166697056793199200611157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12111131371195466133740771 18166697056793199200611157)
              ·
                refine ⟨106445490567147651566081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18166697056793199200611157 106445490567147651566081)
                ·
                  rfl

theorem cell22_2798575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 9].length) (baseStart_2798575 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2798575 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2798575 prefixEnd_2798575 := by exact prefixLift 2798575
  have htrace : WordTrace (prefixWord ++ tailWord_2798575) baseStart_2798575 baseEnd_2798575 := by
    simpa [prefixWord, tailWord_2798575, baseEnd_2798575] using wordTrace_append hprefix tailTrace_2798575
  have hstable : (prefixWord ++ tailWord_2798575).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2798575).length < 2 ^ (prefixWord ++ tailWord_2798575).sum := by decide
  have hdescent : baseEnd_2798575 < baseStart_2798575 := by decide
  rcases family_descends (prefixWord ++ tailWord_2798575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2798669 : List Nat := [1, 6, 1, 1, 1, 2, 1, 2, 2, 5]
def baseStart_2798669 : Nat := 118140960795 + 2798669 * 2 ^ 59
def prefixEnd_2798669 : Nat := 4983230072969 + 3 ^ 40 * 2798669 * 2
def baseEnd_2798669 : Nat := 958041593225343952244441

theorem tailTrace_2798669 : CollatzResearch.WordTrace tailWord_2798669 prefixEnd_2798669 958041593225343952244441 := by
  unfold tailWord_2798669
  simp only [CollatzResearch.WordTrace]
  refine ⟨102075844297907662456807061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68050562865271774971204707 102075844297907662456807061)
  ·
    refine ⟨4784805201464421677662831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 102075844297907662456807061 4784805201464421677662831)
    ·
      refine ⟨7177207802196632516494247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4784805201464421677662831 7177207802196632516494247)
      ·
        refine ⟨10765811703294948774741371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7177207802196632516494247 10765811703294948774741371)
        ·
          refine ⟨16148717554942423162112057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10765811703294948774741371 16148717554942423162112057)
          ·
            refine ⟨12111538166206817371584043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16148717554942423162112057 12111538166206817371584043)
            ·
              refine ⟨18167307249310226057376065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12111538166206817371584043 18167307249310226057376065)
              ·
                refine ⟨13625480436982669543032049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18167307249310226057376065 13625480436982669543032049)
                ·
                  refine ⟨10219110327737002157274037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13625480436982669543032049 10219110327737002157274037)
                  ·
                    refine ⟨958041593225343952244441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10219110327737002157274037 958041593225343952244441)
                    ·
                      rfl

theorem cell22_2798669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 2, 2, 5].length) (baseStart_2798669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2798669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2798669 prefixEnd_2798669 := by exact prefixLift 2798669
  have htrace : WordTrace (prefixWord ++ tailWord_2798669) baseStart_2798669 baseEnd_2798669 := by
    simpa [prefixWord, tailWord_2798669, baseEnd_2798669] using wordTrace_append hprefix tailTrace_2798669
  have hstable : (prefixWord ++ tailWord_2798669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2798669).length < 2 ^ (prefixWord ++ tailWord_2798669).sum := by decide
  have hdescent : baseEnd_2798669 < baseStart_2798669 := by decide
  rcases family_descends (prefixWord ++ tailWord_2798669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2798701 : List Nat := [1, 5, 1, 1, 2, 3, 2, 2, 1, 4]
def baseStart_2798701 : Nat := 118140960795 + 2798701 * 2 ^ 59
def prefixEnd_2798701 : Nat := 4983230072969 + 3 ^ 40 * 2798701 * 2
def baseEnd_2798701 : Nat := 958052547479306535444343

theorem tailTrace_2798701 : CollatzResearch.WordTrace tailWord_2798701 prefixEnd_2798701 958052547479306535444343 := by
  unfold tailWord_2798701
  simp only [CollatzResearch.WordTrace]
  refine ⟨102077011433791731921971957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68051340955861154614647971 102077011433791731921971957)
  ·
    refine ⟨9569719821917974867684871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 102077011433791731921971957 9569719821917974867684871)
    ·
      refine ⟨14354579732876962301527307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9569719821917974867684871 14354579732876962301527307)
      ·
        refine ⟨21531869599315443452290961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14354579732876962301527307 21531869599315443452290961)
        ·
          refine ⟨16148902199486582589218221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21531869599315443452290961 16148902199486582589218221)
          ·
            refine ⟨6055838324807468470956833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16148902199486582589218221 6055838324807468470956833)
            ·
              refine ⟨4541878743605601353217625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6055838324807468470956833 4541878743605601353217625)
              ·
                refine ⟨3406409057704201014913219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4541878743605601353217625 3406409057704201014913219)
                ·
                  refine ⟨5109613586556301522369829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3406409057704201014913219 5109613586556301522369829)
                  ·
                    refine ⟨958052547479306535444343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5109613586556301522369829 958052547479306535444343)
                    ·
                      rfl

theorem cell22_2798701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 2, 2, 1, 4].length) (baseStart_2798701 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2798701 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2798701 prefixEnd_2798701 := by exact prefixLift 2798701
  have htrace : WordTrace (prefixWord ++ tailWord_2798701) baseStart_2798701 baseEnd_2798701 := by
    simpa [prefixWord, tailWord_2798701, baseEnd_2798701] using wordTrace_append hprefix tailTrace_2798701
  have hstable : (prefixWord ++ tailWord_2798701).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2798701).length < 2 ^ (prefixWord ++ tailWord_2798701).sum := by decide
  have hdescent : baseEnd_2798701 < baseStart_2798701 := by decide
  rcases family_descends (prefixWord ++ tailWord_2798701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2798712 : List Nat := [2, 1, 2, 1, 1, 1, 6, 1, 1, 6]
def baseStart_2798712 : Nat := 118140960795 + 2798712 * 2 ^ 59
def prefixEnd_2798712 : Nat := 4983230072969 + 3 ^ 40 * 2798712 * 2
def baseEnd_2798712 : Nat := 958056313004106173419309

theorem tailTrace_2798712 : CollatzResearch.WordTrace tailWord_2798712 prefixEnd_2798712 958056313004106173419309 := by
  unfold tailWord_2798712
  simp only [CollatzResearch.WordTrace]
  refine ⟨51038706318375940400311195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68051608424501253867081593 51038706318375940400311195)
  ·
    refine ⟨76558059477563910600466793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51038706318375940400311195 76558059477563910600466793)
    ·
      refine ⟨57418544608172932950350095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76558059477563910600466793 57418544608172932950350095)
      ·
        refine ⟨86127816912259399425525143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57418544608172932950350095 86127816912259399425525143)
        ·
          refine ⟨129191725368389099138287715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86127816912259399425525143 129191725368389099138287715)
          ·
            refine ⟨193787588052583648707431573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129191725368389099138287715 193787588052583648707431573)
            ·
              refine ⟨9083793189964858533160855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 193787588052583648707431573 9083793189964858533160855)
              ·
                refine ⟨13625689784947287799741283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9083793189964858533160855 13625689784947287799741283)
                ·
                  refine ⟨20438534677420931699611925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13625689784947287799741283 20438534677420931699611925)
                  ·
                    refine ⟨958056313004106173419309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20438534677420931699611925 958056313004106173419309)
                    ·
                      rfl

theorem cell22_2798712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 1, 1, 6].length) (baseStart_2798712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2798712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2798712 prefixEnd_2798712 := by exact prefixLift 2798712
  have htrace : WordTrace (prefixWord ++ tailWord_2798712) baseStart_2798712 baseEnd_2798712 := by
    simpa [prefixWord, tailWord_2798712, baseEnd_2798712] using wordTrace_append hprefix tailTrace_2798712
  have hstable : (prefixWord ++ tailWord_2798712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2798712).length < 2 ^ (prefixWord ++ tailWord_2798712).sum := by decide
  have hdescent : baseEnd_2798712 < baseStart_2798712 := by decide
  rcases family_descends (prefixWord ++ tailWord_2798712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2798729 : List Nat := [1, 2, 1, 1, 4, 4, 1, 2, 2, 4]
def baseStart_2798729 : Nat := 118140960795 + 2798729 * 2 ^ 59
def prefixEnd_2798729 : Nat := 4983230072969 + 3 ^ 40 * 2798729 * 2
def baseEnd_2798729 : Nat := 958062132451523795744257

theorem tailTrace_2798729 : CollatzResearch.WordTrace tailWord_2798729 prefixEnd_2798729 958062132451523795744257 := by
  unfold tailWord_2798729
  simp only [CollatzResearch.WordTrace]
  refine ⟨102078032677690292703991241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68052021785126861802660827 102078032677690292703991241)
  ·
    refine ⟨76558524508267719527993431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102078032677690292703991241 76558524508267719527993431)
    ·
      refine ⟨114837786762401579291990147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76558524508267719527993431 114837786762401579291990147)
      ·
        refine ⟨172256680143602368937985221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114837786762401579291990147 172256680143602368937985221)
        ·
          refine ⟨32298127526925444175872229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 172256680143602368937985221 32298127526925444175872229)
          ·
            refine ⟨6055898911298520782976043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32298127526925444175872229 6055898911298520782976043)
            ·
              refine ⟨9083848366947781174464065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6055898911298520782976043 9083848366947781174464065)
              ·
                refine ⟨6812886275210835880848049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9083848366947781174464065 6812886275210835880848049)
                ·
                  refine ⟨5109664706408126910636037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6812886275210835880848049 5109664706408126910636037)
                  ·
                    refine ⟨958062132451523795744257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5109664706408126910636037 958062132451523795744257)
                    ·
                      rfl

theorem cell22_2798729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 2, 2, 4].length) (baseStart_2798729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2798729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2798729 prefixEnd_2798729 := by exact prefixLift 2798729
  have htrace : WordTrace (prefixWord ++ tailWord_2798729) baseStart_2798729 baseEnd_2798729 := by
    simpa [prefixWord, tailWord_2798729, baseEnd_2798729] using wordTrace_append hprefix tailTrace_2798729
  have hstable : (prefixWord ++ tailWord_2798729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2798729).length < 2 ^ (prefixWord ++ tailWord_2798729).sum := by decide
  have hdescent : baseEnd_2798729 < baseStart_2798729 := by decide
  rcases family_descends (prefixWord ++ tailWord_2798729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2798744 : List Nat := [2, 1, 2, 4, 2, 2, 2, 7]
def baseStart_2798744 : Nat := 118140960795 + 2798744 * 2 ^ 59
def prefixEnd_2798744 : Nat := 4983230072969 + 3 ^ 40 * 2798744 * 2
def baseEnd_2798744 : Nat := 106451918584229861846579

theorem tailTrace_2798744 : CollatzResearch.WordTrace tailWord_2798744 prefixEnd_2798744 106451918584229861846579 := by
  unfold tailWord_2798744
  simp only [CollatzResearch.WordTrace]
  refine ⟨51039289886317975132893643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68052386515090633510524857 51039289886317975132893643)
  ·
    refine ⟨76558934829476962699340465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51039289886317975132893643 76558934829476962699340465)
    ·
      refine ⟨57419201122107722024505349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76558934829476962699340465 57419201122107722024505349)
      ·
        refine ⟨10766100210395197879594753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57419201122107722024505349 10766100210395197879594753)
        ·
          refine ⟨8074575157796398409696065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10766100210395197879594753 8074575157796398409696065)
          ·
            refine ⟨6055931368347298807272049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8074575157796398409696065 6055931368347298807272049)
            ·
              refine ⟨4541948526260474105454037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6055931368347298807272049 4541948526260474105454037)
              ·
                refine ⟨106451918584229861846579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4541948526260474105454037 106451918584229861846579)
                ·
                  rfl

theorem cell22_2798744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 2, 7].length) (baseStart_2798744 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2798744 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2798744 prefixEnd_2798744 := by exact prefixLift 2798744
  have htrace : WordTrace (prefixWord ++ tailWord_2798744) baseStart_2798744 baseEnd_2798744 := by
    simpa [prefixWord, tailWord_2798744, baseEnd_2798744] using wordTrace_append hprefix tailTrace_2798744
  have hstable : (prefixWord ++ tailWord_2798744).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2798744).length < 2 ^ (prefixWord ++ tailWord_2798744).sum := by decide
  have hdescent : baseEnd_2798744 < baseStart_2798744 := by decide
  rcases family_descends (prefixWord ++ tailWord_2798744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2798748 : List Nat := [2, 2, 3, 2, 1, 2, 4, 1, 2, 3]
def baseStart_2798748 : Nat := 118140960795 + 2798748 * 2 ^ 59
def prefixEnd_2798748 : Nat := 4983230072969 + 3 ^ 40 * 2798748 * 2
def baseEnd_2798748 : Nat := 958068636539814079519199

theorem tailTrace_2798748 : CollatzResearch.WordTrace tailWord_2798748 prefixEnd_2798748 958068636539814079519199 := by
  unfold tailWord_2798748
  simp only [CollatzResearch.WordTrace]
  refine ⟨51039362832310729474466449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68052483776414305965955265 51039362832310729474466449)
  ·
    refine ⟨38279522124233047105849837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51039362832310729474466449 38279522124233047105849837)
    ·
      refine ⟨14354820796587392664693689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38279522124233047105849837 14354820796587392664693689)
      ·
        refine ⟨10766115597440544498520267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14354820796587392664693689 10766115597440544498520267)
        ·
          refine ⟨16149173396160816747780401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10766115597440544498520267 16149173396160816747780401)
          ·
            refine ⟨12111880047120612560835301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16149173396160816747780401 12111880047120612560835301)
            ·
              refine ⟨2270977508835114855156619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12111880047120612560835301 2270977508835114855156619)
              ·
                refine ⟨3406466263252672282734929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2270977508835114855156619 3406466263252672282734929)
                ·
                  refine ⟨2554849697439504212051197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3406466263252672282734929 2554849697439504212051197)
                  ·
                    refine ⟨958068636539814079519199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2554849697439504212051197 958068636539814079519199)
                    ·
                      rfl

theorem cell22_2798748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 4, 1, 2, 3].length) (baseStart_2798748 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2798748 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2798748 prefixEnd_2798748 := by exact prefixLift 2798748
  have htrace : WordTrace (prefixWord ++ tailWord_2798748) baseStart_2798748 baseEnd_2798748 := by
    simpa [prefixWord, tailWord_2798748, baseEnd_2798748] using wordTrace_append hprefix tailTrace_2798748
  have hstable : (prefixWord ++ tailWord_2798748).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2798748).length < 2 ^ (prefixWord ++ tailWord_2798748).sum := by decide
  have hdescent : baseEnd_2798748 < baseStart_2798748 := by decide
  rcases family_descends (prefixWord ++ tailWord_2798748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2798851 : List Nat := [1, 1, 1, 3, 2, 4, 2, 4, 4]
def baseStart_2798851 : Nat := 118140960795 + 2798851 * 2 ^ 59
def prefixEnd_2798851 : Nat := 4983230072969 + 3 ^ 40 * 2798851 * 2
def baseEnd_2798851 : Nat := 319367965181585381397961

theorem tailTrace_2798851 : CollatzResearch.WordTrace tailWord_2798851 prefixEnd_2798851 319367965181585381397961 := by
  unfold tailWord_2798851
  simp only [CollatzResearch.WordTrace]
  refine ⟨102082482383248307539932407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68054988255498871693288271 102082482383248307539932407)
  ·
    refine ⟨153123723574872461309898611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102082482383248307539932407 153123723574872461309898611)
    ·
      refine ⟨229685585362308691964847917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153123723574872461309898611 229685585362308691964847917)
      ·
        refine ⟨86132094510865759486817969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 229685585362308691964847917 86132094510865759486817969)
        ·
          refine ⟨64599070883149319615113477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86132094510865759486817969 64599070883149319615113477)
          ·
            refine ⟨12112325790590497427833777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64599070883149319615113477 12112325790590497427833777)
            ·
              refine ⟨9084244342942873070875333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12112325790590497427833777 9084244342942873070875333)
              ·
                refine ⟨1703295814301788700789125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9084244342942873070875333 1703295814301788700789125)
                ·
                  refine ⟨319367965181585381397961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1703295814301788700789125 319367965181585381397961)
                  ·
                    rfl

theorem cell22_2798851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 4, 4].length) (baseStart_2798851 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2798851 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2798851 prefixEnd_2798851 := by exact prefixLift 2798851
  have htrace : WordTrace (prefixWord ++ tailWord_2798851) baseStart_2798851 baseEnd_2798851 := by
    simpa [prefixWord, tailWord_2798851, baseEnd_2798851] using wordTrace_append hprefix tailTrace_2798851
  have hstable : (prefixWord ++ tailWord_2798851).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2798851).length < 2 ^ (prefixWord ++ tailWord_2798851).sum := by decide
  have hdescent : baseEnd_2798851 < baseStart_2798851 := by decide
  rcases family_descends (prefixWord ++ tailWord_2798851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2798902 : List Nat := [5, 1, 2, 3, 2, 1, 1, 1, 6]
def baseStart_2798902 : Nat := 118140960795 + 2798902 * 2 ^ 59
def prefixEnd_2798902 : Nat := 4983230072969 + 3 ^ 40 * 2798902 * 2
def baseEnd_2798902 : Nat := 319373784629003003722909

theorem tailTrace_2798902 : CollatzResearch.WordTrace tailWord_2798902 prefixEnd_2798902 319373784629003003722909 := by
  unfold tailWord_2798902
  simp only [CollatzResearch.WordTrace]
  refine ⟨6380271406628971453127435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 68056228337375695500025973 6380271406628971453127435)
  ·
    refine ⟨9570407109943457179691153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6380271406628971453127435 9570407109943457179691153)
    ·
      refine ⟨7177805332457592884768365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9570407109943457179691153 7177805332457592884768365)
      ·
        refine ⟨2691676999671597331788137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7177805332457592884768365 2691676999671597331788137)
        ·
          refine ⟨2018757749753697998841103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2691676999671597331788137 2018757749753697998841103)
          ·
            refine ⟨3028136624630546998261655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2018757749753697998841103 3028136624630546998261655)
            ·
              refine ⟨4542204936945820497392483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3028136624630546998261655 4542204936945820497392483)
              ·
                refine ⟨6813307405418730746088725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4542204936945820497392483 6813307405418730746088725)
                ·
                  refine ⟨319373784629003003722909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6813307405418730746088725 319373784629003003722909)
                  ·
                    rfl

theorem cell22_2798902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 1, 1, 6].length) (baseStart_2798902 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2798902 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2798902 prefixEnd_2798902 := by exact prefixLift 2798902
  have htrace : WordTrace (prefixWord ++ tailWord_2798902) baseStart_2798902 baseEnd_2798902 := by
    simpa [prefixWord, tailWord_2798902, baseEnd_2798902] using wordTrace_append hprefix tailTrace_2798902
  have hstable : (prefixWord ++ tailWord_2798902).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2798902).length < 2 ^ (prefixWord ++ tailWord_2798902).sum := by decide
  have hdescent : baseEnd_2798902 < baseStart_2798902 := by decide
  rcases family_descends (prefixWord ++ tailWord_2798902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2799001 : List Nat := [1, 2, 1, 2, 1, 5, 2, 2, 1, 5]
def baseStart_2799001 : Nat := 118140960795 + 2799001 * 2 ^ 59
def prefixEnd_2799001 : Nat := 4983230072969 + 3 ^ 40 * 2799001 * 2
def baseEnd_2799001 : Nat := 958155243610205752943423

theorem tailTrace_2799001 : CollatzResearch.WordTrace tailWord_2799001 prefixEnd_2799001 958155243610205752943423 := by
  unfold tailWord_2799001
  simp only [CollatzResearch.WordTrace]
  refine ⟨102087953332704883157892857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68058635555136588771928571 102087953332704883157892857)
  ·
    refine ⟨76565964999528662368419643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102087953332704883157892857 76565964999528662368419643)
    ·
      refine ⟨114848947499292993552629465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76565964999528662368419643 114848947499292993552629465)
      ·
        refine ⟨86136710624469745164472099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114848947499292993552629465 86136710624469745164472099)
        ·
          refine ⟨129205065936704617746708149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86136710624469745164472099 129205065936704617746708149)
          ·
            refine ⟨12112974931566057913753889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 129205065936704617746708149 12112974931566057913753889)
            ·
              refine ⟨9084731198674543435315417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12112974931566057913753889 9084731198674543435315417)
              ·
                refine ⟨6813548399005907576486563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9084731198674543435315417 6813548399005907576486563)
                ·
                  refine ⟨10220322598508861364729845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6813548399005907576486563 10220322598508861364729845)
                  ·
                    refine ⟨958155243610205752943423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10220322598508861364729845 958155243610205752943423)
                    ·
                      rfl

theorem cell22_2799001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 2, 1, 5].length) (baseStart_2799001 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2799001 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2799001 prefixEnd_2799001 := by exact prefixLift 2799001
  have htrace : WordTrace (prefixWord ++ tailWord_2799001) baseStart_2799001 baseEnd_2799001 := by
    simpa [prefixWord, tailWord_2799001, baseEnd_2799001] using wordTrace_append hprefix tailTrace_2799001
  have hstable : (prefixWord ++ tailWord_2799001).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2799001).length < 2 ^ (prefixWord ++ tailWord_2799001).sum := by decide
  have hdescent : baseEnd_2799001 < baseStart_2799001 := by decide
  rcases family_descends (prefixWord ++ tailWord_2799001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2799005 : List Nat := [1, 4, 2, 1, 3, 1, 4, 1, 1, 4]
def baseStart_2799005 : Nat := 118140960795 + 2799005 * 2 ^ 59
def prefixEnd_2799005 : Nat := 4983230072969 + 3 ^ 40 * 2799005 * 2
def baseEnd_2799005 : Nat := 958156612891951075843411

theorem tailTrace_2799005 : CollatzResearch.WordTrace tailWord_2799005 prefixEnd_2799005 958156612891951075843411 := by
  unfold tailWord_2799005
  simp only [CollatzResearch.WordTrace]
  refine ⟨102088099224690391841038469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68058732816460261227358979 102088099224690391841038469)
  ·
    refine ⟨19141518604629448470194713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 102088099224690391841038469 19141518604629448470194713)
    ·
      refine ⟨14356138953472086352646035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19141518604629448470194713 14356138953472086352646035)
      ·
        refine ⟨21534208430208129528969053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14356138953472086352646035 21534208430208129528969053)
        ·
          refine ⟨8075328161328048573363395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21534208430208129528969053 8075328161328048573363395)
          ·
            refine ⟨12112992241992072860045093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8075328161328048573363395 12112992241992072860045093)
            ·
              refine ⟨2271186045373513661258455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12112992241992072860045093 2271186045373513661258455)
              ·
                refine ⟨3406779068060270491887683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2271186045373513661258455 3406779068060270491887683)
                ·
                  refine ⟨5110168602090405737831525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3406779068060270491887683 5110168602090405737831525)
                  ·
                    refine ⟨958156612891951075843411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5110168602090405737831525 958156612891951075843411)
                    ·
                      rfl

theorem cell22_2799005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 4, 1, 1, 4].length) (baseStart_2799005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2799005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2799005 prefixEnd_2799005 := by exact prefixLift 2799005
  have htrace : WordTrace (prefixWord ++ tailWord_2799005) baseStart_2799005 baseEnd_2799005 := by
    simpa [prefixWord, tailWord_2799005, baseEnd_2799005] using wordTrace_append hprefix tailTrace_2799005
  have hstable : (prefixWord ++ tailWord_2799005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2799005).length < 2 ^ (prefixWord ++ tailWord_2799005).sum := by decide
  have hdescent : baseEnd_2799005 < baseStart_2799005 := by decide
  rcases family_descends (prefixWord ++ tailWord_2799005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2799153 : List Nat := [1, 2, 2, 3, 1, 1, 1, 2, 6, 3]
def baseStart_2799153 : Nat := 118140960795 + 2799153 * 2 ^ 59
def prefixEnd_2799153 : Nat := 4983230072969 + 3 ^ 40 * 2799153 * 2
def baseEnd_2799153 : Nat := 958207276316528023142957

theorem tailTrace_2799153 : CollatzResearch.WordTrace tailWord_2799153 prefixEnd_2799153 958207276316528023142957 := by
  unfold tailWord_2799153
  simp only [CollatzResearch.WordTrace]
  refine ⟨102093497228154213117426113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68062331485436142078284075 102093497228154213117426113)
  ·
    refine ⟨76570122921115659838069585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102093497228154213117426113 76570122921115659838069585)
    ·
      refine ⟨57427592190836744878552189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76570122921115659838069585 57427592190836744878552189)
      ·
        refine ⟨21535347071563779329457071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57427592190836744878552189 21535347071563779329457071)
        ·
          refine ⟨32303020607345668994185607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21535347071563779329457071 32303020607345668994185607)
          ·
            refine ⟨48454530911018503491278411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32303020607345668994185607 48454530911018503491278411)
            ·
              refine ⟨72681796366527755236917617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48454530911018503491278411 72681796366527755236917617)
              ·
                refine ⟨54511347274895816427688213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72681796366527755236917617 54511347274895816427688213)
                ·
                  refine ⟨2555219403510741395047885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 54511347274895816427688213 2555219403510741395047885)
                  ·
                    refine ⟨958207276316528023142957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2555219403510741395047885 958207276316528023142957)
                    ·
                      rfl

theorem cell22_2799153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 2, 6, 3].length) (baseStart_2799153 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2799153 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2799153 prefixEnd_2799153 := by exact prefixLift 2799153
  have htrace : WordTrace (prefixWord ++ tailWord_2799153) baseStart_2799153 baseEnd_2799153 := by
    simpa [prefixWord, tailWord_2799153, baseEnd_2799153] using wordTrace_append hprefix tailTrace_2799153
  have hstable : (prefixWord ++ tailWord_2799153).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2799153).length < 2 ^ (prefixWord ++ tailWord_2799153).sum := by decide
  have hdescent : baseEnd_2799153 < baseStart_2799153 := by decide
  rcases family_descends (prefixWord ++ tailWord_2799153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2799174 : List Nat := [6, 1, 1, 1, 3, 1, 1, 3, 1, 4]
def baseStart_2799174 : Nat := 118140960795 + 2799174 * 2 ^ 59
def prefixEnd_2799174 : Nat := 4983230072969 + 3 ^ 40 * 2799174 * 2
def baseEnd_2799174 : Nat := 958214465045690968367893

theorem tailTrace_2799174 : CollatzResearch.WordTrace tailWord_2799174 prefixEnd_2799174 958214465045690968367893 := by
  unfold tailWord_2799174
  simp only [CollatzResearch.WordTrace]
  refine ⟨3190445723783691678248143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 68062842107385422469293717 3190445723783691678248143)
  ·
    refine ⟨4785668585675537517372215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3190445723783691678248143 4785668585675537517372215)
    ·
      refine ⟨7178502878513306276058323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4785668585675537517372215 7178502878513306276058323)
      ·
        refine ⟨10767754317769959414087485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7178502878513306276058323 10767754317769959414087485)
        ·
          refine ⟨4037907869163734780282807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10767754317769959414087485 4037907869163734780282807)
          ·
            refine ⟨6056861803745602170424211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4037907869163734780282807 6056861803745602170424211)
            ·
              refine ⟨9085292705618403255636317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6056861803745602170424211 9085292705618403255636317)
              ·
                refine ⟨3406984764606901220863619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9085292705618403255636317 3406984764606901220863619)
                ·
                  refine ⟨5110477146910351831295429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3406984764606901220863619 5110477146910351831295429)
                  ·
                    refine ⟨958214465045690968367893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5110477146910351831295429 958214465045690968367893)
                    ·
                      rfl

theorem cell22_2799174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 3, 1, 4].length) (baseStart_2799174 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2799174 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2799174 prefixEnd_2799174 := by exact prefixLift 2799174
  have htrace : WordTrace (prefixWord ++ tailWord_2799174) baseStart_2799174 baseEnd_2799174 := by
    simpa [prefixWord, tailWord_2799174, baseEnd_2799174] using wordTrace_append hprefix tailTrace_2799174
  have hstable : (prefixWord ++ tailWord_2799174).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2799174).length < 2 ^ (prefixWord ++ tailWord_2799174).sum := by decide
  have hdescent : baseEnd_2799174 < baseStart_2799174 := by decide
  rcases family_descends (prefixWord ++ tailWord_2799174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2799262 : List Nat := [4, 3, 1, 1, 1, 3, 1, 3, 5]
def baseStart_2799262 : Nat := 118140960795 + 2799262 * 2 ^ 59
def prefixEnd_2799262 : Nat := 4983230072969 + 3 ^ 40 * 2799262 * 2
def baseEnd_2799262 : Nat := 319414863081362690722541

theorem tailTrace_2799262 : CollatzResearch.WordTrace tailWord_2799262 prefixEnd_2799262 319414863081362690722541 := by
  unfold tailWord_2799262
  simp only [CollatzResearch.WordTrace]
  refine ⟨12762184098094915591643005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68064981856506216488762693 12762184098094915591643005)
  ·
    refine ⟨4785819036785593346866127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12762184098094915591643005 4785819036785593346866127)
    ·
      refine ⟨7178728555178390020299191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4785819036785593346866127 7178728555178390020299191)
      ·
        refine ⟨10768092832767585030448787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7178728555178390020299191 10768092832767585030448787)
        ·
          refine ⟨16152139249151377545673181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10768092832767585030448787 16152139249151377545673181)
          ·
            refine ⟨6057052218431766579627443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16152139249151377545673181 6057052218431766579627443)
            ·
              refine ⟨9085578327647649869441165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6057052218431766579627443 9085578327647649869441165)
              ·
                refine ⟨3407091872867868701040437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9085578327647649869441165 3407091872867868701040437)
                ·
                  refine ⟨319414863081362690722541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3407091872867868701040437 319414863081362690722541)
                  ·
                    rfl

theorem cell22_2799262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 3, 5].length) (baseStart_2799262 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2799262 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2799262 prefixEnd_2799262 := by exact prefixLift 2799262
  have htrace : WordTrace (prefixWord ++ tailWord_2799262) baseStart_2799262 baseEnd_2799262 := by
    simpa [prefixWord, tailWord_2799262, baseEnd_2799262] using wordTrace_append hprefix tailTrace_2799262
  have hstable : (prefixWord ++ tailWord_2799262).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2799262).length < 2 ^ (prefixWord ++ tailWord_2799262).sum := by decide
  have hdescent : baseEnd_2799262 < baseStart_2799262 := by decide
  rcases family_descends (prefixWord ++ tailWord_2799262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2799322 : List Nat := [3, 1, 1, 2, 2, 3, 2, 3, 2, 3]
def baseStart_2799322 : Nat := 118140960795 + 2799322 * 2 ^ 59
def prefixEnd_2799322 : Nat := 4983230072969 + 3 ^ 40 * 2799322 * 2
def baseEnd_2799322 : Nat := 958265128470267915667439

theorem tailTrace_2799322 : CollatzResearch.WordTrace tailWord_2799322 prefixEnd_2799322 958265128470267915667439 := by
  unfold tailWord_2799322
  simp only [CollatzResearch.WordTrace]
  refine ⟨25524915291135488745082055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68066440776361303320218813 25524915291135488745082055)
  ·
    refine ⟨38287372936703233117623083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25524915291135488745082055 38287372936703233117623083)
    ·
      refine ⟨57431059405054849676434625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38287372936703233117623083 57431059405054849676434625)
      ·
        refine ⟨43073294553791137257325969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57431059405054849676434625 43073294553791137257325969)
        ·
          refine ⟨32304970915343352942994477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43073294553791137257325969 32304970915343352942994477)
          ·
            refine ⟨12114364093253757353622929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32304970915343352942994477 12114364093253757353622929)
            ·
              refine ⟨9085773069940318015217197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12114364093253757353622929 9085773069940318015217197)
              ·
                refine ⟨3407164901227619255706449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9085773069940318015217197 3407164901227619255706449)
                ·
                  refine ⟨2555373675920714441779837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3407164901227619255706449 2555373675920714441779837)
                  ·
                    refine ⟨958265128470267915667439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2555373675920714441779837 958265128470267915667439)
                    ·
                      rfl

theorem cell22_2799322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 3, 2, 3].length) (baseStart_2799322 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2799322 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2799322 prefixEnd_2799322 := by exact prefixLift 2799322
  have htrace : WordTrace (prefixWord ++ tailWord_2799322) baseStart_2799322 baseEnd_2799322 := by
    simpa [prefixWord, tailWord_2799322, baseEnd_2799322] using wordTrace_append hprefix tailTrace_2799322
  have hstable : (prefixWord ++ tailWord_2799322).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2799322).length < 2 ^ (prefixWord ++ tailWord_2799322).sum := by decide
  have hdescent : baseEnd_2799322 < baseStart_2799322 := by decide
  rcases family_descends (prefixWord ++ tailWord_2799322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2799440 : List Nat := [2, 1, 1, 1, 1, 4, 1, 5, 1, 5]
def baseStart_2799440 : Nat := 118140960795 + 2799440 * 2 ^ 59
def prefixEnd_2799440 : Nat := 4983230072969 + 3 ^ 40 * 2799440 * 2
def baseEnd_2799440 : Nat := 958305522281754941217077

theorem tailTrace_2799440 : CollatzResearch.WordTrace tailWord_2799440 prefixEnd_2799440 958305522281754941217077 := by
  unfold tailWord_2799440
  simp only [CollatzResearch.WordTrace]
  refine ⟨51051982489057230566561887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68069309985409640755415849 51051982489057230566561887)
  ·
    refine ⟨76577973733585845849842831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51051982489057230566561887 76577973733585845849842831)
    ·
      refine ⟨114866960600378768774764247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76577973733585845849842831 114866960600378768774764247)
      ·
        refine ⟨172300440900568153162146371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114866960600378768774764247 172300440900568153162146371)
        ·
          refine ⟨258450661350852229743219557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172300440900568153162146371 258450661350852229743219557)
          ·
            refine ⟨48459499003284793076853667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 258450661350852229743219557 48459499003284793076853667)
            ·
              refine ⟨72689248504927189615280501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48459499003284793076853667 72689248504927189615280501)
              ·
                refine ⟨6814617047336924026432547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 72689248504927189615280501 6814617047336924026432547)
                ·
                  refine ⟨10221925571005386039648821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6814617047336924026432547 10221925571005386039648821)
                  ·
                    refine ⟨958305522281754941217077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10221925571005386039648821 958305522281754941217077)
                    ·
                      rfl

theorem cell22_2799440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 5, 1, 5].length) (baseStart_2799440 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2799440 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2799440 prefixEnd_2799440 := by exact prefixLift 2799440
  have htrace : WordTrace (prefixWord ++ tailWord_2799440) baseStart_2799440 baseEnd_2799440 := by
    simpa [prefixWord, tailWord_2799440, baseEnd_2799440] using wordTrace_append hprefix tailTrace_2799440
  have hstable : (prefixWord ++ tailWord_2799440).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2799440).length < 2 ^ (prefixWord ++ tailWord_2799440).sum := by decide
  have hdescent : baseEnd_2799440 < baseStart_2799440 := by decide
  rcases family_descends (prefixWord ++ tailWord_2799440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2799444 : List Nat := [2, 4, 1, 1, 3, 1, 3, 2, 1, 4]
def baseStart_2799444 : Nat := 118140960795 + 2799444 * 2 ^ 59
def prefixEnd_2799444 : Nat := 4983230072969 + 3 ^ 40 * 2799444 * 2
def baseEnd_2799444 : Nat := 958306891563500264117065

theorem tailTrace_2799444 : CollatzResearch.WordTrace tailWord_2799444 prefixEnd_2799444 958306891563500264117065 := by
  unfold tailWord_2799444
  simp only [CollatzResearch.WordTrace]
  refine ⟨51052055435049984908134693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68069407246733313210846257 51052055435049984908134693)
  ·
    refine ⟨9572260394071872170275255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51052055435049984908134693 9572260394071872170275255)
    ·
      refine ⟨14358390591107808255412883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9572260394071872170275255 14358390591107808255412883)
      ·
        refine ⟨21537585886661712383119325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14358390591107808255412883 21537585886661712383119325)
        ·
          refine ⟨8076594707498142143669747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21537585886661712383119325 8076594707498142143669747)
          ·
            refine ⟨12114892061247213215504621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8076594707498142143669747 12114892061247213215504621)
            ·
              refine ⟨4543084522967704955814233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12114892061247213215504621 4543084522967704955814233)
              ·
                refine ⟨3407313392225778716860675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4543084522967704955814233 3407313392225778716860675)
                ·
                  refine ⟨5110970088338668075291013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3407313392225778716860675 5110970088338668075291013)
                  ·
                    refine ⟨958306891563500264117065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5110970088338668075291013 958306891563500264117065)
                    ·
                      rfl

theorem cell22_2799444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 3, 2, 1, 4].length) (baseStart_2799444 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2799444 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2799444 prefixEnd_2799444 := by exact prefixLift 2799444
  have htrace : WordTrace (prefixWord ++ tailWord_2799444) baseStart_2799444 baseEnd_2799444 := by
    simpa [prefixWord, tailWord_2799444, baseEnd_2799444] using wordTrace_append hprefix tailTrace_2799444
  have hstable : (prefixWord ++ tailWord_2799444).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2799444).length < 2 ^ (prefixWord ++ tailWord_2799444).sum := by decide
  have hdescent : baseEnd_2799444 < baseStart_2799444 := by decide
  rcases family_descends (prefixWord ++ tailWord_2799444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2799485 : List Nat := [1, 4, 1, 1, 2, 1, 1, 2, 2, 7]
def baseStart_2799485 : Nat := 118140960795 + 2799485 * 2 ^ 59
def prefixEnd_2799485 : Nat := 4983230072969 + 3 ^ 40 * 2799485 * 2
def baseEnd_2799485 : Nat := 958320926701389823841939

theorem tailTrace_2799485 : CollatzResearch.WordTrace tailWord_2799485 prefixEnd_2799485 958320926701389823841939 := by
  unfold tailWord_2799485
  simp only [CollatzResearch.WordTrace]
  refine ⟨102105606262951433818511909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68070404175300955879007939 102105606262951433818511909)
  ·
    refine ⟨19144801174303393840970983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 102105606262951433818511909 19144801174303393840970983)
    ·
      refine ⟨28717201761455090761456475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19144801174303393840970983 28717201761455090761456475)
      ·
        refine ⟨43075802642182636142184713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28717201761455090761456475 43075802642182636142184713)
        ·
          refine ⟨32306851981636977106638535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43075802642182636142184713 32306851981636977106638535)
          ·
            refine ⟨48460277972455465659957803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32306851981636977106638535 48460277972455465659957803)
            ·
              refine ⟨72690416958683198489936705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48460277972455465659957803 72690416958683198489936705)
              ·
                refine ⟨54517812719012398867452529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72690416958683198489936705 54517812719012398867452529)
                ·
                  refine ⟨40888359539259299150589397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54517812719012398867452529 40888359539259299150589397)
                  ·
                    refine ⟨958320926701389823841939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40888359539259299150589397 958320926701389823841939)
                    ·
                      rfl

theorem cell22_2799485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 2, 2, 7].length) (baseStart_2799485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2799485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2799485 prefixEnd_2799485 := by exact prefixLift 2799485
  have htrace : WordTrace (prefixWord ++ tailWord_2799485) baseStart_2799485 baseEnd_2799485 := by
    simpa [prefixWord, tailWord_2799485, baseEnd_2799485] using wordTrace_append hprefix tailTrace_2799485
  have hstable : (prefixWord ++ tailWord_2799485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2799485).length < 2 ^ (prefixWord ++ tailWord_2799485).sum := by decide
  have hdescent : baseEnd_2799485 < baseStart_2799485 := by decide
  rcases family_descends (prefixWord ++ tailWord_2799485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2799500 : List Nat := [2, 2, 1, 2, 1, 2, 1, 1, 4, 6]
def baseStart_2799500 : Nat := 118140960795 + 2799500 * 2 ^ 59
def prefixEnd_2799500 : Nat := 4983230072969 + 3 ^ 40 * 2799500 * 2
def baseEnd_2799500 : Nat := 958326061507934784716893

theorem tailTrace_2799500 : CollatzResearch.WordTrace tailWord_2799500 prefixEnd_2799500 958326061507934784716893 := by
  unfold tailWord_2799500
  simp only [CollatzResearch.WordTrace]
  refine ⟨51053076678948545690153977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68070768905264727586871969 51053076678948545690153977)
  ·
    refine ⟨38289807509211409267615483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51053076678948545690153977 38289807509211409267615483)
    ·
      refine ⟨57434711263817113901423225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38289807509211409267615483 57434711263817113901423225)
      ·
        refine ⟨43076033447862835426067419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57434711263817113901423225 43076033447862835426067419)
        ·
          refine ⟨64614050171794253139101129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43076033447862835426067419 64614050171794253139101129)
          ·
            refine ⟨48460537628845689854325847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64614050171794253139101129 48460537628845689854325847)
            ·
              refine ⟨72690806443268534781488771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48460537628845689854325847 72690806443268534781488771)
              ·
                refine ⟨109036209664902802172233157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72690806443268534781488771 109036209664902802172233157)
                ·
                  refine ⟨20444289312169275407293717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 109036209664902802172233157 20444289312169275407293717)
                  ·
                    refine ⟨958326061507934784716893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20444289312169275407293717 958326061507934784716893)
                    ·
                      rfl

theorem cell22_2799500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 4, 6].length) (baseStart_2799500 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2799500 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2799500 prefixEnd_2799500 := by exact prefixLift 2799500
  have htrace : WordTrace (prefixWord ++ tailWord_2799500) baseStart_2799500 baseEnd_2799500 := by
    simpa [prefixWord, tailWord_2799500, baseEnd_2799500] using wordTrace_append hprefix tailTrace_2799500
  have hstable : (prefixWord ++ tailWord_2799500).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2799500).length < 2 ^ (prefixWord ++ tailWord_2799500).sum := by decide
  have hdescent : baseEnd_2799500 < baseStart_2799500 := by decide
  rcases family_descends (prefixWord ++ tailWord_2799500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2799506 : List Nat := [3, 2, 3, 2, 1, 3, 1, 1, 2, 4]
def baseStart_2799506 : Nat := 118140960795 + 2799506 * 2 ^ 59
def prefixEnd_2799506 : Nat := 4983230072969 + 3 ^ 40 * 2799506 * 2
def baseEnd_2799506 : Nat := 958328115430552769066875

theorem tailTrace_2799506 : CollatzResearch.WordTrace tailWord_2799506 prefixEnd_2799506 958328115430552769066875 := by
  unfold tailWord_2799506
  simp only [CollatzResearch.WordTrace]
  refine ⟨25526593048968838601256593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68070914797250236270017581 25526593048968838601256593)
  ·
    refine ⟨19144944786726628950942445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25526593048968838601256593 19144944786726628950942445)
    ·
      refine ⟨7179354295022485856603417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19144944786726628950942445 7179354295022485856603417)
      ·
        refine ⟨5384515721266864392452563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7179354295022485856603417 5384515721266864392452563)
        ·
          refine ⟨8076773581900296588678845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5384515721266864392452563 8076773581900296588678845)
          ·
            refine ⟨3028790093212611220754567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8076773581900296588678845 3028790093212611220754567)
            ·
              refine ⟨4543185139818916831131851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3028790093212611220754567 4543185139818916831131851)
              ·
                refine ⟨6814777709728375246697777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4543185139818916831131851 6814777709728375246697777)
                ·
                  refine ⟨5111083282296281435023333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6814777709728375246697777 5111083282296281435023333)
                  ·
                    refine ⟨958328115430552769066875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5111083282296281435023333 958328115430552769066875)
                    ·
                      rfl

theorem cell22_2799506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 1, 1, 2, 4].length) (baseStart_2799506 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2799506 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2799506 prefixEnd_2799506 := by exact prefixLift 2799506
  have htrace : WordTrace (prefixWord ++ tailWord_2799506) baseStart_2799506 baseEnd_2799506 := by
    simpa [prefixWord, tailWord_2799506, baseEnd_2799506] using wordTrace_append hprefix tailTrace_2799506
  have hstable : (prefixWord ++ tailWord_2799506).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2799506).length < 2 ^ (prefixWord ++ tailWord_2799506).sum := by decide
  have hdescent : baseEnd_2799506 < baseStart_2799506 := by decide
  rcases family_descends (prefixWord ++ tailWord_2799506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2799510 : List Nat := [5, 3, 1, 1, 2, 1, 2, 3, 4]
def baseStart_2799510 : Nat := 118140960795 + 2799510 * 2 ^ 59
def prefixEnd_2799510 : Nat := 4983230072969 + 3 ^ 40 * 2799510 * 2
def baseEnd_2799510 : Nat := 319443161570766030655621

theorem tailTrace_2799510 : CollatzResearch.WordTrace tailWord_2799510 prefixEnd_2799510 319443161570766030655621 := by
  unfold tailWord_2799510
  simp only [CollatzResearch.WordTrace]
  refine ⟨6381657380491303943010749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 68071012058573908725447989 6381657380491303943010749)
  ·
    refine ⟨2393121517684238978629031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6381657380491303943010749 2393121517684238978629031)
    ·
      refine ⟨3589682276526358467943547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2393121517684238978629031 3589682276526358467943547)
      ·
        refine ⟨5384523414789537701915321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3589682276526358467943547 5384523414789537701915321)
        ·
          refine ⟨4038392561092153276436491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5384523414789537701915321 4038392561092153276436491)
          ·
            refine ⟨6057588841638229914654737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4038392561092153276436491 6057588841638229914654737)
            ·
              refine ⟨4543191631228672435991053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6057588841638229914654737 4543191631228672435991053)
              ·
                refine ⟨1703696861710752163496645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4543191631228672435991053 1703696861710752163496645)
                ·
                  refine ⟨319443161570766030655621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1703696861710752163496645 319443161570766030655621)
                  ·
                    rfl

theorem cell22_2799510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 2, 3, 4].length) (baseStart_2799510 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2799510 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2799510 prefixEnd_2799510 := by exact prefixLift 2799510
  have htrace : WordTrace (prefixWord ++ tailWord_2799510) baseStart_2799510 baseEnd_2799510 := by
    simpa [prefixWord, tailWord_2799510, baseEnd_2799510] using wordTrace_append hprefix tailTrace_2799510
  have hstable : (prefixWord ++ tailWord_2799510).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2799510).length < 2 ^ (prefixWord ++ tailWord_2799510).sum := by decide
  have hdescent : baseEnd_2799510 < baseStart_2799510 := by decide
  rcases family_descends (prefixWord ++ tailWord_2799510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2799562 : List Nat := [3, 1, 2, 1, 2, 1, 2, 3, 3, 4]
def baseStart_2799562 : Nat := 118140960795 + 2799562 * 2 ^ 59
def prefixEnd_2799562 : Nat := 4983230072969 + 3 ^ 40 * 2799562 * 2
def baseEnd_2799562 : Nat := 958347285374987289666703

theorem tailTrace_2799562 : CollatzResearch.WordTrace tailWord_2799562 prefixEnd_2799562 958347285374987289666703 := by
  unfold tailWord_2799562
  simp only [CollatzResearch.WordTrace]
  refine ⟨25527103670918118992266235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68072276455781650646043293 25527103670918118992266235)
  ·
    refine ⟨38290655506377178488399353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25527103670918118992266235 38290655506377178488399353)
    ·
      refine ⟨28717991629782883866299515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38290655506377178488399353 28717991629782883866299515)
      ·
        refine ⟨43076987444674325799449273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28717991629782883866299515 43076987444674325799449273)
        ·
          refine ⟨32307740583505744349586955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43076987444674325799449273 32307740583505744349586955)
          ·
            refine ⟨48461610875258616524380433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32307740583505744349586955 48461610875258616524380433)
            ·
              refine ⟨36346208156443962393285325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48461610875258616524380433 36346208156443962393285325)
              ·
                refine ⟨13629828058666485897481997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36346208156443962393285325 13629828058666485897481997)
                ·
                  refine ⟨5111185521999932211555749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13629828058666485897481997 5111185521999932211555749)
                  ·
                    refine ⟨958347285374987289666703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5111185521999932211555749 958347285374987289666703)
                    ·
                      rfl

theorem cell22_2799562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 3, 3, 4].length) (baseStart_2799562 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2799562 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2799562 prefixEnd_2799562 := by exact prefixLift 2799562
  have htrace : WordTrace (prefixWord ++ tailWord_2799562) baseStart_2799562 baseEnd_2799562 := by
    simpa [prefixWord, tailWord_2799562, baseEnd_2799562] using wordTrace_append hprefix tailTrace_2799562
  have hstable : (prefixWord ++ tailWord_2799562).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2799562).length < 2 ^ (prefixWord ++ tailWord_2799562).sum := by decide
  have hdescent : baseEnd_2799562 < baseStart_2799562 := by decide
  rcases family_descends (prefixWord ++ tailWord_2799562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2799570 : List Nat := [3, 2, 2, 3, 2, 2, 1, 3, 1, 3]
def baseStart_2799570 : Nat := 118140960795 + 2799570 * 2 ^ 59
def prefixEnd_2799570 : Nat := 4983230072969 + 3 ^ 40 * 2799570 * 2
def baseEnd_2799570 : Nat := 958350023938477935466679

theorem tailTrace_2799570 : CollatzResearch.WordTrace tailWord_2799570 prefixEnd_2799570 958350023938477935466679 := by
  unfold tailWord_2799570
  simp only [CollatzResearch.WordTrace]
  refine ⟨25527176616910873333839041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68072470978428995556904109 25527176616910873333839041)
  ·
    refine ⟨19145382462683155000379281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25527176616910873333839041 19145382462683155000379281)
    ·
      refine ⟨14359036847012366250284461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19145382462683155000379281 14359036847012366250284461)
      ·
        refine ⟨5384638817629637343856673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14359036847012366250284461 5384638817629637343856673)
        ·
          refine ⟨4038479113222228007892505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5384638817629637343856673 4038479113222228007892505)
          ·
            refine ⟨3028859334916671005919379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4038479113222228007892505 3028859334916671005919379)
            ·
              refine ⟨4543289002375006508879069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3028859334916671005919379 4543289002375006508879069)
              ·
                refine ⟨1703733375890627440829651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4543289002375006508879069 1703733375890627440829651)
                ·
                  refine ⟨2555600063835941161244477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1703733375890627440829651 2555600063835941161244477)
                  ·
                    refine ⟨958350023938477935466679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2555600063835941161244477 958350023938477935466679)
                    ·
                      rfl

theorem cell22_2799570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 1, 3, 1, 3].length) (baseStart_2799570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2799570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2799570 prefixEnd_2799570 := by exact prefixLift 2799570
  have htrace : WordTrace (prefixWord ++ tailWord_2799570) baseStart_2799570 baseEnd_2799570 := by
    simpa [prefixWord, tailWord_2799570, baseEnd_2799570] using wordTrace_append hprefix tailTrace_2799570
  have hstable : (prefixWord ++ tailWord_2799570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2799570).length < 2 ^ (prefixWord ++ tailWord_2799570).sum := by decide
  have hdescent : baseEnd_2799570 < baseStart_2799570 := by decide
  rcases family_descends (prefixWord ++ tailWord_2799570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2799624 : List Nat := [2, 1, 3, 2, 1, 2, 4, 1, 2, 4]
def baseStart_2799624 : Nat := 118140960795 + 2799624 * 2 ^ 59
def prefixEnd_2799624 : Nat := 4983230072969 + 3 ^ 40 * 2799624 * 2
def baseEnd_2799624 : Nat := 958368509242039794616513

theorem tailTrace_2799624 : CollatzResearch.WordTrace tailWord_2799624 prefixEnd_2799624 958368509242039794616513 := by
  unfold tailWord_2799624
  simp only [CollatzResearch.WordTrace]
  refine ⟨51055338004723930278910963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68073784006298573705214617 51055338004723930278910963)
  ·
    refine ⟨76583007007085895418366445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51055338004723930278910963 76583007007085895418366445)
    ·
      refine ⟨28718627627657210781887417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76583007007085895418366445 28718627627657210781887417)
      ·
        refine ⟨21538970720742908086415563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28718627627657210781887417 21538970720742908086415563)
        ·
          refine ⟨32308456081114362129623345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21538970720742908086415563 32308456081114362129623345)
          ·
            refine ⟨24231342060835771597217509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32308456081114362129623345 24231342060835771597217509)
            ·
              refine ⟨4543376636406707174478283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24231342060835771597217509 4543376636406707174478283)
              ·
                refine ⟨6815064954610060761717425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4543376636406707174478283 6815064954610060761717425)
                ·
                  refine ⟨5111298715957545571288069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6815064954610060761717425 5111298715957545571288069)
                  ·
                    refine ⟨958368509242039794616513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5111298715957545571288069 958368509242039794616513)
                    ·
                      rfl

theorem cell22_2799624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 4, 1, 2, 4].length) (baseStart_2799624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2799624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2799624 prefixEnd_2799624 := by exact prefixLift 2799624
  have htrace : WordTrace (prefixWord ++ tailWord_2799624) baseStart_2799624 baseEnd_2799624 := by
    simpa [prefixWord, tailWord_2799624, baseEnd_2799624] using wordTrace_append hprefix tailTrace_2799624
  have hstable : (prefixWord ++ tailWord_2799624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2799624).length < 2 ^ (prefixWord ++ tailWord_2799624).sum := by decide
  have hdescent : baseEnd_2799624 < baseStart_2799624 := by decide
  rcases family_descends (prefixWord ++ tailWord_2799624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2799639 : List Nat := [1, 1, 3, 5, 3, 9]
def baseStart_2799639 : Nat := 118140960795 + 2799639 * 2 ^ 59
def prefixEnd_2799639 : Nat := 4983230072969 + 3 ^ 40 * 2799639 * 2
def baseEnd_2799639 : Nat := 11831773383315861178907

theorem tailTrace_2799639 : CollatzResearch.WordTrace tailWord_2799639 prefixEnd_2799639 11831773383315861178907 := by
  unfold tailWord_2799639
  simp only [CollatzResearch.WordTrace]
  refine ⟨102111223104393518119617971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68074148736262345413078647 102111223104393518119617971)
  ·
    refine ⟨153166834656590277179426957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102111223104393518119617971 153166834656590277179426957)
    ·
      refine ⟨57437562996221353942285109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 153166834656590277179426957 57437562996221353942285109)
      ·
        refine ⟨5384771530895751932089229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 57437562996221353942285109 5384771530895751932089229)
        ·
          refine ⟨2019289324085906974533461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5384771530895751932089229 2019289324085906974533461)
          ·
            refine ⟨11831773383315861178907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2019289324085906974533461 11831773383315861178907)
            ·
              rfl

theorem cell22_2799639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 9].length) (baseStart_2799639 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2799639 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2799639 prefixEnd_2799639 := by exact prefixLift 2799639
  have htrace : WordTrace (prefixWord ++ tailWord_2799639) baseStart_2799639 baseEnd_2799639 := by
    simpa [prefixWord, tailWord_2799639, baseEnd_2799639] using wordTrace_append hprefix tailTrace_2799639
  have hstable : (prefixWord ++ tailWord_2799639).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2799639).length < 2 ^ (prefixWord ++ tailWord_2799639).sum := by decide
  have hdescent : baseEnd_2799639 < baseStart_2799639 := by decide
  rcases family_descends (prefixWord ++ tailWord_2799639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2799701 : List Nat := [1, 3, 2, 2, 1, 5, 1, 2, 5]
def baseStart_2799701 : Nat := 118140960795 + 2799701 * 2 ^ 59
def prefixEnd_2799701 : Nat := 4983230072969 + 3 ^ 40 * 2799701 * 2
def baseEnd_2799701 : Nat := 319464955971879086813759

theorem tailTrace_2799701 : CollatzResearch.WordTrace tailWord_2799701 prefixEnd_2799701 319464955971879086813759 := by
  unfold tailWord_2799701
  simp only [CollatzResearch.WordTrace]
  refine ⟨102113484430168902708374957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68075656286779268472249971 102113484430168902708374957)
  ·
    refine ⟨38292556661313338515640609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102113484430168902708374957 38292556661313338515640609)
    ·
      refine ⟨28719417495985003886730457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38292556661313338515640609 28719417495985003886730457)
      ·
        refine ⟨21539563121988752915047843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28719417495985003886730457 21539563121988752915047843)
        ·
          refine ⟨32309344682983129372571765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21539563121988752915047843 32309344682983129372571765)
          ·
            refine ⟨3029001064029668378678603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 32309344682983129372571765 3029001064029668378678603)
            ·
              refine ⟨4543501596044502568017905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3029001064029668378678603 4543501596044502568017905)
              ·
                refine ⟨3407626197033376926013429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4543501596044502568017905 3407626197033376926013429)
                ·
                  refine ⟨319464955971879086813759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3407626197033376926013429 319464955971879086813759)
                  ·
                    rfl

theorem cell22_2799701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 1, 2, 5].length) (baseStart_2799701 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2799701 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2799701 prefixEnd_2799701 := by exact prefixLift 2799701
  have htrace : WordTrace (prefixWord ++ tailWord_2799701) baseStart_2799701 baseEnd_2799701 := by
    simpa [prefixWord, tailWord_2799701, baseEnd_2799701] using wordTrace_append hprefix tailTrace_2799701
  have hstable : (prefixWord ++ tailWord_2799701).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2799701).length < 2 ^ (prefixWord ++ tailWord_2799701).sum := by decide
  have hdescent : baseEnd_2799701 < baseStart_2799701 := by decide
  rcases family_descends (prefixWord ++ tailWord_2799701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2799793 : List Nat := [1, 2, 2, 5, 2, 1, 2, 1, 2, 4]
def baseStart_2799793 : Nat := 118140960795 + 2799793 * 2 ^ 59
def prefixEnd_2799793 : Nat := 4983230072969 + 3 ^ 40 * 2799793 * 2
def baseEnd_2799793 : Nat := 958426361395779687140995

theorem tailTrace_2799793 : CollatzResearch.WordTrace tailWord_2799793 prefixEnd_2799793 958426361395779687140995 := by
  unfold tailWord_2799793
  simp only [CollatzResearch.WordTrace]
  refine ⟨102116839945835602420724033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68077893297223734947149355 102116839945835602420724033)
  ·
    refine ⟨76587629959376701815543025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102116839945835602420724033 76587629959376701815543025)
    ·
      refine ⟨57440722469532526361657269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76587629959376701815543025 57440722469532526361657269)
      ·
        refine ⟨5385067731518674346405369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 57440722469532526361657269 5385067731518674346405369)
        ·
          refine ⟨4038800798639005759804027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5385067731518674346405369 4038800798639005759804027)
          ·
            refine ⟨6058201197958508639706041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4038800798639005759804027 6058201197958508639706041)
            ·
              refine ⟨4543650898468881479779531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6058201197958508639706041 4543650898468881479779531)
              ·
                refine ⟨6815476347703322219669297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4543650898468881479779531 6815476347703322219669297)
                ·
                  refine ⟨5111607260777491664751973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6815476347703322219669297 5111607260777491664751973)
                  ·
                    refine ⟨958426361395779687140995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5111607260777491664751973 958426361395779687140995)
                    ·
                      rfl

theorem cell22_2799793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 2, 1, 2, 4].length) (baseStart_2799793 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2799793 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2799793 prefixEnd_2799793 := by exact prefixLift 2799793
  have htrace : WordTrace (prefixWord ++ tailWord_2799793) baseStart_2799793 baseEnd_2799793 := by
    simpa [prefixWord, tailWord_2799793, baseEnd_2799793] using wordTrace_append hprefix tailTrace_2799793
  have hstable : (prefixWord ++ tailWord_2799793).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2799793).length < 2 ^ (prefixWord ++ tailWord_2799793).sum := by decide
  have hdescent : baseEnd_2799793 < baseStart_2799793 := by decide
  rcases family_descends (prefixWord ++ tailWord_2799793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2799810 : List Nat := [3, 5, 1, 1, 1, 1, 2, 2, 2, 4]
def baseStart_2799810 : Nat := 118140960795 + 2799810 * 2 ^ 59
def prefixEnd_2799810 : Nat := 4983230072969 + 3 ^ 40 * 2799810 * 2
def baseEnd_2799810 : Nat := 958432180843197309465943

theorem tailTrace_2799810 : CollatzResearch.WordTrace tailWord_2799810 prefixEnd_2799810 958432180843197309465943 := by
  unfold tailWord_2799810
  simp only [CollatzResearch.WordTrace]
  refine ⟨25529364996693503581023221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68078306657849342882728589 25529364996693503581023221)
  ·
    refine ⟨2393377968440015960720927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 25529364996693503581023221 2393377968440015960720927)
    ·
      refine ⟨3590066952660023941081391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2393377968440015960720927 3590066952660023941081391)
      ·
        refine ⟨5385100428990035911622087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3590066952660023941081391 5385100428990035911622087)
        ·
          refine ⟨8077650643485053867433131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5385100428990035911622087 8077650643485053867433131)
          ·
            refine ⟨12116475965227580801149697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8077650643485053867433131 12116475965227580801149697)
            ·
              refine ⟨9087356973920685600862273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12116475965227580801149697 9087356973920685600862273)
              ·
                refine ⟨6815517730440514200646705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9087356973920685600862273 6815517730440514200646705)
                ·
                  refine ⟨5111638297830385650485029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6815517730440514200646705 5111638297830385650485029)
                  ·
                    refine ⟨958432180843197309465943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5111638297830385650485029 958432180843197309465943)
                    ·
                      rfl

theorem cell22_2799810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_2799810 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2799810 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2799810 prefixEnd_2799810 := by exact prefixLift 2799810
  have htrace : WordTrace (prefixWord ++ tailWord_2799810) baseStart_2799810 baseEnd_2799810 := by
    simpa [prefixWord, tailWord_2799810, baseEnd_2799810] using wordTrace_append hprefix tailTrace_2799810
  have hstable : (prefixWord ++ tailWord_2799810).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2799810).length < 2 ^ (prefixWord ++ tailWord_2799810).sum := by decide
  have hdescent : baseEnd_2799810 < baseStart_2799810 := by decide
  rcases family_descends (prefixWord ++ tailWord_2799810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2799823 : List Nat := [1, 1, 2, 1, 1, 3, 5, 4, 1, 3]
def baseStart_2799823 : Nat := 118140960795 + 2799823 * 2 ^ 59
def prefixEnd_2799823 : Nat := 4983230072969 + 3 ^ 40 * 2799823 * 2
def baseEnd_2799823 : Nat := 958436631008869608890903

theorem tailTrace_2799823 : CollatzResearch.WordTrace tailWord_2799823 prefixEnd_2799823 958436631008869608890903 := by
  unfold tailWord_2799823
  simp only [CollatzResearch.WordTrace]
  refine ⟨102117934135726917544316123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68078622757151278362877415 102117934135726917544316123)
  ·
    refine ⟨153176901203590376316474185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102117934135726917544316123 153176901203590376316474185)
    ·
      refine ⟨114882675902692782237355639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153176901203590376316474185 114882675902692782237355639)
      ·
        refine ⟨172324013854039173356033459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114882675902692782237355639 172324013854039173356033459)
        ·
          refine ⟨258486020781058760034050189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172324013854039173356033459 258486020781058760034050189)
          ·
            refine ⟨96932257792897035012768821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 258486020781058760034050189 96932257792897035012768821)
            ·
              refine ⟨9087399168084097032447077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 96932257792897035012768821 9087399168084097032447077)
              ·
                refine ⟨1703887344015768193583827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9087399168084097032447077 1703887344015768193583827)
                ·
                  refine ⟨2555831016023652290375741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1703887344015768193583827 2555831016023652290375741)
                  ·
                    refine ⟨958436631008869608890903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2555831016023652290375741 958436631008869608890903)
                    ·
                      rfl

theorem cell22_2799823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 4, 1, 3].length) (baseStart_2799823 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2799823 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2799823 prefixEnd_2799823 := by exact prefixLift 2799823
  have htrace : WordTrace (prefixWord ++ tailWord_2799823) baseStart_2799823 baseEnd_2799823 := by
    simpa [prefixWord, tailWord_2799823, baseEnd_2799823] using wordTrace_append hprefix tailTrace_2799823
  have hstable : (prefixWord ++ tailWord_2799823).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2799823).length < 2 ^ (prefixWord ++ tailWord_2799823).sum := by decide
  have hdescent : baseEnd_2799823 < baseStart_2799823 := by decide
  rcases family_descends (prefixWord ++ tailWord_2799823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2799834 : List Nat := [3, 1, 1, 2, 2, 1, 3, 1, 1, 7]
def baseStart_2799834 : Nat := 118140960795 + 2799834 * 2 ^ 59
def prefixEnd_2799834 : Nat := 4983230072969 + 3 ^ 40 * 2799834 * 2
def baseEnd_2799834 : Nat := 958440396533669246865869

theorem tailTrace_2799834 : CollatzResearch.WordTrace tailWord_2799834 prefixEnd_2799834 958440396533669246865869 := by
  unfold tailWord_2799834
  simp only [CollatzResearch.WordTrace]
  refine ⟨25529583834671766605741639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68078890225791377615311037 25529583834671766605741639)
  ·
    refine ⟨38294375752007649908612459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25529583834671766605741639 38294375752007649908612459)
    ·
      refine ⟨57441563628011474862918689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38294375752007649908612459 57441563628011474862918689)
      ·
        refine ⟨43081172721008606147189017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57441563628011474862918689 43081172721008606147189017)
        ·
          refine ⟨32310879540756454610391763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43081172721008606147189017 32310879540756454610391763)
          ·
            refine ⟨48466319311134681915587645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32310879540756454610391763 48466319311134681915587645)
            ·
              refine ⟨18174869741675505718345367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48466319311134681915587645 18174869741675505718345367)
              ·
                refine ⟨27262304612513258577518051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18174869741675505718345367 27262304612513258577518051)
                ·
                  refine ⟨40893456918769887866277077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27262304612513258577518051 40893456918769887866277077)
                  ·
                    refine ⟨958440396533669246865869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40893456918769887866277077 958440396533669246865869)
                    ·
                      rfl

theorem cell22_2799834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 1, 1, 7].length) (baseStart_2799834 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2799834 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2799834 prefixEnd_2799834 := by exact prefixLift 2799834
  have htrace : WordTrace (prefixWord ++ tailWord_2799834) baseStart_2799834 baseEnd_2799834 := by
    simpa [prefixWord, tailWord_2799834, baseEnd_2799834] using wordTrace_append hprefix tailTrace_2799834
  have hstable : (prefixWord ++ tailWord_2799834).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2799834).length < 2 ^ (prefixWord ++ tailWord_2799834).sum := by decide
  have hdescent : baseEnd_2799834 < baseStart_2799834 := by decide
  rcases family_descends (prefixWord ++ tailWord_2799834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2799842 : List Nat := [3, 3, 4, 1, 1, 1, 3, 6]
def baseStart_2799842 : Nat := 118140960795 + 2799842 * 2 ^ 59
def prefixEnd_2799842 : Nat := 4983230072969 + 3 ^ 40 * 2799842 * 2
def baseEnd_2799842 : Nat := 106493681677462210296205

theorem tailTrace_2799842 : CollatzResearch.WordTrace tailWord_2799842 prefixEnd_2799842 106493681677462210296205 := by
  unfold tailWord_2799842
  simp only [CollatzResearch.WordTrace]
  refine ⟨25529656780664520947314445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68079084748438722526171853 25529656780664520947314445)
  ·
    refine ⟨9573621292749195355242917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25529656780664520947314445 9573621292749195355242917)
    ·
      refine ⟨1795053992390474129108047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9573621292749195355242917 1795053992390474129108047)
      ·
        refine ⟨2692580988585711193662071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1795053992390474129108047 2692580988585711193662071)
        ·
          refine ⟨4038871482878566790493107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2692580988585711193662071 4038871482878566790493107)
          ·
            refine ⟨6058307224317850185739661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4038871482878566790493107 6058307224317850185739661)
            ·
              refine ⟨2271865209119193819652373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6058307224317850185739661 2271865209119193819652373)
              ·
                refine ⟨106493681677462210296205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2271865209119193819652373 106493681677462210296205)
                ·
                  rfl

theorem cell22_2799842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 3, 6].length) (baseStart_2799842 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2799842 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2799842 prefixEnd_2799842 := by exact prefixLift 2799842
  have htrace : WordTrace (prefixWord ++ tailWord_2799842) baseStart_2799842 baseEnd_2799842 := by
    simpa [prefixWord, tailWord_2799842, baseEnd_2799842] using wordTrace_append hprefix tailTrace_2799842
  have hstable : (prefixWord ++ tailWord_2799842).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2799842).length < 2 ^ (prefixWord ++ tailWord_2799842).sum := by decide
  have hdescent : baseEnd_2799842 < baseStart_2799842 := by decide
  rcases family_descends (prefixWord ++ tailWord_2799842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2799881 : List Nat := [1, 2, 1, 1, 3, 5, 2, 1, 6]
def baseStart_2799881 : Nat := 118140960795 + 2799881 * 2 ^ 59
def prefixEnd_2799881 : Nat := 4983230072969 + 3 ^ 40 * 2799881 * 2
def baseEnd_2799881 : Nat := 319485495198058930313575

theorem tailTrace_2799881 : CollatzResearch.WordTrace tailWord_2799881 prefixEnd_2799881 319485495198058930313575 := by
  unfold tailWord_2799881
  simp only [CollatzResearch.WordTrace]
  refine ⟨102120049569516793449927497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68080033046344528966618331 102120049569516793449927497)
  ·
    refine ⟨76590037177137595087445623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102120049569516793449927497 76590037177137595087445623)
    ·
      refine ⟨114885055765706392631168435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76590037177137595087445623 114885055765706392631168435)
      ·
        refine ⟨172327583648559588946752653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114885055765706392631168435 172327583648559588946752653)
        ·
          refine ⟨64622843868209845855032245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 172327583648559588946752653 64622843868209845855032245)
          ·
            refine ⟨6058391612644673048909273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 64622843868209845855032245 6058391612644673048909273)
            ·
              refine ⟨4543793709483504786681955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6058391612644673048909273 4543793709483504786681955)
              ·
                refine ⟨6815690564225257180022933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4543793709483504786681955 6815690564225257180022933)
                ·
                  refine ⟨319485495198058930313575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6815690564225257180022933 319485495198058930313575)
                  ·
                    rfl

theorem cell22_2799881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 2, 1, 6].length) (baseStart_2799881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2799881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2799881 prefixEnd_2799881 := by exact prefixLift 2799881
  have htrace : WordTrace (prefixWord ++ tailWord_2799881) baseStart_2799881 baseEnd_2799881 := by
    simpa [prefixWord, tailWord_2799881, baseEnd_2799881] using wordTrace_append hprefix tailTrace_2799881
  have hstable : (prefixWord ++ tailWord_2799881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2799881).length < 2 ^ (prefixWord ++ tailWord_2799881).sum := by decide
  have hdescent : baseEnd_2799881 < baseStart_2799881 := by decide
  rcases family_descends (prefixWord ++ tailWord_2799881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2800003 : List Nat := [1, 1, 1, 3, 6, 1, 1, 1, 2, 5]
def baseStart_2800003 : Nat := 118140960795 + 2800003 * 2 ^ 59
def prefixEnd_2800003 : Nat := 4983230072969 + 3 ^ 40 * 2800003 * 2
def baseEnd_2800003 : Nat := 958498248687409139390351

theorem tailTrace_2800003 : CollatzResearch.WordTrace tailWord_2800003 prefixEnd_2800003 958498248687409139390351 := by
  unfold tailWord_2800003
  simp only [CollatzResearch.WordTrace]
  refine ⟨102124499275074808285868663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68082999516716538857245775 102124499275074808285868663)
  ·
    refine ⟨153186748912612212428802995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102124499275074808285868663 153186748912612212428802995)
    ·
      refine ⟨229780123368918318643204493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153186748912612212428802995 229780123368918318643204493)
      ·
        refine ⟨86167546263344369491201685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 229780123368918318643204493 86167546263344369491201685)
        ·
          refine ⟨4039103731094267319900079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 86167546263344369491201685 4039103731094267319900079)
          ·
            refine ⟨6058655596641400979850119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4039103731094267319900079 6058655596641400979850119)
            ·
              refine ⟨9087983394962101469775179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6058655596641400979850119 9087983394962101469775179)
              ·
                refine ⟨13631975092443152204662769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9087983394962101469775179 13631975092443152204662769)
                ·
                  refine ⟨10223981319332364153497077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13631975092443152204662769 10223981319332364153497077)
                  ·
                    refine ⟨958498248687409139390351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10223981319332364153497077 958498248687409139390351)
                    ·
                      rfl

theorem cell22_2800003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 1, 2, 5].length) (baseStart_2800003 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2800003 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2800003 prefixEnd_2800003 := by exact prefixLift 2800003
  have htrace : WordTrace (prefixWord ++ tailWord_2800003) baseStart_2800003 baseEnd_2800003 := by
    simpa [prefixWord, tailWord_2800003, baseEnd_2800003] using wordTrace_append hprefix tailTrace_2800003
  have hstable : (prefixWord ++ tailWord_2800003).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2800003).length < 2 ^ (prefixWord ++ tailWord_2800003).sum := by decide
  have hdescent : baseEnd_2800003 < baseStart_2800003 := by decide
  rcases family_descends (prefixWord ++ tailWord_2800003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2800035 : List Nat := [1, 1, 1, 4, 1, 4, 4, 1, 1, 4]
def baseStart_2800035 : Nat := 118140960795 + 2800035 * 2 ^ 59
def prefixEnd_2800035 : Nat := 4983230072969 + 3 ^ 40 * 2800035 * 2
def baseEnd_2800035 : Nat := 958509202941371722590253

theorem tailTrace_2800035 : CollatzResearch.WordTrace tailWord_2800035 prefixEnd_2800035 958509202941371722590253 := by
  unfold tailWord_2800035
  simp only [CollatzResearch.WordTrace]
  refine ⟨102125666410958877751033559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68083777607305918500689039 102125666410958877751033559)
  ·
    refine ⟨153188499616438316626550339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102125666410958877751033559 153188499616438316626550339)
    ·
      refine ⟨229782749424657474939825509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153188499616438316626550339 229782749424657474939825509)
      ·
        refine ⟨43084265517123276551217283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 229782749424657474939825509 43084265517123276551217283)
        ·
          refine ⟨64626398275684914826825925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43084265517123276551217283 64626398275684914826825925)
          ·
            refine ⟨12117449676690921530029861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64626398275684914826825925 12117449676690921530029861)
            ·
              refine ⟨2272021814379547786880599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12117449676690921530029861 2272021814379547786880599)
              ·
                refine ⟨3408032721569321680320899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2272021814379547786880599 3408032721569321680320899)
                ·
                  refine ⟨5112049082353982520481349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3408032721569321680320899 5112049082353982520481349)
                  ·
                    refine ⟨958509202941371722590253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5112049082353982520481349 958509202941371722590253)
                    ·
                      rfl

theorem cell22_2800035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 4, 1, 1, 4].length) (baseStart_2800035 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2800035 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2800035 prefixEnd_2800035 := by exact prefixLift 2800035
  have htrace : WordTrace (prefixWord ++ tailWord_2800035) baseStart_2800035 baseEnd_2800035 := by
    simpa [prefixWord, tailWord_2800035, baseEnd_2800035] using wordTrace_append hprefix tailTrace_2800035
  have hstable : (prefixWord ++ tailWord_2800035).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2800035).length < 2 ^ (prefixWord ++ tailWord_2800035).sum := by decide
  have hdescent : baseEnd_2800035 < baseStart_2800035 := by decide
  rcases family_descends (prefixWord ++ tailWord_2800035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2800170 : List Nat := [3, 1, 4, 1, 1, 2, 1, 2, 3, 4]
def baseStart_2800170 : Nat := 118140960795 + 2800170 * 2 ^ 59
def prefixEnd_2800170 : Nat := 4983230072969 + 3 ^ 40 * 2800170 * 2
def baseEnd_2800170 : Nat := 958555416200276370464839

theorem tailTrace_2800170 : CollatzResearch.WordTrace tailWord_2800170 prefixEnd_2800170 958555416200276370464839 := by
  unfold tailWord_2800170
  simp only [CollatzResearch.WordTrace]
  refine ⟨25532647566367448951799491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68087060176979863871465309 25532647566367448951799491)
  ·
    refine ⟨38298971349551173427699237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25532647566367448951799491 38298971349551173427699237)
    ·
      refine ⟨7181057128040845017693607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38298971349551173427699237 7181057128040845017693607)
      ·
        refine ⟨10771585692061267526540411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7181057128040845017693607 10771585692061267526540411)
        ·
          refine ⟨16157378538091901289810617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10771585692061267526540411 16157378538091901289810617)
          ·
            refine ⟨12118033903568925967357963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16157378538091901289810617 12118033903568925967357963)
            ·
              refine ⟨18177050855353388951036945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12118033903568925967357963 18177050855353388951036945)
              ·
                refine ⟨13632788141515041713277709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18177050855353388951036945 13632788141515041713277709)
                ·
                  refine ⟨5112295553068140642479141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13632788141515041713277709 5112295553068140642479141)
                  ·
                    refine ⟨958555416200276370464839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5112295553068140642479141 958555416200276370464839)
                    ·
                      rfl

theorem cell22_2800170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 2, 3, 4].length) (baseStart_2800170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2800170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2800170 prefixEnd_2800170 := by exact prefixLift 2800170
  have htrace : WordTrace (prefixWord ++ tailWord_2800170) baseStart_2800170 baseEnd_2800170 := by
    simpa [prefixWord, tailWord_2800170, baseEnd_2800170] using wordTrace_append hprefix tailTrace_2800170
  have hstable : (prefixWord ++ tailWord_2800170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2800170).length < 2 ^ (prefixWord ++ tailWord_2800170).sum := by decide
  have hdescent : baseEnd_2800170 < baseStart_2800170 := by decide
  rcases family_descends (prefixWord ++ tailWord_2800170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2800202 : List Nat := [3, 1, 2, 1, 1, 5, 2, 3, 4]
def baseStart_2800202 : Nat := 118140960795 + 2800202 * 2 ^ 59
def prefixEnd_2800202 : Nat := 4983230072969 + 3 ^ 40 * 2800202 * 2
def baseEnd_2800202 : Nat := 319522123484746317888247

theorem tailTrace_2800202 : CollatzResearch.WordTrace tailWord_2800202 prefixEnd_2800202 319522123484746317888247 := by
  unfold tailWord_2800202
  simp only [CollatzResearch.WordTrace]
  refine ⟨25532939350338466318090715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68087838267569243514908573 25532939350338466318090715)
  ·
    refine ⟨38299409025507699477136073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25532939350338466318090715 38299409025507699477136073)
    ·
      refine ⟨28724556769130774607852055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38299409025507699477136073 28724556769130774607852055)
      ·
        refine ⟨43086835153696161911778083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28724556769130774607852055 43086835153696161911778083)
        ·
          refine ⟨64630252730544242867667125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43086835153696161911778083 64630252730544242867667125)
          ·
            refine ⟨6059086193488522768843793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 64630252730544242867667125 6059086193488522768843793)
            ·
              refine ⟨4544314645116392076632845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6059086193488522768843793 4544314645116392076632845)
              ·
                refine ⟨1704117991918647028737317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4544314645116392076632845 1704117991918647028737317)
                ·
                  refine ⟨319522123484746317888247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1704117991918647028737317 319522123484746317888247)
                  ·
                    rfl

theorem cell22_2800202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 2, 3, 4].length) (baseStart_2800202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2800202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2800202 prefixEnd_2800202 := by exact prefixLift 2800202
  have htrace : WordTrace (prefixWord ++ tailWord_2800202) baseStart_2800202 baseEnd_2800202 := by
    simpa [prefixWord, tailWord_2800202, baseEnd_2800202] using wordTrace_append hprefix tailTrace_2800202
  have hstable : (prefixWord ++ tailWord_2800202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2800202).length < 2 ^ (prefixWord ++ tailWord_2800202).sum := by decide
  have hdescent : baseEnd_2800202 < baseStart_2800202 := by decide
  rcases family_descends (prefixWord ++ tailWord_2800202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2800234 : List Nat := [3, 1, 3, 2, 1, 1, 5, 1, 2, 3]
def baseStart_2800234 : Nat := 118140960795 + 2800234 * 2 ^ 59
def prefixEnd_2800234 : Nat := 4983230072969 + 3 ^ 40 * 2800234 * 2
def baseEnd_2800234 : Nat := 958577324708201536864643

theorem tailTrace_2800234 : CollatzResearch.WordTrace tailWord_2800234 prefixEnd_2800234 958577324708201536864643 := by
  unfold tailWord_2800234
  simp only [CollatzResearch.WordTrace]
  refine ⟨25533231134309483684381939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68088616358158623158351837 25533231134309483684381939)
  ·
    refine ⟨38299846701464225526572909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25533231134309483684381939 38299846701464225526572909)
    ·
      refine ⟨14362442513049084572464841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38299846701464225526572909 14362442513049084572464841)
      ·
        refine ⟨10771831884786813429348631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14362442513049084572464841 10771831884786813429348631)
        ·
          refine ⟨16157747827180220144022947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10771831884786813429348631 16157747827180220144022947)
          ·
            refine ⟨24236621740770330216034421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16157747827180220144022947 24236621740770330216034421)
            ·
              refine ⟨2272183288197218457753227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24236621740770330216034421 2272183288197218457753227)
              ·
                refine ⟨3408274932295827686629841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2272183288197218457753227 3408274932295827686629841)
                ·
                  refine ⟨2556206199221870764972381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3408274932295827686629841 2556206199221870764972381)
                  ·
                    refine ⟨958577324708201536864643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2556206199221870764972381 958577324708201536864643)
                    ·
                      rfl

theorem cell22_2800234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 5, 1, 2, 3].length) (baseStart_2800234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2800234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2800234 prefixEnd_2800234 := by exact prefixLift 2800234
  have htrace : WordTrace (prefixWord ++ tailWord_2800234) baseStart_2800234 baseEnd_2800234 := by
    simpa [prefixWord, tailWord_2800234, baseEnd_2800234] using wordTrace_append hprefix tailTrace_2800234
  have hstable : (prefixWord ++ tailWord_2800234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2800234).length < 2 ^ (prefixWord ++ tailWord_2800234).sum := by decide
  have hdescent : baseEnd_2800234 < baseStart_2800234 := by decide
  rcases family_descends (prefixWord ++ tailWord_2800234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2800337 : List Nat := [1, 2, 2, 1, 2, 3, 3, 4, 4]
def baseStart_2800337 : Nat := 118140960795 + 2800337 * 2 ^ 59
def prefixEnd_2800337 : Nat := 4983230072969 + 3 ^ 40 * 2800337 * 2
def baseEnd_2800337 : Nat := 319537527904381200513109

theorem tailTrace_2800337 : CollatzResearch.WordTrace tailWord_2800337 prefixEnd_2800337 319537527904381200513109 := by
  unfold tailWord_2800337
  simp only [CollatzResearch.WordTrace]
  refine ⟨102136681255864783328527265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68091120837243188885684843 102136681255864783328527265)
  ·
    refine ⟨76602510941898587496395449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102136681255864783328527265 76602510941898587496395449)
    ·
      refine ⟨57451883206423940622296587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76602510941898587496395449 57451883206423940622296587)
      ·
        refine ⟨86177824809635910933444881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57451883206423940622296587 86177824809635910933444881)
        ·
          refine ⟨64633368607226933200083661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86177824809635910933444881 64633368607226933200083661)
          ·
            refine ⟨24237513227710099950031373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64633368607226933200083661 24237513227710099950031373)
            ·
              refine ⟨9089067460391287481261765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24237513227710099950031373 9089067460391287481261765)
              ·
                refine ⟨1704200148823366402736581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9089067460391287481261765 1704200148823366402736581)
                ·
                  refine ⟨319537527904381200513109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1704200148823366402736581 319537527904381200513109)
                  ·
                    rfl

theorem cell22_2800337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 4, 4].length) (baseStart_2800337 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2800337 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2800337 prefixEnd_2800337 := by exact prefixLift 2800337
  have htrace : WordTrace (prefixWord ++ tailWord_2800337) baseStart_2800337 baseEnd_2800337 := by
    simpa [prefixWord, tailWord_2800337, baseEnd_2800337] using wordTrace_append hprefix tailTrace_2800337
  have hstable : (prefixWord ++ tailWord_2800337).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2800337).length < 2 ^ (prefixWord ++ tailWord_2800337).sum := by decide
  have hdescent : baseEnd_2800337 < baseStart_2800337 := by decide
  rcases family_descends (prefixWord ++ tailWord_2800337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2800367 : List Nat := [1, 1, 2, 1, 5, 2, 3, 1, 2, 4]
def baseStart_2800367 : Nat := 118140960795 + 2800367 * 2 ^ 59
def prefixEnd_2800367 : Nat := 4983230072969 + 3 ^ 40 * 2800367 * 2
def baseEnd_2800367 : Nat := 958622853326233523289235

theorem tailTrace_2800367 : CollatzResearch.WordTrace tailWord_2800367 prefixEnd_2800367 958622853326233523289235 := by
  unfold tailWord_2800367
  simp only [CollatzResearch.WordTrace]
  refine ⟨102137775445756098452119355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68091850297170732301412903 102137775445756098452119355)
  ·
    refine ⟨153206663168634147678179033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102137775445756098452119355 153206663168634147678179033)
    ·
      refine ⟨114904997376475610758634275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153206663168634147678179033 114904997376475610758634275)
      ·
        refine ⟨172357496064713416137951413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114904997376475610758634275 172357496064713416137951413)
        ·
          refine ⟨16158515256066882762932945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 172357496064713416137951413 16158515256066882762932945)
          ·
            refine ⟨12118886442050162072199709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16158515256066882762932945 12118886442050162072199709)
            ·
              refine ⟨4544582415768810777074891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12118886442050162072199709 4544582415768810777074891)
              ·
                refine ⟨6816873623653216165612337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4544582415768810777074891 6816873623653216165612337)
                ·
                  refine ⟨5112655217739912124209253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6816873623653216165612337 5112655217739912124209253)
                  ·
                    refine ⟨958622853326233523289235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5112655217739912124209253 958622853326233523289235)
                    ·
                      rfl

theorem cell22_2800367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 3, 1, 2, 4].length) (baseStart_2800367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2800367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2800367 prefixEnd_2800367 := by exact prefixLift 2800367
  have htrace : WordTrace (prefixWord ++ tailWord_2800367) baseStart_2800367 baseEnd_2800367 := by
    simpa [prefixWord, tailWord_2800367, baseEnd_2800367] using wordTrace_append hprefix tailTrace_2800367
  have hstable : (prefixWord ++ tailWord_2800367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2800367).length < 2 ^ (prefixWord ++ tailWord_2800367).sum := by decide
  have hdescent : baseEnd_2800367 < baseStart_2800367 := by decide
  rcases family_descends (prefixWord ++ tailWord_2800367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2800373 : List Nat := [1, 3, 6, 1, 1, 1, 1, 3, 1, 4]
def baseStart_2800373 : Nat := 118140960795 + 2800373 * 2 ^ 59
def prefixEnd_2800373 : Nat := 4983230072969 + 3 ^ 40 * 2800373 * 2
def baseEnd_2800373 : Nat := 958624907248851507639217

theorem tailTrace_2800373 : CollatzResearch.WordTrace tailWord_2800373 prefixEnd_2800373 958624907248851507639217 := by
  unfold tailWord_2800373
  simp only [CollatzResearch.WordTrace]
  refine ⟨102137994283734361476837773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68091996189156240984558515 102137994283734361476837773)
  ·
    refine ⟨38301747856400385553814165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102137994283734361476837773 38301747856400385553814165)
    ·
      refine ⟨1795394430768768072835039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 38301747856400385553814165 1795394430768768072835039)
      ·
        refine ⟨2693091646153152109252559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1795394430768768072835039 2693091646153152109252559)
        ·
          refine ⟨4039637469229728163878839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2693091646153152109252559 4039637469229728163878839)
          ·
            refine ⟨6059456203844592245818259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4039637469229728163878839 6059456203844592245818259)
            ·
              refine ⟨9089184305766888368727389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6059456203844592245818259 9089184305766888368727389)
              ·
                refine ⟨3408444114662583138272771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9089184305766888368727389 3408444114662583138272771)
                ·
                  refine ⟨5112666171993874707409157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3408444114662583138272771 5112666171993874707409157)
                  ·
                    refine ⟨958624907248851507639217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5112666171993874707409157 958624907248851507639217)
                    ·
                      rfl

theorem cell22_2800373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_2800373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2800373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2800373 prefixEnd_2800373 := by exact prefixLift 2800373
  have htrace : WordTrace (prefixWord ++ tailWord_2800373) baseStart_2800373 baseEnd_2800373 := by
    simpa [prefixWord, tailWord_2800373, baseEnd_2800373] using wordTrace_append hprefix tailTrace_2800373
  have hstable : (prefixWord ++ tailWord_2800373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2800373).length < 2 ^ (prefixWord ++ tailWord_2800373).sum := by decide
  have hdescent : baseEnd_2800373 < baseStart_2800373 := by decide
  rcases family_descends (prefixWord ++ tailWord_2800373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2800382 : List Nat := [4, 2, 2, 1, 2, 2, 9]
def baseStart_2800382 : Nat := 118140960795 + 2800382 * 2 ^ 59
def prefixEnd_2800382 : Nat := 4983230072969 + 3 ^ 40 * 2800382 * 2
def baseEnd_2800382 : Nat := 35504740301214017932007

theorem tailTrace_2800382 : CollatzResearch.WordTrace tailWord_2800382 prefixEnd_2800382 35504740301214017932007 := by
  unfold tailWord_2800382
  simp only [CollatzResearch.WordTrace]
  refine ⟨12767290317587719501739425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68092215027134504009276933 12767290317587719501739425)
  ·
    refine ⟨9575467738190789626304569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12767290317587719501739425 9575467738190789626304569)
    ·
      refine ⟨7181600803643092219728427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9575467738190789626304569 7181600803643092219728427)
      ·
        refine ⟨10772401205464638329592641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7181600803643092219728427 10772401205464638329592641)
        ·
          refine ⟨8079300904098478747194481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10772401205464638329592641 8079300904098478747194481)
          ·
            refine ⟨6059475678073859060395861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8079300904098478747194481 6059475678073859060395861)
            ·
              refine ⟨35504740301214017932007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6059475678073859060395861 35504740301214017932007)
              ·
                rfl

theorem cell22_2800382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 9].length) (baseStart_2800382 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2800382 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2800382 prefixEnd_2800382 := by exact prefixLift 2800382
  have htrace : WordTrace (prefixWord ++ tailWord_2800382) baseStart_2800382 baseEnd_2800382 := by
    simpa [prefixWord, tailWord_2800382, baseEnd_2800382] using wordTrace_append hprefix tailTrace_2800382
  have hstable : (prefixWord ++ tailWord_2800382).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2800382).length < 2 ^ (prefixWord ++ tailWord_2800382).sum := by decide
  have hdescent : baseEnd_2800382 < baseStart_2800382 := by decide
  rcases family_descends (prefixWord ++ tailWord_2800382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2800386 : List Nat := [3, 4, 1, 1, 1, 2, 3, 2, 2, 3]
def baseStart_2800386 : Nat := 118140960795 + 2800386 * 2 ^ 59
def prefixEnd_2800386 : Nat := 4983230072969 + 3 ^ 40 * 2800386 * 2
def baseEnd_2800386 : Nat := 958629357414523807064177

theorem tailTrace_2800386 : CollatzResearch.WordTrace tailWord_2800386 prefixEnd_2800386 958629357414523807064177 := by
  unfold tailWord_2800386
  simp only [CollatzResearch.WordTrace]
  refine ⟨25534617108171816174265253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68092312288458176464707341 25534617108171816174265253)
  ·
    refine ⟨4787740707782215532674735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25534617108171816174265253 4787740707782215532674735)
    ·
      refine ⟨7181611061673323299012103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4787740707782215532674735 7181611061673323299012103)
      ·
        refine ⟨10772416592509984948518155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7181611061673323299012103 10772416592509984948518155)
        ·
          refine ⟨16158624888764977422777233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10772416592509984948518155 16158624888764977422777233)
          ·
            refine ⟨12118968666573733067082925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16158624888764977422777233 12118968666573733067082925)
            ·
              refine ⟨4544613249965149900156097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12118968666573733067082925 4544613249965149900156097)
              ·
                refine ⟨3408459937473862425117073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4544613249965149900156097 3408459937473862425117073)
                ·
                  refine ⟨2556344953105396818837805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3408459937473862425117073 2556344953105396818837805)
                  ·
                    refine ⟨958629357414523807064177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2556344953105396818837805 958629357414523807064177)
                    ·
                      rfl

theorem cell22_2800386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 3, 2, 2, 3].length) (baseStart_2800386 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2800386 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2800386 prefixEnd_2800386 := by exact prefixLift 2800386
  have htrace : WordTrace (prefixWord ++ tailWord_2800386) baseStart_2800386 baseEnd_2800386 := by
    simpa [prefixWord, tailWord_2800386, baseEnd_2800386] using wordTrace_append hprefix tailTrace_2800386
  have hstable : (prefixWord ++ tailWord_2800386).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2800386).length < 2 ^ (prefixWord ++ tailWord_2800386).sum := by decide
  have hdescent : baseEnd_2800386 < baseStart_2800386 := by decide
  rcases family_descends (prefixWord ++ tailWord_2800386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2800461 : List Nat := [1, 6, 1, 2, 2, 1, 1, 3, 5]
def baseStart_2800461 : Nat := 118140960795 + 2800461 * 2 ^ 59
def prefixEnd_2800461 : Nat := 4983230072969 + 3 ^ 40 * 2800461 * 2
def baseEnd_2800461 : Nat := 319551677149082870479649

theorem tailTrace_2800461 : CollatzResearch.WordTrace tailWord_2800461 prefixEnd_2800461 319551677149082870479649 := by
  unfold tailWord_2800461
  simp only [CollatzResearch.WordTrace]
  refine ⟨102141203907415552506041237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68094135938277035004027491 102141203907415552506041237)
  ·
    refine ⟨4787868933160104023720683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 102141203907415552506041237 4787868933160104023720683)
    ·
      refine ⟨7181803399740156035581025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4787868933160104023720683 7181803399740156035581025)
      ·
        refine ⟨5386352549805117026685769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7181803399740156035581025 5386352549805117026685769)
        ·
          refine ⟨4039764412353837770014327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5386352549805117026685769 4039764412353837770014327)
          ·
            refine ⟨6059646618530756655021491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4039764412353837770014327 6059646618530756655021491)
            ·
              refine ⟨9089469927796134982532237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6059646618530756655021491 9089469927796134982532237)
              ·
                refine ⟨3408551222923550618449589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9089469927796134982532237 3408551222923550618449589)
                ·
                  refine ⟨319551677149082870479649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3408551222923550618449589 319551677149082870479649)
                  ·
                    rfl

theorem cell22_2800461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 3, 5].length) (baseStart_2800461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2800461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2800461 prefixEnd_2800461 := by exact prefixLift 2800461
  have htrace : WordTrace (prefixWord ++ tailWord_2800461) baseStart_2800461 baseEnd_2800461 := by
    simpa [prefixWord, tailWord_2800461, baseEnd_2800461] using wordTrace_append hprefix tailTrace_2800461
  have hstable : (prefixWord ++ tailWord_2800461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2800461).length < 2 ^ (prefixWord ++ tailWord_2800461).sum := by decide
  have hdescent : baseEnd_2800461 < baseStart_2800461 := by decide
  rcases family_descends (prefixWord ++ tailWord_2800461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2800474 : List Nat := [3, 1, 1, 2, 1, 4, 3, 2, 1, 4]
def baseStart_2800474 : Nat := 118140960795 + 2800474 * 2 ^ 59
def prefixEnd_2800474 : Nat := 4983230072969 + 3 ^ 40 * 2800474 * 2
def baseEnd_2800474 : Nat := 958659481612920910863907

theorem tailTrace_2800474 : CollatzResearch.WordTrace tailWord_2800474 prefixEnd_2800474 958659481612920910863907 := by
  unfold tailWord_2800474
  simp only [CollatzResearch.WordTrace]
  refine ⟨25535419514092113931566119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68094452037578970484176317 25535419514092113931566119)
  ·
    refine ⟨38303129271138170897349179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25535419514092113931566119 38303129271138170897349179)
    ·
      refine ⟨57454693906707256346023769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38303129271138170897349179 57454693906707256346023769)
      ·
        refine ⟨43091020430030442259517827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57454693906707256346023769 43091020430030442259517827)
        ·
          refine ⟨64636530645045663389276741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43091020430030442259517827 64636530645045663389276741)
          ·
            refine ⟨12119349495946061885489389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64636530645045663389276741 12119349495946061885489389)
            ·
              refine ⟨4544756060979773207058521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12119349495946061885489389 4544756060979773207058521)
              ·
                refine ⟨3408567045734829905293891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4544756060979773207058521 3408567045734829905293891)
                ·
                  refine ⟨5112850568602244857940837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3408567045734829905293891 5112850568602244857940837)
                  ·
                    refine ⟨958659481612920910863907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5112850568602244857940837 958659481612920910863907)
                    ·
                      rfl

theorem cell22_2800474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 3, 2, 1, 4].length) (baseStart_2800474 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2800474 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2800474 prefixEnd_2800474 := by exact prefixLift 2800474
  have htrace : WordTrace (prefixWord ++ tailWord_2800474) baseStart_2800474 baseEnd_2800474 := by
    simpa [prefixWord, tailWord_2800474, baseEnd_2800474] using wordTrace_append hprefix tailTrace_2800474
  have hstable : (prefixWord ++ tailWord_2800474).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2800474).length < 2 ^ (prefixWord ++ tailWord_2800474).sum := by decide
  have hdescent : baseEnd_2800474 < baseStart_2800474 := by decide
  rcases family_descends (prefixWord ++ tailWord_2800474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2800487 : List Nat := [1, 1, 5, 1, 2, 2, 1, 1, 3, 5]
def baseStart_2800487 : Nat := 118140960795 + 2800487 * 2 ^ 59
def prefixEnd_2800487 : Nat := 4983230072969 + 3 ^ 40 * 2800487 * 2
def baseEnd_2800487 : Nat := 958663931778593210288867

theorem tailTrace_2800487 : CollatzResearch.WordTrace tailWord_2800487 prefixEnd_2800487 958663931778593210288867 := by
  unfold tailWord_2800487
  simp only [CollatzResearch.WordTrace]
  refine ⟨102142152205321358946487715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68094768136880905964325143 102142152205321358946487715)
  ·
    refine ⟨153213228307982038419731573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102142152205321358946487715 153213228307982038419731573)
    ·
      refine ⟨14363740153873316101849835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 153213228307982038419731573 14363740153873316101849835)
      ·
        refine ⟨21545610230809974152774753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14363740153873316101849835 21545610230809974152774753)
        ·
          refine ⟨16159207673107480614581065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21545610230809974152774753 16159207673107480614581065)
          ·
            refine ⟨12119405754830610460935799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16159207673107480614581065 12119405754830610460935799)
            ·
              refine ⟨18179108632245915691403699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12119405754830610460935799 18179108632245915691403699)
              ·
                refine ⟨27268662948368873537105549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18179108632245915691403699 27268662948368873537105549)
                ·
                  refine ⟨10225748605638327576414581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27268662948368873537105549 10225748605638327576414581)
                  ·
                    refine ⟨958663931778593210288867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10225748605638327576414581 958663931778593210288867)
                    ·
                      rfl

theorem cell22_2800487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 1, 3, 5].length) (baseStart_2800487 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2800487 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2800487 prefixEnd_2800487 := by exact prefixLift 2800487
  have htrace : WordTrace (prefixWord ++ tailWord_2800487) baseStart_2800487 baseEnd_2800487 := by
    simpa [prefixWord, tailWord_2800487, baseEnd_2800487] using wordTrace_append hprefix tailTrace_2800487
  have hstable : (prefixWord ++ tailWord_2800487).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2800487).length < 2 ^ (prefixWord ++ tailWord_2800487).sum := by decide
  have hdescent : baseEnd_2800487 < baseStart_2800487 := by decide
  rcases family_descends (prefixWord ++ tailWord_2800487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
