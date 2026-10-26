import V185TrunkScan23Chunk1133

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6717008 : List Nat := [2, 1, 1, 1, 1, 3, 7, 2, 1, 2, 2]
def baseStart_6717008 : Nat := 118140960795 + 6717008 * 2 ^ 59
def prefixEnd_6717008 : Nat := 4983230072969 + 3 ^ 40 * 6717008 * 2
def baseEnd_6717008 : Nat := 3449053664095560909009049

theorem tailTrace_6717008 : CollatzResearch.WordTrace tailWord_6717008 prefixEnd_6717008 3449053664095560909009049 := by
  unfold tailWord_6717008
  simp only [CollatzResearch.WordTrace]
  refine ⟨122494704224717332240175839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163326272299623109653567785 122494704224717332240175839)
  ·
    refine ⟨183742056337075998360263759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122494704224717332240175839 183742056337075998360263759)
    ·
      refine ⟨275613084505613997540395639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183742056337075998360263759 275613084505613997540395639)
      ·
        refine ⟨413419626758420996310593459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275613084505613997540395639 413419626758420996310593459)
        ·
          refine ⟨620129440137631494465890189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 413419626758420996310593459 620129440137631494465890189)
          ·
            refine ⟨232548540051611810424708821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 620129440137631494465890189 232548540051611810424708821)
            ·
              refine ⟨5450356407459651806829113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 232548540051611810424708821 5450356407459651806829113)
              ·
                refine ⟨4087767305594738855121835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5450356407459651806829113 4087767305594738855121835)
                ·
                  refine ⟨6131650958392108282682753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4087767305594738855121835 6131650958392108282682753)
                  ·
                    refine ⟨4598738218794081212012065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6131650958392108282682753 4598738218794081212012065)
                    ·
                      refine ⟨3449053664095560909009049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4598738218794081212012065 3449053664095560909009049)
                      ·
                        rfl

theorem cell23_6717008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 7, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 7, 2, 1, 2, 2].length) (baseStart_6717008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6717008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6717008 prefixEnd_6717008 := by exact prefixLift 6717008
  have htrace : WordTrace (prefixWord ++ tailWord_6717008) baseStart_6717008 baseEnd_6717008 := by
    simpa [prefixWord, tailWord_6717008, baseEnd_6717008] using wordTrace_append hprefix tailTrace_6717008
  have hstable : (prefixWord ++ tailWord_6717008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6717008).length < 2 ^ (prefixWord ++ tailWord_6717008).sum := by decide
  have hdescent : baseEnd_6717008 < baseStart_6717008 := by decide
  rcases family_descends (prefixWord ++ tailWord_6717008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6717050 : List Nat := [3, 1, 1, 1, 1, 1, 1, 5, 1, 3, 5]
def baseStart_6717050 : Nat := 118140960795 + 6717050 * 2 ^ 59
def prefixEnd_6717050 : Nat := 4983230072969 + 3 ^ 40 * 6717050 * 2
def baseEnd_6717050 : Nat := 3449075230283049744683855

theorem tailTrace_6717050 : CollatzResearch.WordTrace tailWord_6717050 prefixEnd_6717050 3449075230283049744683855 := by
  unfold tailWord_6717050
  simp only [CollatzResearch.WordTrace]
  refine ⟨61247735078820626413345151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163327293543521670435587069 61247735078820626413345151)
  ·
    refine ⟨91871602618230939620017727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61247735078820626413345151 91871602618230939620017727)
    ·
      refine ⟨137807403927346409430026591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91871602618230939620017727 137807403927346409430026591)
      ·
        refine ⟨206711105891019614145039887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137807403927346409430026591 206711105891019614145039887)
        ·
          refine ⟨310066658836529421217559831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206711105891019614145039887 310066658836529421217559831)
          ·
            refine ⟨465099988254794131826339747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 310066658836529421217559831 465099988254794131826339747)
            ·
              refine ⟨697649982382191197739509621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 465099988254794131826339747 697649982382191197739509621)
              ·
                refine ⟨65404685848330424788079027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 697649982382191197739509621 65404685848330424788079027)
                ·
                  refine ⟨98107028772495637182118541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65404685848330424788079027 98107028772495637182118541)
                  ·
                    refine ⟨36790135789685863943294453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 98107028772495637182118541 36790135789685863943294453)
                    ·
                      refine ⟨3449075230283049744683855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36790135789685863943294453 3449075230283049744683855)
                      ·
                        rfl

theorem cell23_6717050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 5, 1, 3, 5].length) (baseStart_6717050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6717050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6717050 prefixEnd_6717050 := by exact prefixLift 6717050
  have htrace : WordTrace (prefixWord ++ tailWord_6717050) baseStart_6717050 baseEnd_6717050 := by
    simpa [prefixWord, tailWord_6717050, baseEnd_6717050] using wordTrace_append hprefix tailTrace_6717050
  have hstable : (prefixWord ++ tailWord_6717050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6717050).length < 2 ^ (prefixWord ++ tailWord_6717050).sum := by decide
  have hdescent : baseEnd_6717050 < baseStart_6717050 := by decide
  rcases family_descends (prefixWord ++ tailWord_6717050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6717051 : List Nat := [1, 1, 1, 1, 1, 4, 7, 1, 1, 3, 2]
def baseStart_6717051 : Nat := 118140960795 + 6717051 * 2 ^ 59
def prefixEnd_6717051 : Nat := 4983230072969 + 3 ^ 40 * 6717051 * 2
def baseEnd_6717051 : Nat := 3449075743763704240771351

theorem tailTrace_6717051 : CollatzResearch.WordTrace tailWord_6717051 prefixEnd_6717051 3449075743763704240771351 := by
  unfold tailWord_6717051
  simp only [CollatzResearch.WordTrace]
  refine ⟨244990976788278882824167007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163327317858852588549444671 244990976788278882824167007)
  ·
    refine ⟨367486465182418324236250511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244990976788278882824167007 367486465182418324236250511)
    ·
      refine ⟨551229697773627486354375767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 367486465182418324236250511 551229697773627486354375767)
      ·
        refine ⟨826844546660441229531563651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 551229697773627486354375767 826844546660441229531563651)
        ·
          refine ⟨1240266819990661844297345477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 826844546660441229531563651 1240266819990661844297345477)
          ·
            refine ⟨232550028748249095805752277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1240266819990661844297345477 232550028748249095805752277)
            ·
              refine ⟨5450391298787088182947319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 232550028748249095805752277 5450391298787088182947319)
              ·
                refine ⟨8175586948180632274420979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5450391298787088182947319 8175586948180632274420979)
                ·
                  refine ⟨12263380422270948411631469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8175586948180632274420979 12263380422270948411631469)
                  ·
                    refine ⟨4598767658351605654361801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12263380422270948411631469 4598767658351605654361801)
                    ·
                      refine ⟨3449075743763704240771351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4598767658351605654361801 3449075743763704240771351)
                      ·
                        rfl

theorem cell23_6717051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 7, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 7, 1, 1, 3, 2].length) (baseStart_6717051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6717051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6717051 prefixEnd_6717051 := by exact prefixLift 6717051
  have htrace : WordTrace (prefixWord ++ tailWord_6717051) baseStart_6717051 baseEnd_6717051 := by
    simpa [prefixWord, tailWord_6717051, baseEnd_6717051] using wordTrace_append hprefix tailTrace_6717051
  have hstable : (prefixWord ++ tailWord_6717051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6717051).length < 2 ^ (prefixWord ++ tailWord_6717051).sum := by decide
  have hdescent : baseEnd_6717051 < baseStart_6717051 := by decide
  rcases family_descends (prefixWord ++ tailWord_6717051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6717074 : List Nat := [3, 2, 3, 1, 3, 1, 1, 1, 2, 6]
def baseStart_6717074 : Nat := 118140960795 + 6717074 * 2 ^ 59
def prefixEnd_6717074 : Nat := 4983230072969 + 3 ^ 40 * 6717074 * 2
def baseEnd_6717074 : Nat := 1149695851272919216927915

theorem tailTrace_6717074 : CollatzResearch.WordTrace tailWord_6717074 prefixEnd_6717074 1149695851272919216927915 := by
  unfold tailWord_6717074
  simp only [CollatzResearch.WordTrace]
  refine ⟨61247953916798889438063569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163327877111463705168169517 61247953916798889438063569)
  ·
    refine ⟨45935965437599167078547677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61247953916798889438063569 45935965437599167078547677)
    ·
      refine ⟨17225987039099687654455379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45935965437599167078547677 17225987039099687654455379)
      ·
        refine ⟨25838980558649531481683069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17225987039099687654455379 25838980558649531481683069)
        ·
          refine ⟨9689617709493574305631151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25838980558649531481683069 9689617709493574305631151)
          ·
            refine ⟨14534426564240361458446727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9689617709493574305631151 14534426564240361458446727)
            ·
              refine ⟨21801639846360542187670091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14534426564240361458446727 21801639846360542187670091)
              ·
                refine ⟨32702459769540813281505137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21801639846360542187670091 32702459769540813281505137)
                ·
                  refine ⟨24526844827155609961128853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32702459769540813281505137 24526844827155609961128853)
                  ·
                    refine ⟨1149695851272919216927915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24526844827155609961128853 1149695851272919216927915)
                    ·
                      rfl

theorem cell23_6717074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 1, 2, 6].length) (baseStart_6717074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6717074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6717074 prefixEnd_6717074 := by exact prefixLift 6717074
  have htrace : WordTrace (prefixWord ++ tailWord_6717074) baseStart_6717074 baseEnd_6717074 := by
    simpa [prefixWord, tailWord_6717074, baseEnd_6717074] using wordTrace_append hprefix tailTrace_6717074
  have hstable : (prefixWord ++ tailWord_6717074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6717074).length < 2 ^ (prefixWord ++ tailWord_6717074).sum := by decide
  have hdescent : baseEnd_6717074 < baseStart_6717074 := by decide
  rcases family_descends (prefixWord ++ tailWord_6717074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6717102 : List Nat := [4, 1, 4, 1, 2, 2, 2, 1, 1, 3, 2]
def baseStart_6717102 : Nat := 118140960795 + 6717102 * 2 ^ 59
def prefixEnd_6717102 : Nat := 4983230072969 + 3 ^ 40 * 6717102 * 2
def baseEnd_6717102 : Nat := 3449101931277083541233617

theorem tailTrace_6717102 : CollatzResearch.WordTrace tailWord_6717102 prefixEnd_6717102 3449101931277083541233617 := by
  unfold tailWord_6717102
  simp only [CollatzResearch.WordTrace]
  refine ⟨30624104613886764816784195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 163328557940729412356182373 30624104613886764816784195)
  ·
    refine ⟨45936156920830147225176293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30624104613886764816784195 45936156920830147225176293)
    ·
      refine ⟨8613029422655652604720555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45936156920830147225176293 8613029422655652604720555)
      ·
        refine ⟨12919544133983478907080833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8613029422655652604720555 12919544133983478907080833)
        ·
          refine ⟨9689658100487609180310625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12919544133983478907080833 9689658100487609180310625)
          ·
            refine ⟨7267243575365706885232969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9689658100487609180310625 7267243575365706885232969)
            ·
              refine ⟨5450432681524280163924727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7267243575365706885232969 5450432681524280163924727)
              ·
                refine ⟨8175649022286420245887091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5450432681524280163924727 8175649022286420245887091)
                ·
                  refine ⟨12263473533429630368830637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8175649022286420245887091 12263473533429630368830637)
                  ·
                    refine ⟨4598802575036111388311489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12263473533429630368830637 4598802575036111388311489)
                    ·
                      refine ⟨3449101931277083541233617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4598802575036111388311489 3449101931277083541233617)
                      ·
                        rfl

theorem cell23_6717102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 2, 1, 1, 3, 2].length) (baseStart_6717102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6717102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6717102 prefixEnd_6717102 := by exact prefixLift 6717102
  have htrace : WordTrace (prefixWord ++ tailWord_6717102) baseStart_6717102 baseEnd_6717102 := by
    simpa [prefixWord, tailWord_6717102, baseEnd_6717102] using wordTrace_append hprefix tailTrace_6717102
  have hstable : (prefixWord ++ tailWord_6717102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6717102).length < 2 ^ (prefixWord ++ tailWord_6717102).sum := by decide
  have hdescent : baseEnd_6717102 < baseStart_6717102 := by decide
  rcases family_descends (prefixWord ++ tailWord_6717102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6717117 : List Nat := [1, 4, 1, 2, 1, 2, 2, 1, 4, 5]
def baseStart_6717117 : Nat := 118140960795 + 6717117 * 2 ^ 59
def prefixEnd_6717117 : Nat := 4983230072969 + 3 ^ 40 * 6717117 * 2
def baseEnd_6717117 : Nat := 1149703211162300327515349

theorem tailTrace_6717117 : CollatzResearch.WordTrace tailWord_6717117 prefixEnd_6717117 1149703211162300327515349 := by
  unfold tailWord_6717117
  simp only [CollatzResearch.WordTrace]
  refine ⟨244993384006039776096069605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163328922670693184064046403 244993384006039776096069605)
  ·
    refine ⟨45936259501132458018013051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 244993384006039776096069605 45936259501132458018013051)
    ·
      refine ⟨68904389251698687027019577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45936259501132458018013051 68904389251698687027019577)
      ·
        refine ⟨51678291938774015270264683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68904389251698687027019577 51678291938774015270264683)
        ·
          refine ⟨77517437908161022905397025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51678291938774015270264683 77517437908161022905397025)
          ·
            refine ⟨58138078431120767179047769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77517437908161022905397025 58138078431120767179047769)
            ·
              refine ⟨43603558823340575384285827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58138078431120767179047769 43603558823340575384285827)
              ·
                refine ⟨65405338235010863076428741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43603558823340575384285827 65405338235010863076428741)
                ·
                  refine ⟨12263500919064536826830389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65405338235010863076428741 12263500919064536826830389)
                  ·
                    refine ⟨1149703211162300327515349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12263500919064536826830389 1149703211162300327515349)
                    ·
                      rfl

theorem cell23_6717117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 1, 4, 5].length) (baseStart_6717117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6717117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6717117 prefixEnd_6717117 := by exact prefixLift 6717117
  have htrace : WordTrace (prefixWord ++ tailWord_6717117) baseStart_6717117 baseEnd_6717117 := by
    simpa [prefixWord, tailWord_6717117, baseEnd_6717117] using wordTrace_append hprefix tailTrace_6717117
  have hstable : (prefixWord ++ tailWord_6717117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6717117).length < 2 ^ (prefixWord ++ tailWord_6717117).sum := by decide
  have hdescent : baseEnd_6717117 < baseStart_6717117 := by decide
  rcases family_descends (prefixWord ++ tailWord_6717117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6717137 : List Nat := [1, 2, 2, 1, 2, 4, 1, 2, 1, 3, 4]
def baseStart_6717137 : Nat := 118140960795 + 6717137 * 2 ^ 59
def prefixEnd_6717137 : Nat := 4983230072969 + 3 ^ 40 * 6717137 * 2
def baseEnd_6717137 : Nat := 3449119903099990904295955

theorem tailTrace_6717137 : CollatzResearch.WordTrace tailWord_6717137 prefixEnd_6717137 3449119903099990904295955 := by
  unfold tailWord_6717137
  simp only [CollatzResearch.WordTrace]
  refine ⟨244994113465967319511797665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163329408977311546341198443 244994113465967319511797665)
  ·
    refine ⟨183745585099475489633848249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244994113465967319511797665 183745585099475489633848249)
    ·
      refine ⟨137809188824606617225386187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183745585099475489633848249 137809188824606617225386187)
      ·
        refine ⟨206713783236909925838079281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137809188824606617225386187 206713783236909925838079281)
        ·
          refine ⟨155035337427682444378559461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 206713783236909925838079281 155035337427682444378559461)
          ·
            refine ⟨29069125767690458320979899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 155035337427682444378559461 29069125767690458320979899)
            ·
              refine ⟨43603688651535687481469849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29069125767690458320979899 43603688651535687481469849)
              ·
                refine ⟨32702766488651765611102387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43603688651535687481469849 32702766488651765611102387)
                ·
                  refine ⟨49054149732977648416653581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32702766488651765611102387 49054149732977648416653581)
                  ·
                    refine ⟨18395306149866618156245093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49054149732977648416653581 18395306149866618156245093)
                    ·
                      refine ⟨3449119903099990904295955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18395306149866618156245093 3449119903099990904295955)
                      ·
                        rfl

theorem cell23_6717137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 2, 1, 3, 4].length) (baseStart_6717137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6717137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6717137 prefixEnd_6717137 := by exact prefixLift 6717137
  have htrace : WordTrace (prefixWord ++ tailWord_6717137) baseStart_6717137 baseEnd_6717137 := by
    simpa [prefixWord, tailWord_6717137, baseEnd_6717137] using wordTrace_append hprefix tailTrace_6717137
  have hstable : (prefixWord ++ tailWord_6717137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6717137).length < 2 ^ (prefixWord ++ tailWord_6717137).sum := by decide
  have hdescent : baseEnd_6717137 < baseStart_6717137 := by decide
  rcases family_descends (prefixWord ++ tailWord_6717137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6717194 : List Nat := [3, 1, 2, 2, 1, 4, 1, 3, 6]
def baseStart_6717194 : Nat := 118140960795 + 6717194 * 2 ^ 59
def prefixEnd_6717194 : Nat := 4983230072969 + 3 ^ 40 * 6717194 * 2
def baseEnd_6717194 : Nat := 383238796833033020142577

theorem tailTrace_6717194 : CollatzResearch.WordTrace tailWord_6717194 prefixEnd_6717194 383238796833033020142577 := by
  unfold tailWord_6717194
  simp only [CollatzResearch.WordTrace]
  refine ⟨61249048106690204561655659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163330794951173878831081757 61249048106690204561655659)
  ·
    refine ⟨91873572160035306842483489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61249048106690204561655659 91873572160035306842483489)
    ·
      refine ⟨68905179120026480131862617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91873572160035306842483489 68905179120026480131862617)
      ·
        refine ⟨51678884340019860098896963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68905179120026480131862617 51678884340019860098896963)
        ·
          refine ⟨77518326510029790148345445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51678884340019860098896963 77518326510029790148345445)
          ·
            refine ⟨14534686220630585652814771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 77518326510029790148345445 14534686220630585652814771)
            ·
              refine ⟨21802029330945878479222157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14534686220630585652814771 21802029330945878479222157)
              ·
                refine ⟨8175760999104704429708309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21802029330945878479222157 8175760999104704429708309)
                ·
                  refine ⟨383238796833033020142577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8175760999104704429708309 383238796833033020142577)
                  ·
                    rfl

theorem cell23_6717194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 3, 6].length) (baseStart_6717194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6717194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6717194 prefixEnd_6717194 := by exact prefixLift 6717194
  have htrace : WordTrace (prefixWord ++ tailWord_6717194) baseStart_6717194 baseEnd_6717194 := by
    simpa [prefixWord, tailWord_6717194, baseEnd_6717194] using wordTrace_append hprefix tailTrace_6717194
  have hstable : (prefixWord ++ tailWord_6717194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6717194).length < 2 ^ (prefixWord ++ tailWord_6717194).sum := by decide
  have hdescent : baseEnd_6717194 < baseStart_6717194 := by decide
  rcases family_descends (prefixWord ++ tailWord_6717194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6717244 : List Nat := [2, 2, 2, 2, 1, 1, 3, 2, 3, 1, 4]
def baseStart_6717244 : Nat := 118140960795 + 6717244 * 2 ^ 59
def prefixEnd_6717244 : Nat := 4983230072969 + 3 ^ 40 * 6717244 * 2
def baseEnd_6717244 : Nat := 3449174845530021985657963

theorem tailTrace_6717244 : CollatzResearch.WordTrace tailWord_6717244 prefixEnd_6717244 3449174845530021985657963 := by
  unfold tailWord_6717244
  simp only [CollatzResearch.WordTrace]
  refine ⟨122499008038289838392971393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163332010717719784523961857 122499008038289838392971393)
  ·
    refine ⟨91874256028717378794728545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122499008038289838392971393 91874256028717378794728545)
    ·
      refine ⟨68905692021538034096046409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91874256028717378794728545 68905692021538034096046409)
      ·
        refine ⟨51679269016153525572034807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68905692021538034096046409 51679269016153525572034807)
        ·
          refine ⟨77518903524230288358052211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51679269016153525572034807 77518903524230288358052211)
          ·
            refine ⟨116278355286345432537078317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77518903524230288358052211 116278355286345432537078317)
            ·
              refine ⟨43604383232379537201404369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 116278355286345432537078317 43604383232379537201404369)
              ·
                refine ⟨32703287424284652901053277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43604383232379537201404369 32703287424284652901053277)
                ·
                  refine ⟨12263732784106744837894979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32703287424284652901053277 12263732784106744837894979)
                  ·
                    refine ⟨18395599176160117256842469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12263732784106744837894979 18395599176160117256842469)
                    ·
                      refine ⟨3449174845530021985657963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18395599176160117256842469 3449174845530021985657963)
                      ·
                        rfl

theorem cell23_6717244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 2, 3, 1, 4].length) (baseStart_6717244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6717244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6717244 prefixEnd_6717244 := by exact prefixLift 6717244
  have htrace : WordTrace (prefixWord ++ tailWord_6717244) baseStart_6717244 baseEnd_6717244 := by
    simpa [prefixWord, tailWord_6717244, baseEnd_6717244] using wordTrace_append hprefix tailTrace_6717244
  have hstable : (prefixWord ++ tailWord_6717244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6717244).length < 2 ^ (prefixWord ++ tailWord_6717244).sum := by decide
  have hdescent : baseEnd_6717244 < baseStart_6717244 := by decide
  rcases family_descends (prefixWord ++ tailWord_6717244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6717274 : List Nat := [3, 1, 1, 2, 1, 3, 1, 4, 1, 2, 4]
def baseStart_6717274 : Nat := 118140960795 + 6717274 * 2 ^ 59
def prefixEnd_6717274 : Nat := 4983230072969 + 3 ^ 40 * 6717274 * 2
def baseEnd_6717274 : Nat := 3449190249949656868282825

theorem tailTrace_6717274 : CollatzResearch.WordTrace tailWord_6717274 prefixEnd_6717274 3449190249949656868282825 := by
  unfold tailWord_6717274
  simp only [CollatzResearch.WordTrace]
  refine ⟨61249777566617747977383719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163332740177647327939689917 61249777566617747977383719)
  ·
    refine ⟨91874666349926621966075579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61249777566617747977383719 91874666349926621966075579)
    ·
      refine ⟨137811999524889932949113369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91874666349926621966075579 137811999524889932949113369)
      ·
        refine ⟨103358999643667449711835027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137811999524889932949113369 103358999643667449711835027)
        ·
          refine ⟨155038499465501174567752541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103358999643667449711835027 155038499465501174567752541)
          ·
            refine ⟨58139437299562940462907203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 155038499465501174567752541 58139437299562940462907203)
            ·
              refine ⟨87209155949344410694360805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58139437299562940462907203 87209155949344410694360805)
              ·
                refine ⟨16351716740502077005192651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 87209155949344410694360805 16351716740502077005192651)
                ·
                  refine ⟨24527575110753115507788977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16351716740502077005192651 24527575110753115507788977)
                  ·
                    refine ⟨18395681333064836630841733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24527575110753115507788977 18395681333064836630841733)
                    ·
                      refine ⟨3449190249949656868282825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18395681333064836630841733 3449190249949656868282825)
                      ·
                        rfl

theorem cell23_6717274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 4, 1, 2, 4].length) (baseStart_6717274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6717274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6717274 prefixEnd_6717274 := by exact prefixLift 6717274
  have htrace : WordTrace (prefixWord ++ tailWord_6717274) baseStart_6717274 baseEnd_6717274 := by
    simpa [prefixWord, tailWord_6717274, baseEnd_6717274] using wordTrace_append hprefix tailTrace_6717274
  have hstable : (prefixWord ++ tailWord_6717274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6717274).length < 2 ^ (prefixWord ++ tailWord_6717274).sum := by decide
  have hdescent : baseEnd_6717274 < baseStart_6717274 := by decide
  rcases family_descends (prefixWord ++ tailWord_6717274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6717281 : List Nat := [1, 2, 3, 1, 1, 1, 5, 3, 1, 2, 3]
def baseStart_6717281 : Nat := 118140960795 + 6717281 * 2 ^ 59
def prefixEnd_6717281 : Nat := 4983230072969 + 3 ^ 40 * 6717281 * 2
def baseEnd_6717281 : Nat := 3449193844314238340895293

theorem tailTrace_6717281 : CollatzResearch.WordTrace tailWord_6717281 prefixEnd_6717281 3449193844314238340895293 := by
  unfold tailWord_6717281
  simp only [CollatzResearch.WordTrace]
  refine ⟨244999365577445632105039697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163332910384963754736693131 244999365577445632105039697)
  ·
    refine ⟨183749524183084224078779773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244999365577445632105039697 183749524183084224078779773)
    ·
      refine ⟨68906071568656584029542415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 183749524183084224078779773 68906071568656584029542415)
      ·
        refine ⟨103359107352984876044313623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68906071568656584029542415 103359107352984876044313623)
        ·
          refine ⟨155038661029477314066470435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103359107352984876044313623 155038661029477314066470435)
          ·
            refine ⟨232557991544215971099705653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155038661029477314066470435 232557991544215971099705653)
            ·
              refine ⟨21802311707270247290597405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 232557991544215971099705653 21802311707270247290597405)
              ·
                refine ⟨8175866890226342733974027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21802311707270247290597405 8175866890226342733974027)
                ·
                  refine ⟨12263800335339514100961041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8175866890226342733974027 12263800335339514100961041)
                  ·
                    refine ⟨9197850251504635575720781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12263800335339514100961041 9197850251504635575720781)
                    ·
                      refine ⟨3449193844314238340895293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9197850251504635575720781 3449193844314238340895293)
                      ·
                        rfl

theorem cell23_6717281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 3, 1, 2, 3].length) (baseStart_6717281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6717281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6717281 prefixEnd_6717281 := by exact prefixLift 6717281
  have htrace : WordTrace (prefixWord ++ tailWord_6717281) baseStart_6717281 baseEnd_6717281 := by
    simpa [prefixWord, tailWord_6717281, baseEnd_6717281] using wordTrace_append hprefix tailTrace_6717281
  have hstable : (prefixWord ++ tailWord_6717281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6717281).length < 2 ^ (prefixWord ++ tailWord_6717281).sum := by decide
  have hdescent : baseEnd_6717281 < baseStart_6717281 := by decide
  rcases family_descends (prefixWord ++ tailWord_6717281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6717284 : List Nat := [2, 3, 1, 1, 5, 1, 10]
def baseStart_6717284 : Nat := 118140960795 + 6717284 * 2 ^ 59
def prefixEnd_6717284 : Nat := 4983230072969 + 3 ^ 40 * 6717284 * 2
def baseEnd_6717284 : Nat := 42582659071064220113059

theorem tailTrace_6717284 : CollatzResearch.WordTrace tailWord_6717284 prefixEnd_6717284 42582659071064220113059 := by
  unfold tailWord_6717284
  simp only [CollatzResearch.WordTrace]
  refine ⟨122499737498217381808699453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163332983330956509078265937 122499737498217381808699453)
  ·
    refine ⟨45937401561831518178262295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122499737498217381808699453 45937401561831518178262295)
    ·
      refine ⟨68906102342747277267393443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45937401561831518178262295 68906102342747277267393443)
      ·
        refine ⟨103359153514120915901090165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68906102342747277267393443 103359153514120915901090165)
        ·
          refine ⟨9689920641948835865727203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 103359153514120915901090165 9689920641948835865727203)
          ·
            refine ⟨14534880962923253798590805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9689920641948835865727203 14534880962923253798590805)
            ·
              refine ⟨42582659071064220113059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 14534880962923253798590805 42582659071064220113059)
              ·
                rfl

theorem cell23_6717284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 10].length) (baseStart_6717284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6717284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6717284 prefixEnd_6717284 := by exact prefixLift 6717284
  have htrace : WordTrace (prefixWord ++ tailWord_6717284) baseStart_6717284 baseEnd_6717284 := by
    simpa [prefixWord, tailWord_6717284, baseEnd_6717284] using wordTrace_append hprefix tailTrace_6717284
  have hstable : (prefixWord ++ tailWord_6717284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6717284).length < 2 ^ (prefixWord ++ tailWord_6717284).sum := by decide
  have hdescent : baseEnd_6717284 < baseStart_6717284 := by decide
  rcases family_descends (prefixWord ++ tailWord_6717284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6717391 : List Nat := [1, 1, 2, 1, 1, 5, 2, 5, 5]
def baseStart_6717391 : Nat := 118140960795 + 6717391 * 2 ^ 59
def prefixEnd_6717391 : Nat := 4983230072969 + 3 ^ 40 * 6717391 * 2
def baseEnd_6717391 : Nat := 383250036354025878946643

theorem tailTrace_6717391 : CollatzResearch.WordTrace tailWord_6717391 prefixEnd_6717391 383250036354025878946643 := by
  unfold tailWord_6717391
  simp only [CollatzResearch.WordTrace]
  refine ⟨245003377607047120891544027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163335585071364747261029351 245003377607047120891544027)
  ·
    refine ⟨367505066410570681337316041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245003377607047120891544027 367505066410570681337316041)
    ·
      refine ⟨275628799807928011002987031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 367505066410570681337316041 275628799807928011002987031)
      ·
        refine ⟨413443199711892016504480547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275628799807928011002987031 413443199711892016504480547)
        ·
          refine ⟨620164799567838024756720821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 413443199711892016504480547 620164799567838024756720821)
          ·
            refine ⟨58140449959484814820942577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 620164799567838024756720821 58140449959484814820942577)
            ·
              refine ⟨43605337469613611115706933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58140449959484814820942577 43605337469613611115706933)
              ·
                refine ⟨4088000387776276042097525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43605337469613611115706933 4088000387776276042097525)
                ·
                  refine ⟨383250036354025878946643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4088000387776276042097525 383250036354025878946643)
                  ·
                    rfl

theorem cell23_6717391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 5, 5].length) (baseStart_6717391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6717391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6717391 prefixEnd_6717391 := by exact prefixLift 6717391
  have htrace : WordTrace (prefixWord ++ tailWord_6717391) baseStart_6717391 baseEnd_6717391 := by
    simpa [prefixWord, tailWord_6717391, baseEnd_6717391] using wordTrace_append hprefix tailTrace_6717391
  have hstable : (prefixWord ++ tailWord_6717391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6717391).length < 2 ^ (prefixWord ++ tailWord_6717391).sum := by decide
  have hdescent : baseEnd_6717391 < baseStart_6717391 := by decide
  rcases family_descends (prefixWord ++ tailWord_6717391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6717402 : List Nat := [3, 1, 1, 2, 5, 1, 2, 2, 2, 2, 2]
def baseStart_6717402 : Nat := 118140960795 + 6717402 * 2 ^ 59
def prefixEnd_6717402 : Nat := 4983230072969 + 3 ^ 40 * 6717402 * 2
def baseEnd_6717402 : Nat := 3449255975473432367482237

theorem tailTrace_6717402 : CollatzResearch.WordTrace tailWord_6717402 prefixEnd_6717402 3449255975473432367482237 := by
  unfold tailWord_6717402
  simp only [CollatzResearch.WordTrace]
  refine ⟨61250944702501817442548615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163335852540004846513462973 61250944702501817442548615)
  ·
    refine ⟨91876417053752726163822923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61250944702501817442548615 91876417053752726163822923)
    ·
      refine ⟨137814625580629089245734385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91876417053752726163822923 137814625580629089245734385)
      ·
        refine ⟨103360969185471816934300789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137814625580629089245734385 103360969185471816934300789)
        ·
          refine ⟨9690090861137982837590699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 103360969185471816934300789 9690090861137982837590699)
          ·
            refine ⟨14535136291706974256386049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9690090861137982837590699 14535136291706974256386049)
            ·
              refine ⟨10901352218780230692289537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14535136291706974256386049 10901352218780230692289537)
              ·
                refine ⟨8176014164085173019217153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10901352218780230692289537 8176014164085173019217153)
                ·
                  refine ⟨6132010623063879764412865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8176014164085173019217153 6132010623063879764412865)
                  ·
                    refine ⟨4599007967297909823309649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6132010623063879764412865 4599007967297909823309649)
                    ·
                      refine ⟨3449255975473432367482237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4599007967297909823309649 3449255975473432367482237)
                      ·
                        rfl

theorem cell23_6717402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 2, 2, 2, 2, 2].length) (baseStart_6717402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6717402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6717402 prefixEnd_6717402 := by exact prefixLift 6717402
  have htrace : WordTrace (prefixWord ++ tailWord_6717402) baseStart_6717402 baseEnd_6717402 := by
    simpa [prefixWord, tailWord_6717402, baseEnd_6717402] using wordTrace_append hprefix tailTrace_6717402
  have hstable : (prefixWord ++ tailWord_6717402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6717402).length < 2 ^ (prefixWord ++ tailWord_6717402).sum := by decide
  have hdescent : baseEnd_6717402 < baseStart_6717402 := by decide
  rcases family_descends (prefixWord ++ tailWord_6717402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6717438 : List Nat := [4, 2, 2, 2, 1, 2, 1, 1, 1, 7]
def baseStart_6717438 : Nat := 118140960795 + 6717438 * 2 ^ 59
def prefixEnd_6717438 : Nat := 4983230072969 + 3 ^ 40 * 6717438 * 2
def baseEnd_6717438 : Nat := 1149758153592331408877357

theorem tailTrace_6717438 : CollatzResearch.WordTrace tailWord_6717438 prefixEnd_6717438 1149758153592331408877357 := by
  unfold tailWord_6717438
  simp only [CollatzResearch.WordTrace]
  refine ⟨30625636479734605989813121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 163336727891917898612336645 30625636479734605989813121)
  ·
    refine ⟨22969227359800954492359841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30625636479734605989813121 22969227359800954492359841)
    ·
      refine ⟨17226920519850715869269881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22969227359800954492359841 17226920519850715869269881)
      ·
        refine ⟨12920190389888036901952411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17226920519850715869269881 12920190389888036901952411)
        ·
          refine ⟨19380285584832055352928617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12920190389888036901952411 19380285584832055352928617)
          ·
            refine ⟨14535214188624041514696463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19380285584832055352928617 14535214188624041514696463)
            ·
              refine ⟨21802821282936062272044695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14535214188624041514696463 21802821282936062272044695)
              ·
                refine ⟨32704231924404093408067043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21802821282936062272044695 32704231924404093408067043)
                ·
                  refine ⟨49056347886606140112100565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32704231924404093408067043 49056347886606140112100565)
                  ·
                    refine ⟨1149758153592331408877357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49056347886606140112100565 1149758153592331408877357)
                    ·
                      rfl

theorem cell23_6717438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 1, 1, 7].length) (baseStart_6717438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6717438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6717438 prefixEnd_6717438 := by exact prefixLift 6717438
  have htrace : WordTrace (prefixWord ++ tailWord_6717438) baseStart_6717438 baseEnd_6717438 := by
    simpa [prefixWord, tailWord_6717438, baseEnd_6717438] using wordTrace_append hprefix tailTrace_6717438
  have hstable : (prefixWord ++ tailWord_6717438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6717438).length < 2 ^ (prefixWord ++ tailWord_6717438).sum := by decide
  have hdescent : baseEnd_6717438 < baseStart_6717438 := by decide
  rcases family_descends (prefixWord ++ tailWord_6717438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6717441 : List Nat := [1, 2, 4, 1, 2, 1, 3, 1, 1, 3, 4]
def baseStart_6717441 : Nat := 118140960795 + 6717441 * 2 ^ 59
def prefixEnd_6717441 : Nat := 4983230072969 + 3 ^ 40 * 6717441 * 2
def baseEnd_6717441 : Nat := 3449276001218957714894557

theorem tailTrace_6717441 : CollatzResearch.WordTrace tailWord_6717441 prefixEnd_6717441 3449276001218957714894557 := by
  unfold tailWord_6717441
  simp only [CollatzResearch.WordTrace]
  refine ⟨245005201256865979430864177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163336800837910652953909451 245005201256865979430864177)
  ·
    refine ⟨183753900942649484573148133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245005201256865979430864177 183753900942649484573148133)
    ·
      refine ⟨34453856426746778357465275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 183753900942649484573148133 34453856426746778357465275)
      ·
        refine ⟨51680784640120167536197913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34453856426746778357465275 51680784640120167536197913)
        ·
          refine ⟨38760588480090125652148435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51680784640120167536197913 38760588480090125652148435)
          ·
            refine ⟨58140882720135188478222653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38760588480090125652148435 58140882720135188478222653)
            ·
              refine ⟨21802831020050695679333495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58140882720135188478222653 21802831020050695679333495)
              ·
                refine ⟨32704246530076043519000243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21802831020050695679333495 32704246530076043519000243)
                ·
                  refine ⟨49056369795114065278500365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32704246530076043519000243 49056369795114065278500365)
                  ·
                    refine ⟨18396138673167774479437637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49056369795114065278500365 18396138673167774479437637)
                    ·
                      refine ⟨3449276001218957714894557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18396138673167774479437637 3449276001218957714894557)
                      ·
                        rfl

theorem cell23_6717441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 1, 1, 3, 4].length) (baseStart_6717441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6717441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6717441 prefixEnd_6717441 := by exact prefixLift 6717441
  have htrace : WordTrace (prefixWord ++ tailWord_6717441) baseStart_6717441 baseEnd_6717441 := by
    simpa [prefixWord, tailWord_6717441, baseEnd_6717441] using wordTrace_append hprefix tailTrace_6717441
  have hstable : (prefixWord ++ tailWord_6717441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6717441).length < 2 ^ (prefixWord ++ tailWord_6717441).sum := by decide
  have hdescent : baseEnd_6717441 < baseStart_6717441 := by decide
  rcases family_descends (prefixWord ++ tailWord_6717441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6717451 : List Nat := [1, 1, 1, 1, 6, 1, 1, 2, 5, 4]
def baseStart_6717451 : Nat := 118140960795 + 6717451 * 2 ^ 59
def prefixEnd_6717451 : Nat := 4983230072969 + 3 ^ 40 * 6717451 * 2
def baseEnd_6717451 : Nat := 1149760378675167558589837

theorem tailTrace_6717451 : CollatzResearch.WordTrace tailWord_6717451 prefixEnd_6717451 1149760378675167558589837 := by
  unfold tailWord_6717451
  simp only [CollatzResearch.WordTrace]
  refine ⟨245005565986829751138728207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163337043991219834092485471 245005565986829751138728207)
  ·
    refine ⟨367508348980244626708092311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245005565986829751138728207 367508348980244626708092311)
    ·
      refine ⟨551262523470366940062138467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 367508348980244626708092311 551262523470366940062138467)
      ·
        refine ⟨826893785205550410093207701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 551262523470366940062138467 826893785205550410093207701)
        ·
          refine ⟨38760646181510175473119111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 826893785205550410093207701 38760646181510175473119111)
          ·
            refine ⟨58140969272265263209678667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38760646181510175473119111 58140969272265263209678667)
            ·
              refine ⟨87211453908397894814518001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58140969272265263209678667 87211453908397894814518001)
              ·
                refine ⟨65408590431298421110888501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87211453908397894814518001 65408590431298421110888501)
                ·
                  refine ⟨6132055352934226979145797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 65408590431298421110888501 6132055352934226979145797)
                  ·
                    refine ⟨1149760378675167558589837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6132055352934226979145797 1149760378675167558589837)
                    ·
                      rfl

theorem cell23_6717451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 2, 5, 4].length) (baseStart_6717451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6717451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6717451 prefixEnd_6717451 := by exact prefixLift 6717451
  have htrace : WordTrace (prefixWord ++ tailWord_6717451) baseStart_6717451 baseEnd_6717451 := by
    simpa [prefixWord, tailWord_6717451, baseEnd_6717451] using wordTrace_append hprefix tailTrace_6717451
  have hstable : (prefixWord ++ tailWord_6717451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6717451).length < 2 ^ (prefixWord ++ tailWord_6717451).sum := by decide
  have hdescent : baseEnd_6717451 < baseStart_6717451 := by decide
  rcases family_descends (prefixWord ++ tailWord_6717451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6717453 : List Nat := [1, 7, 1, 2, 1, 2, 1, 2, 2, 2, 2]
def baseStart_6717453 : Nat := 118140960795 + 6717453 * 2 ^ 59
def prefixEnd_6717453 : Nat := 4983230072969 + 3 ^ 40 * 6717453 * 2
def baseEnd_6717453 : Nat := 3449282162986811667944503

theorem tailTrace_6717453 : CollatzResearch.WordTrace tailWord_6717453 prefixEnd_6717453 3449282162986811667944503 := by
  unfold tailWord_6717453
  simp only [CollatzResearch.WordTrace]
  refine ⟨245005638932822505480301013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163337092621881670320200675 245005638932822505480301013)
  ·
    refine ⟨5742319662488027472194555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 245005638932822505480301013 5742319662488027472194555)
    ·
      refine ⟨8613479493732041208291833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5742319662488027472194555 8613479493732041208291833)
      ·
        refine ⟨6460109620299030906218875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8613479493732041208291833 6460109620299030906218875)
        ·
          refine ⟨9690164430448546359328313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6460109620299030906218875 9690164430448546359328313)
          ·
            refine ⟨7267623322836409769496235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9690164430448546359328313 7267623322836409769496235)
            ·
              refine ⟨10901434984254614654244353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7267623322836409769496235 10901434984254614654244353)
              ·
                refine ⟨8176076238190960990683265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10901434984254614654244353 8176076238190960990683265)
                ·
                  refine ⟨6132057178643220743012449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8176076238190960990683265 6132057178643220743012449)
                  ·
                    refine ⟨4599042883982415557259337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6132057178643220743012449 4599042883982415557259337)
                    ·
                      refine ⟨3449282162986811667944503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4599042883982415557259337 3449282162986811667944503)
                      ·
                        rfl

theorem cell23_6717453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 1, 2, 2, 2, 2].length) (baseStart_6717453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6717453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6717453 prefixEnd_6717453 := by exact prefixLift 6717453
  have htrace : WordTrace (prefixWord ++ tailWord_6717453) baseStart_6717453 baseEnd_6717453 := by
    simpa [prefixWord, tailWord_6717453, baseEnd_6717453] using wordTrace_append hprefix tailTrace_6717453
  have hstable : (prefixWord ++ tailWord_6717453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6717453).length < 2 ^ (prefixWord ++ tailWord_6717453).sum := by decide
  have hdescent : baseEnd_6717453 < baseStart_6717453 := by decide
  rcases family_descends (prefixWord ++ tailWord_6717453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6717468 : List Nat := [2, 2, 3, 1, 3, 1, 1, 3, 3, 4]
def baseStart_6717468 : Nat := 118140960795 + 6717468 * 2 ^ 59
def prefixEnd_6717468 : Nat := 4983230072969 + 3 ^ 40 * 6717468 * 2
def baseEnd_6717468 : Nat := 1149763288398876369752311

theorem tailTrace_6717468 : CollatzResearch.WordTrace tailWord_6717468 prefixEnd_6717468 1149763288398876369752311 := by
  unfold tailWord_6717468
  simp only [CollatzResearch.WordTrace]
  refine ⟨122503093013884081521048529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163337457351845442028064705 122503093013884081521048529)
  ·
    refine ⟨91877319760413061140786397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122503093013884081521048529 91877319760413061140786397)
    ·
      refine ⟨34453994910154897927794899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91877319760413061140786397 34453994910154897927794899)
      ·
        refine ⟨51680992365232346891692349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34453994910154897927794899 51680992365232346891692349)
        ·
          refine ⟨19380372136962130084384631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51680992365232346891692349 19380372136962130084384631)
          ·
            refine ⟨29070558205443195126576947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19380372136962130084384631 29070558205443195126576947)
            ·
              refine ⟨43605837308164792689865421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29070558205443195126576947 43605837308164792689865421)
              ·
                refine ⟨16352188990561797258699533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43605837308164792689865421 16352188990561797258699533)
                ·
                  refine ⟨6132070871460673972012325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16352188990561797258699533 6132070871460673972012325)
                  ·
                    refine ⟨1149763288398876369752311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6132070871460673972012325 1149763288398876369752311)
                    ·
                      rfl

theorem cell23_6717468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 3, 3, 4].length) (baseStart_6717468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6717468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6717468 prefixEnd_6717468 := by exact prefixLift 6717468
  have htrace : WordTrace (prefixWord ++ tailWord_6717468) baseStart_6717468 baseEnd_6717468 := by
    simpa [prefixWord, tailWord_6717468, baseEnd_6717468] using wordTrace_append hprefix tailTrace_6717468
  have hstable : (prefixWord ++ tailWord_6717468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6717468).length < 2 ^ (prefixWord ++ tailWord_6717468).sum := by decide
  have hdescent : baseEnd_6717468 < baseStart_6717468 := by decide
  rcases family_descends (prefixWord ++ tailWord_6717468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6717525 : List Nat := [1, 3, 2, 2, 1, 3, 3, 1, 3, 1, 3]
def baseStart_6717525 : Nat := 118140960795 + 6717525 * 2 ^ 59
def prefixEnd_6717525 : Nat := 4983230072969 + 3 ^ 40 * 6717525 * 2
def baseEnd_6717525 : Nat := 3449319133593935386244171

theorem tailTrace_6717525 : CollatzResearch.WordTrace tailWord_6717525 prefixEnd_6717525 3449319133593935386244171 := by
  unfold tailWord_6717525
  simp only [CollatzResearch.WordTrace]
  refine ⟨245008264988561661776922029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163338843325707774517948019 245008264988561661776922029)
  ·
    refine ⟨91878099370710623166345761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 245008264988561661776922029 91878099370710623166345761)
    ·
      refine ⟨68908574528032967374759321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91878099370710623166345761 68908574528032967374759321)
      ·
        refine ⟨51681430896024725531069491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68908574528032967374759321 51681430896024725531069491)
        ·
          refine ⟨77522146344037088296604237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51681430896024725531069491 77522146344037088296604237)
          ·
            refine ⟨29070804879013908111226589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77522146344037088296604237 29070804879013908111226589)
            ·
              refine ⟨10901551829630215541709971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29070804879013908111226589 10901551829630215541709971)
              ·
                refine ⟨16352327744445323312564957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10901551829630215541709971 16352327744445323312564957)
                ·
                  refine ⟨6132122904166996242211859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16352327744445323312564957 6132122904166996242211859)
                  ·
                    refine ⟨9198184356250494363317789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6132122904166996242211859 9198184356250494363317789)
                    ·
                      refine ⟨3449319133593935386244171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9198184356250494363317789 3449319133593935386244171)
                      ·
                        rfl

theorem cell23_6717525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 3, 1, 3, 1, 3].length) (baseStart_6717525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6717525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6717525 prefixEnd_6717525 := by exact prefixLift 6717525
  have htrace : WordTrace (prefixWord ++ tailWord_6717525) baseStart_6717525 baseEnd_6717525 := by
    simpa [prefixWord, tailWord_6717525, baseEnd_6717525] using wordTrace_append hprefix tailTrace_6717525
  have hstable : (prefixWord ++ tailWord_6717525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6717525).length < 2 ^ (prefixWord ++ tailWord_6717525).sum := by decide
  have hdescent : baseEnd_6717525 < baseStart_6717525 := by decide
  rcases family_descends (prefixWord ++ tailWord_6717525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6717548 : List Nat := [2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 4]
def baseStart_6717548 : Nat := 118140960795 + 6717548 * 2 ^ 59
def prefixEnd_6717548 : Nat := 4983230072969 + 3 ^ 40 * 6717548 * 2
def baseEnd_6717548 : Nat := 3449330943648988796256565

theorem tailTrace_6717548 : CollatzResearch.WordTrace tailWord_6717548 prefixEnd_6717548 3449330943648988796256565 := by
  unfold tailWord_6717548
  simp only [CollatzResearch.WordTrace]
  refine ⟨122504551933739168352504649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163339402578318891136672865 122504551933739168352504649)
  ·
    refine ⟨91878413950304376264378487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122504551933739168352504649 91878413950304376264378487)
    ·
      refine ⟨137817620925456564396567731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91878413950304376264378487 137817620925456564396567731)
      ·
        refine ⟨206726431388184846594851597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137817620925456564396567731 206726431388184846594851597)
        ·
          refine ⟨77522411770569317473069349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 206726431388184846594851597 77522411770569317473069349)
          ·
            refine ⟨14535452206981747026200503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 77522411770569317473069349 14535452206981747026200503)
            ·
              refine ⟨21803178310472620539300755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14535452206981747026200503 21803178310472620539300755)
              ·
                refine ⟨32704767465708930808951133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21803178310472620539300755 32704767465708930808951133)
                ·
                  refine ⟨12264287799640849053356675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32704767465708930808951133 12264287799640849053356675)
                  ·
                    refine ⟨18396431699461273580035013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12264287799640849053356675 18396431699461273580035013)
                    ·
                      refine ⟨3449330943648988796256565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18396431699461273580035013 3449330943648988796256565)
                      ·
                        rfl

theorem cell23_6717548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 4].length) (baseStart_6717548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6717548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6717548 prefixEnd_6717548 := by exact prefixLift 6717548
  have htrace : WordTrace (prefixWord ++ tailWord_6717548) baseStart_6717548 baseEnd_6717548 := by
    simpa [prefixWord, tailWord_6717548, baseEnd_6717548] using wordTrace_append hprefix tailTrace_6717548
  have hstable : (prefixWord ++ tailWord_6717548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6717548).length < 2 ^ (prefixWord ++ tailWord_6717548).sum := by decide
  have hdescent : baseEnd_6717548 < baseStart_6717548 := by decide
  rcases family_descends (prefixWord ++ tailWord_6717548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6717558 : List Nat := [5, 1, 1, 2, 1, 2, 1, 1, 3, 6]
def baseStart_6717558 : Nat := 118140960795 + 6717558 * 2 ^ 59
def prefixEnd_6717558 : Nat := 4983230072969 + 3 ^ 40 * 6717558 * 2
def baseEnd_6717558 : Nat := 1149778692818511252377173

theorem tailTrace_6717558 : CollatzResearch.WordTrace tailWord_6717558 prefixEnd_6717558 1149778692818511252377173 := by
  unfold tailWord_6717558
  simp only [CollatzResearch.WordTrace]
  refine ⟨15313091787340131775804583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 163339645731628072275248885 15313091787340131775804583)
  ·
    refine ⟨22969637681010197663706875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15313091787340131775804583 22969637681010197663706875)
    ·
      refine ⟨34454456521515296495560313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22969637681010197663706875 34454456521515296495560313)
      ·
        refine ⟨25840842391136472371670235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34454456521515296495560313 25840842391136472371670235)
        ·
          refine ⟨38761263586704708557505353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25840842391136472371670235 38761263586704708557505353)
          ·
            refine ⟨29070947690028531418129015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38761263586704708557505353 29070947690028531418129015)
            ·
              refine ⟨43606421535042797127193523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29070947690028531418129015 43606421535042797127193523)
              ·
                refine ⟨65409632302564195690790285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43606421535042797127193523 65409632302564195690790285)
                ·
                  refine ⟨24528612113461573384046357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65409632302564195690790285 24528612113461573384046357)
                  ·
                    refine ⟨1149778692818511252377173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24528612113461573384046357 1149778692818511252377173)
                    ·
                      rfl

theorem cell23_6717558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 1, 3, 6].length) (baseStart_6717558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6717558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6717558 prefixEnd_6717558 := by exact prefixLift 6717558
  have htrace : WordTrace (prefixWord ++ tailWord_6717558) baseStart_6717558 baseEnd_6717558 := by
    simpa [prefixWord, tailWord_6717558, baseEnd_6717558] using wordTrace_append hprefix tailTrace_6717558
  have hstable : (prefixWord ++ tailWord_6717558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6717558).length < 2 ^ (prefixWord ++ tailWord_6717558).sum := by decide
  have hdescent : baseEnd_6717558 < baseStart_6717558 := by decide
  rcases family_descends (prefixWord ++ tailWord_6717558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6717576 : List Nat := [2, 1, 3, 4, 1, 3, 2, 2, 1, 1, 3]
def baseStart_6717576 : Nat := 118140960795 + 6717576 * 2 ^ 59
def prefixEnd_6717576 : Nat := 4983230072969 + 3 ^ 40 * 6717576 * 2
def baseEnd_6717576 : Nat := 3449345321107314686706437

theorem tailTrace_6717576 : CollatzResearch.WordTrace tailWord_6717576 prefixEnd_6717576 3449345321107314686706437 := by
  unfold tailWord_6717576
  simp only [CollatzResearch.WordTrace]
  refine ⟨122505062555688448743514291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163340083407584598324685721 122505062555688448743514291)
  ·
    refine ⟨183757593833532673115271437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122505062555688448743514291 183757593833532673115271437)
    ·
      refine ⟨68909097687574752418226789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 183757593833532673115271437 68909097687574752418226789)
      ·
        refine ⟨12920455816420266078417523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68909097687574752418226789 12920455816420266078417523)
        ·
          refine ⟨19380683724630399117626285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12920455816420266078417523 19380683724630399117626285)
          ·
            refine ⟨7267756396736399669109857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19380683724630399117626285 7267756396736399669109857)
            ·
              refine ⟨5450817297552299751832393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7267756396736399669109857 5450817297552299751832393)
              ·
                refine ⟨4088112973164224813874295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5450817297552299751832393 4088112973164224813874295)
                ·
                  refine ⟨6132169459746337220811443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4088112973164224813874295 6132169459746337220811443)
                  ·
                    refine ⟨9198254189619505831217165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6132169459746337220811443 9198254189619505831217165)
                    ·
                      refine ⟨3449345321107314686706437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9198254189619505831217165 3449345321107314686706437)
                      ·
                        rfl

theorem cell23_6717576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 2, 2, 1, 1, 3].length) (baseStart_6717576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6717576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6717576 prefixEnd_6717576 := by exact prefixLift 6717576
  have htrace : WordTrace (prefixWord ++ tailWord_6717576) baseStart_6717576 baseEnd_6717576 := by
    simpa [prefixWord, tailWord_6717576, baseEnd_6717576] using wordTrace_append hprefix tailTrace_6717576
  have hstable : (prefixWord ++ tailWord_6717576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6717576).length < 2 ^ (prefixWord ++ tailWord_6717576).sum := by decide
  have hdescent : baseEnd_6717576 < baseStart_6717576 := by decide
  rcases family_descends (prefixWord ++ tailWord_6717576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6717632 : List Nat := [2, 1, 1, 2, 5, 1, 3, 2, 2, 1, 3]
def baseStart_6717632 : Nat := 118140960795 + 6717632 * 2 ^ 59
def prefixEnd_6717632 : Nat := 4983230072969 + 3 ^ 40 * 6717632 * 2
def baseEnd_6717632 : Nat := 3449374076023966467606179

theorem tailTrace_6717632 : CollatzResearch.WordTrace tailWord_6717632 prefixEnd_6717632 3449374076023966467606179 := by
  unfold tailWord_6717632
  simp only [CollatzResearch.WordTrace]
  refine ⟨122506083799587009525533575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163341445066116012700711433 122506083799587009525533575)
  ·
    refine ⟨183759125699380514288300363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122506083799587009525533575 183759125699380514288300363)
    ·
      refine ⟨275638688549070771432450545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183759125699380514288300363 275638688549070771432450545)
      ·
        refine ⟨206729016411803078574337909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 275638688549070771432450545 206729016411803078574337909)
        ·
          refine ⟨19380845288606538616344179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 206729016411803078574337909 19380845288606538616344179)
          ·
            refine ⟨29071267932909807924516269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19380845288606538616344179 29071267932909807924516269)
            ·
              refine ⟨10901725474841177971693601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29071267932909807924516269 10901725474841177971693601)
              ·
                refine ⟨8176294106130883478770201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10901725474841177971693601 8176294106130883478770201)
                ·
                  refine ⟨6132220579598162609077651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8176294106130883478770201 6132220579598162609077651)
                  ·
                    refine ⟨9198330869397243913616477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6132220579598162609077651 9198330869397243913616477)
                    ·
                      refine ⟨3449374076023966467606179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9198330869397243913616477 3449374076023966467606179)
                      ·
                        rfl

theorem cell23_6717632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 3, 2, 2, 1, 3].length) (baseStart_6717632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6717632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6717632 prefixEnd_6717632 := by exact prefixLift 6717632
  have htrace : WordTrace (prefixWord ++ tailWord_6717632) baseStart_6717632 baseEnd_6717632 := by
    simpa [prefixWord, tailWord_6717632, baseEnd_6717632] using wordTrace_append hprefix tailTrace_6717632
  have hstable : (prefixWord ++ tailWord_6717632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6717632).length < 2 ^ (prefixWord ++ tailWord_6717632).sum := by decide
  have hdescent : baseEnd_6717632 < baseStart_6717632 := by decide
  rcases family_descends (prefixWord ++ tailWord_6717632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6717641 : List Nat := [1, 2, 1, 1, 2, 1, 1, 3, 3, 3, 5]
def baseStart_6717641 : Nat := 118140960795 + 6717641 * 2 ^ 59
def prefixEnd_6717641 : Nat := 4983230072969 + 3 ^ 40 * 6717641 * 2
def baseEnd_6717641 : Nat := 3449378697349856932393637

theorem tailTrace_6717641 : CollatzResearch.WordTrace tailWord_6717641 prefixEnd_6717641 3449378697349856932393637 := by
  unfold tailWord_6717641
  simp only [CollatzResearch.WordTrace]
  refine ⟨245012495856141413588144777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163341663904094275725429851 245012495856141413588144777)
  ·
    refine ⟨183759371892106060191108583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245012495856141413588144777 183759371892106060191108583)
    ·
      refine ⟨275639057838159090286662875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183759371892106060191108583 275639057838159090286662875)
      ·
        refine ⟨413458586757238635429994313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275639057838159090286662875 413458586757238635429994313)
        ·
          refine ⟨310093940067928976572495735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 413458586757238635429994313 310093940067928976572495735)
          ·
            refine ⟨465140910101893464858743603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 310093940067928976572495735 465140910101893464858743603)
            ·
              refine ⟨697711365152840197288115405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 465140910101893464858743603 697711365152840197288115405)
              ·
                refine ⟨261641761932315073983043277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 697711365152840197288115405 261641761932315073983043277)
                ·
                  refine ⟨98115660724618152743641229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 261641761932315073983043277 98115660724618152743641229)
                  ·
                    refine ⟨36793372771731807278865461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 98115660724618152743641229 36793372771731807278865461)
                    ·
                      refine ⟨3449378697349856932393637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36793372771731807278865461 3449378697349856932393637)
                      ·
                        rfl

theorem cell23_6717641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 3, 3, 3, 5].length) (baseStart_6717641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6717641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6717641 prefixEnd_6717641 := by exact prefixLift 6717641
  have htrace : WordTrace (prefixWord ++ tailWord_6717641) baseStart_6717641 baseEnd_6717641 := by
    simpa [prefixWord, tailWord_6717641, baseEnd_6717641] using wordTrace_append hprefix tailTrace_6717641
  have hstable : (prefixWord ++ tailWord_6717641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6717641).length < 2 ^ (prefixWord ++ tailWord_6717641).sum := by decide
  have hdescent : baseEnd_6717641 < baseStart_6717641 := by decide
  rcases family_descends (prefixWord ++ tailWord_6717641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6717658 : List Nat := [3, 1, 1, 2, 2, 1, 2, 2, 2, 4, 3]
def baseStart_6717658 : Nat := 118140960795 + 6717658 * 2 ^ 59
def prefixEnd_6717658 : Nat := 4983230072969 + 3 ^ 40 * 6717658 * 2
def baseEnd_6717658 : Nat := 3449387426520983365881059

theorem tailTrace_6717658 : CollatzResearch.WordTrace tailWord_6717658 prefixEnd_6717658 3449387426520983365881059 := by
  unfold tailWord_6717658
  simp only [CollatzResearch.WordTrace]
  refine ⟨61253278974269956372878407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163342077264719883661009085 61253278974269956372878407)
  ·
    refine ⟨91879918461404934559317611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61253278974269956372878407 91879918461404934559317611)
    ·
      refine ⟨137819877692107401838976417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91879918461404934559317611 137819877692107401838976417)
      ·
        refine ⟨103364908269080551379232313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137819877692107401838976417 103364908269080551379232313)
        ·
          refine ⟨77523681201810413534424235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103364908269080551379232313 77523681201810413534424235)
          ·
            refine ⟨116285521802715620301636353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77523681201810413534424235 116285521802715620301636353)
            ·
              refine ⟨87214141352036715226227265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116285521802715620301636353 87214141352036715226227265)
              ·
                refine ⟨65410606014027536419670449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87214141352036715226227265 65410606014027536419670449)
                ·
                  refine ⟨49057954510520652314752837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65410606014027536419670449 49057954510520652314752837)
                  ·
                    refine ⟨9198366470722622309016157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 49057954510520652314752837 9198366470722622309016157)
                    ·
                      refine ⟨3449387426520983365881059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9198366470722622309016157 3449387426520983365881059)
                      ·
                        rfl

theorem cell23_6717658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 2, 2, 4, 3].length) (baseStart_6717658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6717658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6717658 prefixEnd_6717658 := by exact prefixLift 6717658
  have htrace : WordTrace (prefixWord ++ tailWord_6717658) baseStart_6717658 baseEnd_6717658 := by
    simpa [prefixWord, tailWord_6717658, baseEnd_6717658] using wordTrace_append hprefix tailTrace_6717658
  have hstable : (prefixWord ++ tailWord_6717658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6717658).length < 2 ^ (prefixWord ++ tailWord_6717658).sum := by decide
  have hdescent : baseEnd_6717658 < baseStart_6717658 := by decide
  rcases family_descends (prefixWord ++ tailWord_6717658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6717672 : List Nat := [2, 1, 4, 1, 2, 2, 1, 2, 4, 2, 2]
def baseStart_6717672 : Nat := 118140960795 + 6717672 * 2 ^ 59
def prefixEnd_6717672 : Nat := 4983230072969 + 3 ^ 40 * 6717672 * 2
def baseEnd_6717672 : Nat := 3449394615250146311105995

theorem tailTrace_6717672 : CollatzResearch.WordTrace tailWord_6717672 prefixEnd_6717672 3449394615250146311105995 := by
  unfold tailWord_6717672
  simp only [CollatzResearch.WordTrace]
  refine ⟨122506813259514552941261635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163342417679352737255015513 122506813259514552941261635)
  ·
    refine ⟨183760219889271829411892453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122506813259514552941261635 183760219889271829411892453)
    ·
      refine ⟨34455041229238468014729835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 183760219889271829411892453 34455041229238468014729835)
      ·
        refine ⟨51682561843857702022094753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34455041229238468014729835 51682561843857702022094753)
        ·
          refine ⟨38761921382893276516571065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51682561843857702022094753 38761921382893276516571065)
          ·
            refine ⟨29071441037169957387428299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38761921382893276516571065 29071441037169957387428299)
            ·
              refine ⟨43607161555754936081142449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29071441037169957387428299 43607161555754936081142449)
              ·
                refine ⟨32705371166816202060856837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43607161555754936081142449 32705371166816202060856837)
                ·
                  refine ⟨6132257093778037886410657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32705371166816202060856837 6132257093778037886410657)
                  ·
                    refine ⟨4599192820333528414807993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6132257093778037886410657 4599192820333528414807993)
                    ·
                      refine ⟨3449394615250146311105995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4599192820333528414807993 3449394615250146311105995)
                      ·
                        rfl

theorem cell23_6717672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 2, 4, 2, 2].length) (baseStart_6717672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6717672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6717672 prefixEnd_6717672 := by exact prefixLift 6717672
  have htrace : WordTrace (prefixWord ++ tailWord_6717672) baseStart_6717672 baseEnd_6717672 := by
    simpa [prefixWord, tailWord_6717672, baseEnd_6717672] using wordTrace_append hprefix tailTrace_6717672
  have hstable : (prefixWord ++ tailWord_6717672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6717672).length < 2 ^ (prefixWord ++ tailWord_6717672).sum := by decide
  have hdescent : baseEnd_6717672 < baseStart_6717672 := by decide
  rcases family_descends (prefixWord ++ tailWord_6717672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6717688 : List Nat := [2, 1, 2, 1, 1, 2, 1, 3, 4, 3, 3]
def baseStart_6717688 : Nat := 118140960795 + 6717688 * 2 ^ 59
def prefixEnd_6717688 : Nat := 4983230072969 + 3 ^ 40 * 6717688 * 2
def baseEnd_6717688 : Nat := 3449402830940618248505921

theorem tailTrace_6717688 : CollatzResearch.WordTrace tailWord_6717688 prefixEnd_6717688 3449402830940618248505921 := by
  unfold tailWord_6717688
  simp only [CollatzResearch.WordTrace]
  refine ⟨122507105043485570307552859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163342806724647427076737145 122507105043485570307552859)
  ·
    refine ⟨183760657565228355461329289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122507105043485570307552859 183760657565228355461329289)
    ·
      refine ⟨137820493173921266595996967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183760657565228355461329289 137820493173921266595996967)
      ·
        refine ⟨206730739760881899893995451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137820493173921266595996967 206730739760881899893995451)
        ·
          refine ⟨310096109641322849840993177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206730739760881899893995451 310096109641322849840993177)
          ·
            refine ⟨232572082230992137380744883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 310096109641322849840993177 232572082230992137380744883)
            ·
              refine ⟨348858123346488206071117325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 232572082230992137380744883 348858123346488206071117325)
              ·
                refine ⟨130821796254933077276668997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 348858123346488206071117325 130821796254933077276668997)
                ·
                  refine ⟨24529086797799951989375437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 130821796254933077276668997 24529086797799951989375437)
                  ·
                    refine ⟨9198407549174981996015789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24529086797799951989375437 9198407549174981996015789)
                    ·
                      refine ⟨3449402830940618248505921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9198407549174981996015789 3449402830940618248505921)
                      ·
                        rfl

theorem cell23_6717688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 3, 4, 3, 3].length) (baseStart_6717688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6717688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6717688 prefixEnd_6717688 := by exact prefixLift 6717688
  have htrace : WordTrace (prefixWord ++ tailWord_6717688) baseStart_6717688 baseEnd_6717688 := by
    simpa [prefixWord, tailWord_6717688, baseEnd_6717688] using wordTrace_append hprefix tailTrace_6717688
  have hstable : (prefixWord ++ tailWord_6717688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6717688).length < 2 ^ (prefixWord ++ tailWord_6717688).sum := by decide
  have hdescent : baseEnd_6717688 < baseStart_6717688 := by decide
  rcases family_descends (prefixWord ++ tailWord_6717688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6717691 : List Nat := [1, 1, 1, 1, 1, 3, 1, 1, 2, 11]
def baseStart_6717691 : Nat := 118140960795 + 6717691 * 2 ^ 59
def prefixEnd_6717691 : Nat := 4983230072969 + 3 ^ 40 * 6717691 * 2
def baseEnd_6717691 : Nat := 1149801457127527245589469

theorem tailTrace_6717691 : CollatzResearch.WordTrace tailWord_6717691 prefixEnd_6717691 1149801457127527245589469 := by
  unfold tailWord_6717691
  simp only [CollatzResearch.WordTrace]
  refine ⟨245014319505960272127464927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163342879670640181418309951 245014319505960272127464927)
  ·
    refine ⟨367521479258940408191197391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245014319505960272127464927 367521479258940408191197391)
    ·
      refine ⟨551282218888410612286796087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 367521479258940408191197391 551282218888410612286796087)
      ·
        refine ⟨826923328332615918430194131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 551282218888410612286796087 826923328332615918430194131)
        ·
          refine ⟨1240384992498923877645291197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 826923328332615918430194131 1240384992498923877645291197)
          ·
            refine ⟨465144372187096454116984199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1240384992498923877645291197 465144372187096454116984199)
            ·
              refine ⟨697716558280644681175476299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 465144372187096454116984199 697716558280644681175476299)
              ·
                refine ⟨1046574837420967021763214449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 697716558280644681175476299 1046574837420967021763214449)
                ·
                  refine ⟨784931128065725266322410837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1046574837420967021763214449 784931128065725266322410837)
                  ·
                    refine ⟨1149801457127527245589469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 784931128065725266322410837 1149801457127527245589469)
                    ·
                      rfl

theorem cell23_6717691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 11].length) (baseStart_6717691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6717691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6717691 prefixEnd_6717691 := by exact prefixLift 6717691
  have htrace : WordTrace (prefixWord ++ tailWord_6717691) baseStart_6717691 baseEnd_6717691 := by
    simpa [prefixWord, tailWord_6717691, baseEnd_6717691] using wordTrace_append hprefix tailTrace_6717691
  have hstable : (prefixWord ++ tailWord_6717691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6717691).length < 2 ^ (prefixWord ++ tailWord_6717691).sum := by decide
  have hdescent : baseEnd_6717691 < baseStart_6717691 := by decide
  rcases family_descends (prefixWord ++ tailWord_6717691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6717708 : List Nat := [2, 2, 1, 2, 2, 2, 1, 2, 4, 5]
def baseStart_6717708 : Nat := 118140960795 + 6717708 * 2 ^ 59
def prefixEnd_6717708 : Nat := 4983230072969 + 3 ^ 40 * 6717708 * 2
def baseEnd_6717708 : Nat := 1149804366851236056751943

theorem tailTrace_6717708 : CollatzResearch.WordTrace tailWord_6717708 prefixEnd_6717708 1149804366851236056751943 := by
  unfold tailWord_6717708
  simp only [CollatzResearch.WordTrace]
  refine ⟨122507469773449342015416889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163343293031265789353889185 122507469773449342015416889)
  ·
    refine ⟨91880602330087006511562667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122507469773449342015416889 91880602330087006511562667)
    ·
      refine ⟨137820903495130509767344001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91880602330087006511562667 137820903495130509767344001)
      ·
        refine ⟨103365677621347882325508001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137820903495130509767344001 103365677621347882325508001)
        ·
          refine ⟨77524258216010911744131001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103365677621347882325508001 77524258216010911744131001)
          ·
            refine ⟨58143193662008183808098251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77524258216010911744131001 58143193662008183808098251)
            ·
              refine ⟨87214790493012275712147377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58143193662008183808098251 87214790493012275712147377)
              ·
                refine ⟨65411092869759206784110533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87214790493012275712147377 65411092869759206784110533)
                ·
                  refine ⟨12264579913079851272020725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65411092869759206784110533 12264579913079851272020725)
                  ·
                    refine ⟨1149804366851236056751943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12264579913079851272020725 1149804366851236056751943)
                    ·
                      rfl

theorem cell23_6717708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 2, 4, 5].length) (baseStart_6717708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6717708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6717708 prefixEnd_6717708 := by exact prefixLift 6717708
  have htrace : WordTrace (prefixWord ++ tailWord_6717708) baseStart_6717708 baseEnd_6717708 := by
    simpa [prefixWord, tailWord_6717708, baseEnd_6717708] using wordTrace_append hprefix tailTrace_6717708
  have hstable : (prefixWord ++ tailWord_6717708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6717708).length < 2 ^ (prefixWord ++ tailWord_6717708).sum := by decide
  have hdescent : baseEnd_6717708 < baseStart_6717708 := by decide
  rcases family_descends (prefixWord ++ tailWord_6717708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6717746 : List Nat := [3, 2, 1, 1, 6, 1, 2, 2, 5]
def baseStart_6717746 : Nat := 118140960795 + 6717746 * 2 ^ 59
def prefixEnd_6717746 : Nat := 4983230072969 + 3 ^ 40 * 6717746 * 2
def baseEnd_6717746 : Nat := 383270290313175446842295

theorem tailTrace_6717746 : CollatzResearch.WordTrace tailWord_6717746 prefixEnd_6717746 383270290313175446842295 := by
  unfold tailWord_6717746
  simp only [CollatzResearch.WordTrace]
  refine ⟨61254081380190254130179273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163344217013840677680478061 61254081380190254130179273)
  ·
    refine ⟨45940561035142690597634455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61254081380190254130179273 45940561035142690597634455)
    ·
      refine ⟨68910841552714035896451683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45940561035142690597634455 68910841552714035896451683)
      ·
        refine ⟨103366262329071053844677525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68910841552714035896451683 103366262329071053844677525)
        ·
          refine ⟨4845293546675205648969259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 103366262329071053844677525 4845293546675205648969259)
          ·
            refine ⟨7267940320012808473453889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4845293546675205648969259 7267940320012808473453889)
            ·
              refine ⟨5450955240009606355090417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7267940320012808473453889 5450955240009606355090417)
              ·
                refine ⟨4088216430007204766317813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5450955240009606355090417 4088216430007204766317813)
                ·
                  refine ⟨383270290313175446842295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4088216430007204766317813 383270290313175446842295)
                  ·
                    rfl

theorem cell23_6717746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 2, 2, 5].length) (baseStart_6717746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6717746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6717746 prefixEnd_6717746 := by exact prefixLift 6717746
  have htrace : WordTrace (prefixWord ++ tailWord_6717746) baseStart_6717746 baseEnd_6717746 := by
    simpa [prefixWord, tailWord_6717746, baseEnd_6717746] using wordTrace_append hprefix tailTrace_6717746
  have hstable : (prefixWord ++ tailWord_6717746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6717746).length < 2 ^ (prefixWord ++ tailWord_6717746).sum := by decide
  have hdescent : baseEnd_6717746 < baseStart_6717746 := by decide
  rcases family_descends (prefixWord ++ tailWord_6717746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6717802 : List Nat := [3, 1, 3, 3, 1, 1, 3, 2, 6]
def baseStart_6717802 : Nat := 118140960795 + 6717802 * 2 ^ 59
def prefixEnd_6717802 : Nat := 4983230072969 + 3 ^ 40 * 6717802 * 2
def baseEnd_6717802 : Nat := 383273485303914533608933

theorem tailTrace_6717802 : CollatzResearch.WordTrace tailWord_6717802 prefixEnd_6717802 383273485303914533608933 := by
  unfold tailWord_6717802
  simp only [CollatzResearch.WordTrace]
  refine ⟨61254592002139534521188915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163345578672372092056503773 61254592002139534521188915)
  ·
    refine ⟨91881888003209301781783373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61254592002139534521188915 91881888003209301781783373)
    ·
      refine ⟨34455708001203488168168765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91881888003209301781783373 34455708001203488168168765)
      ·
        refine ⟨12920890500451308063063287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34455708001203488168168765 12920890500451308063063287)
        ·
          refine ⟨19381335750676962094594931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12920890500451308063063287 19381335750676962094594931)
          ·
            refine ⟨29072003626015443141892397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19381335750676962094594931 29072003626015443141892397)
            ·
              refine ⟨10902001359755791178209649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29072003626015443141892397 10902001359755791178209649)
              ·
                refine ⟨8176501019816843383657237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10902001359755791178209649 8176501019816843383657237)
                ·
                  refine ⟨383273485303914533608933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8176501019816843383657237 383273485303914533608933)
                  ·
                    rfl

theorem cell23_6717802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 3, 2, 6].length) (baseStart_6717802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6717802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6717802 prefixEnd_6717802 := by exact prefixLift 6717802
  have htrace : WordTrace (prefixWord ++ tailWord_6717802) baseStart_6717802 baseEnd_6717802 := by
    simpa [prefixWord, tailWord_6717802, baseEnd_6717802] using wordTrace_append hprefix tailTrace_6717802
  have hstable : (prefixWord ++ tailWord_6717802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6717802).length < 2 ^ (prefixWord ++ tailWord_6717802).sum := by decide
  have hdescent : baseEnd_6717802 < baseStart_6717802 := by decide
  rcases family_descends (prefixWord ++ tailWord_6717802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6717832 : List Nat := [2, 1, 3, 3, 1, 1, 4, 2, 1, 5]
def baseStart_6717832 : Nat := 118140960795 + 6717832 * 2 ^ 59
def prefixEnd_6717832 : Nat := 4983230072969 + 3 ^ 40 * 6717832 * 2
def baseEnd_6717832 : Nat := 1149825590718288561701753

theorem tailTrace_6717832 : CollatzResearch.WordTrace tailWord_6717832 prefixEnd_6717832 1149825590718288561701753 := by
  unfold tailWord_6717832
  simp only [CollatzResearch.WordTrace]
  refine ⟨122509731099224726604173875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163346308132299635472231833 122509731099224726604173875)
  ·
    refine ⟨183764596648837089906260813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122509731099224726604173875 183764596648837089906260813)
    ·
      refine ⟨68911723743313908714847805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 183764596648837089906260813 68911723743313908714847805)
      ·
        refine ⟨25841896403742715768067927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68911723743313908714847805 25841896403742715768067927)
        ·
          refine ⟨38762844605614073652101891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25841896403742715768067927 38762844605614073652101891)
          ·
            refine ⟨58144266908421110478152837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38762844605614073652101891 58144266908421110478152837)
            ·
              refine ⟨10902050045328958214653657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58144266908421110478152837 10902050045328958214653657)
              ·
                refine ⟨8176537533996718660990243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10902050045328958214653657 8176537533996718660990243)
                ·
                  refine ⟨12264806300995077991485365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8176537533996718660990243 12264806300995077991485365)
                  ·
                    refine ⟨1149825590718288561701753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12264806300995077991485365 1149825590718288561701753)
                    ·
                      rfl

theorem cell23_6717832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 4, 2, 1, 5].length) (baseStart_6717832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6717832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6717832 prefixEnd_6717832 := by exact prefixLift 6717832
  have htrace : WordTrace (prefixWord ++ tailWord_6717832) baseStart_6717832 baseEnd_6717832 := by
    simpa [prefixWord, tailWord_6717832, baseEnd_6717832] using wordTrace_append hprefix tailTrace_6717832
  have hstable : (prefixWord ++ tailWord_6717832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6717832).length < 2 ^ (prefixWord ++ tailWord_6717832).sum := by decide
  have hdescent : baseEnd_6717832 < baseStart_6717832 := by decide
  rcases family_descends (prefixWord ++ tailWord_6717832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6717863 : List Nat := [1, 1, 6, 1, 1, 3, 3, 2, 1, 1, 3]
def baseStart_6717863 : Nat := 118140960795 + 6717863 * 2 ^ 59
def prefixEnd_6717863 : Nat := 4983230072969 + 3 ^ 40 * 6717863 * 2
def baseEnd_6717863 : Nat := 3449492690055155063817617

theorem tailTrace_6717863 : CollatzResearch.WordTrace tailWord_6717863 prefixEnd_6717863 3449492690055155063817617 := by
  unfold tailWord_6717863
  simp only [CollatzResearch.WordTrace]
  refine ⟨245020592861337145502726243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163347061907558097001817495 245020592861337145502726243)
  ·
    refine ⟨367530889292005718254089365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245020592861337145502726243 367530889292005718254089365)
    ·
      refine ⟨17228010435562768043160439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 367530889292005718254089365 17228010435562768043160439)
      ·
        refine ⟨25842015653344152064740659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17228010435562768043160439 25842015653344152064740659)
        ·
          refine ⟨38763023480016228097110989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25842015653344152064740659 38763023480016228097110989)
          ·
            refine ⟨14536133805006085536416621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38763023480016228097110989 14536133805006085536416621)
            ·
              refine ⟨5451050176877282076156233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14536133805006085536416621 5451050176877282076156233)
              ·
                refine ⟨4088287632657961557117175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5451050176877282076156233 4088287632657961557117175)
                ·
                  refine ⟨6132431448986942335675763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4088287632657961557117175 6132431448986942335675763)
                  ·
                    refine ⟨9198647173480413503513645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6132431448986942335675763 9198647173480413503513645)
                    ·
                      refine ⟨3449492690055155063817617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9198647173480413503513645 3449492690055155063817617)
                      ·
                        rfl

theorem cell23_6717863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 3, 2, 1, 1, 3].length) (baseStart_6717863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6717863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6717863 prefixEnd_6717863 := by exact prefixLift 6717863
  have htrace : WordTrace (prefixWord ++ tailWord_6717863) baseStart_6717863 baseEnd_6717863 := by
    simpa [prefixWord, tailWord_6717863, baseEnd_6717863] using wordTrace_append hprefix tailTrace_6717863
  have hstable : (prefixWord ++ tailWord_6717863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6717863).length < 2 ^ (prefixWord ++ tailWord_6717863).sum := by decide
  have hdescent : baseEnd_6717863 < baseStart_6717863 := by decide
  rcases family_descends (prefixWord ++ tailWord_6717863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6717879 : List Nat := [1, 1, 3, 1, 3, 3, 4, 1, 2, 4]
def baseStart_6717879 : Nat := 118140960795 + 6717879 * 2 ^ 59
def prefixEnd_6717879 : Nat := 4983230072969 + 3 ^ 40 * 6717879 * 2
def baseEnd_6717879 : Nat := 1149833635248542333739181

theorem tailTrace_6717879 : CollatzResearch.WordTrace tailWord_6717879 prefixEnd_6717879 1149833635248542333739181 := by
  unfold tailWord_6717879
  simp only [CollatzResearch.WordTrace]
  refine ⟨245021176429279180235308691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163347450952852786823539127 245021176429279180235308691)
  ·
    refine ⟨367531764643918770352963037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245021176429279180235308691 367531764643918770352963037)
    ·
      refine ⟨137824411741469538882361139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 367531764643918770352963037 137824411741469538882361139)
      ·
        refine ⟨206736617612204308323541709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137824411741469538882361139 206736617612204308323541709)
        ·
          refine ⟨77526231604576615621328141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 206736617612204308323541709 77526231604576615621328141)
          ·
            refine ⟨29072336851716230857998053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77526231604576615621328141 29072336851716230857998053)
            ·
              refine ⟨5451063159696793285874635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29072336851716230857998053 5451063159696793285874635)
              ·
                refine ⟨8176594739545189928811953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5451063159696793285874635 8176594739545189928811953)
                ·
                  refine ⟨6132446054658892446608965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8176594739545189928811953 6132446054658892446608965)
                  ·
                    refine ⟨1149833635248542333739181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6132446054658892446608965 1149833635248542333739181)
                    ·
                      rfl

theorem cell23_6717879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 4, 1, 2, 4].length) (baseStart_6717879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6717879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6717879 prefixEnd_6717879 := by exact prefixLift 6717879
  have htrace : WordTrace (prefixWord ++ tailWord_6717879) baseStart_6717879 baseEnd_6717879 := by
    simpa [prefixWord, tailWord_6717879, baseEnd_6717879] using wordTrace_append hprefix tailTrace_6717879
  have hstable : (prefixWord ++ tailWord_6717879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6717879).length < 2 ^ (prefixWord ++ tailWord_6717879).sum := by decide
  have hdescent : baseEnd_6717879 < baseStart_6717879 := by decide
  rcases family_descends (prefixWord ++ tailWord_6717879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6717906 : List Nat := [3, 2, 2, 4, 1, 2, 1, 1, 1, 1, 5]
def baseStart_6717906 : Nat := 118140960795 + 6717906 * 2 ^ 59
def prefixEnd_6717906 : Nat := 4983230072969 + 3 ^ 40 * 6717906 * 2
def baseEnd_6717906 : Nat := 3449514769723298395579919

theorem tailTrace_6717906 : CollatzResearch.WordTrace tailWord_6717906 prefixEnd_6717906 3449514769723298395579919 := by
  unfold tailWord_6717906
  simp only [CollatzResearch.WordTrace]
  refine ⟨61255540300045340961635393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163348107466787575897694381 61255540300045340961635393)
  ·
    refine ⟨45941655225034005721226545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61255540300045340961635393 45941655225034005721226545)
    ·
      refine ⟨34456241418775504290919909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45941655225034005721226545 34456241418775504290919909)
      ·
        refine ⟨6460545266020407054547483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34456241418775504290919909 6460545266020407054547483)
        ·
          refine ⟨9690817899030610581821225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6460545266020407054547483 9690817899030610581821225)
          ·
            refine ⟨7268113424272957936365919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9690817899030610581821225 7268113424272957936365919)
            ·
              refine ⟨10902170136409436904548879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7268113424272957936365919 10902170136409436904548879)
              ·
                refine ⟨16353255204614155356823319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10902170136409436904548879 16353255204614155356823319)
                ·
                  refine ⟨24529882806921233035234979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16353255204614155356823319 24529882806921233035234979)
                  ·
                    refine ⟨36794824210381849552852469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24529882806921233035234979 36794824210381849552852469)
                    ·
                      refine ⟨3449514769723298395579919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36794824210381849552852469 3449514769723298395579919)
                      ·
                        rfl

theorem cell23_6717906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_6717906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6717906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6717906 prefixEnd_6717906 := by exact prefixLift 6717906
  have htrace : WordTrace (prefixWord ++ tailWord_6717906) baseStart_6717906 baseEnd_6717906 := by
    simpa [prefixWord, tailWord_6717906, baseEnd_6717906] using wordTrace_append hprefix tailTrace_6717906
  have hstable : (prefixWord ++ tailWord_6717906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6717906).length < 2 ^ (prefixWord ++ tailWord_6717906).sum := by decide
  have hdescent : baseEnd_6717906 < baseStart_6717906 := by decide
  rcases family_descends (prefixWord ++ tailWord_6717906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6717919 : List Nat := [1, 1, 2, 3, 3, 2, 1, 4, 2, 1, 3]
def baseStart_6717919 : Nat := 118140960795 + 6717919 * 2 ^ 59
def prefixEnd_6717919 : Nat := 4983230072969 + 3 ^ 40 * 6717919 * 2
def baseEnd_6717919 : Nat := 3449521444971806844717359

theorem tailTrace_6717919 : CollatzResearch.WordTrace tailWord_6717919 prefixEnd_6717919 3449521444971806844717359 := by
  unfold tailWord_6717919
  simp only [CollatzResearch.WordTrace]
  refine ⟨245022635349134267066764811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163348423566089511377843207 245022635349134267066764811)
  ·
    refine ⟨367533953023701400600147217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245022635349134267066764811 367533953023701400600147217)
    ·
      refine ⟨275650464767776050450110413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 367533953023701400600147217 275650464767776050450110413)
      ·
        refine ⟨103368924287916018918791405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 275650464767776050450110413 103368924287916018918791405)
        ·
          refine ⟨38763346607968507094546777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103368924287916018918791405 38763346607968507094546777)
          ·
            refine ⟨29072509955976380320910083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38763346607968507094546777 29072509955976380320910083)
            ·
              refine ⟨43608764933964570481365125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29072509955976380320910083 43608764933964570481365125)
              ·
                refine ⟨8176643425118356965255961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43608764933964570481365125 8176643425118356965255961)
                ·
                  refine ⟨6132482568838767723941971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8176643425118356965255961 6132482568838767723941971)
                  ·
                    refine ⟨9198723853258151585912957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6132482568838767723941971 9198723853258151585912957)
                    ·
                      refine ⟨3449521444971806844717359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9198723853258151585912957 3449521444971806844717359)
                      ·
                        rfl

theorem cell23_6717919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 4, 2, 1, 3].length) (baseStart_6717919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6717919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6717919 prefixEnd_6717919 := by exact prefixLift 6717919
  have htrace : WordTrace (prefixWord ++ tailWord_6717919) baseStart_6717919 baseEnd_6717919 := by
    simpa [prefixWord, tailWord_6717919, baseEnd_6717919] using wordTrace_append hprefix tailTrace_6717919
  have hstable : (prefixWord ++ tailWord_6717919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6717919).length < 2 ^ (prefixWord ++ tailWord_6717919).sum := by decide
  have hdescent : baseEnd_6717919 < baseStart_6717919 := by decide
  rcases family_descends (prefixWord ++ tailWord_6717919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6717942 : List Nat := [5, 1, 1, 1, 2, 1, 1, 2, 2, 3, 4]
def baseStart_6717942 : Nat := 118140960795 + 6717942 * 2 ^ 59
def prefixEnd_6717942 : Nat := 4983230072969 + 3 ^ 40 * 6717942 * 2
def baseEnd_6717942 : Nat := 3449533255026860254729753

theorem tailTrace_6717942 : CollatzResearch.WordTrace tailWord_6717942 prefixEnd_6717942 3449533255026860254729753 := by
  unfold tailWord_6717942
  simp only [CollatzResearch.WordTrace]
  refine ⟨15313967139253183874678255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 163348982818700627996568053 15313967139253183874678255)
  ·
    refine ⟨22970950708879775812017383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15313967139253183874678255 22970950708879775812017383)
    ·
      refine ⟨34456426063319663718026075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22970950708879775812017383 34456426063319663718026075)
      ·
        refine ⟨51684639094979495577039113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34456426063319663718026075 51684639094979495577039113)
        ·
          refine ⟨38763479321234621682779335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51684639094979495577039113 38763479321234621682779335)
          ·
            refine ⟨58145218981851932524169003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38763479321234621682779335 58145218981851932524169003)
            ·
              refine ⟨87217828472777898786253505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58145218981851932524169003 87217828472777898786253505)
              ·
                refine ⟨65413371354583424089690129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87217828472777898786253505 65413371354583424089690129)
                ·
                  refine ⟨49060028515937568067267597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65413371354583424089690129 49060028515937568067267597)
                  ·
                    refine ⟨18397510693476588025225349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49060028515937568067267597 18397510693476588025225349)
                    ·
                      refine ⟨3449533255026860254729753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18397510693476588025225349 3449533255026860254729753)
                      ·
                        rfl

theorem cell23_6717942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 2, 2, 3, 4].length) (baseStart_6717942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6717942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6717942 prefixEnd_6717942 := by exact prefixLift 6717942
  have htrace : WordTrace (prefixWord ++ tailWord_6717942) baseStart_6717942 baseEnd_6717942 := by
    simpa [prefixWord, tailWord_6717942, baseEnd_6717942] using wordTrace_append hprefix tailTrace_6717942
  have hstable : (prefixWord ++ tailWord_6717942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6717942).length < 2 ^ (prefixWord ++ tailWord_6717942).sum := by decide
  have hdescent : baseEnd_6717942 < baseStart_6717942 := by decide
  rcases family_descends (prefixWord ++ tailWord_6717942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6717945 : List Nat := [1, 2, 1, 3, 1, 2, 2, 1, 4, 1, 5]
def baseStart_6717945 : Nat := 118140960795 + 6717945 * 2 ^ 59
def prefixEnd_6717945 : Nat := 4983230072969 + 3 ^ 40 * 6717945 * 2
def baseEnd_6717945 : Nat := 3449534795468823742992239

theorem tailTrace_6717945 : CollatzResearch.WordTrace tailWord_6717945 prefixEnd_6717945 3449534795468823742992239 := by
  unfold tailWord_6717945
  simp only [CollatzResearch.WordTrace]
  refine ⟨245023583647040073507211289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163349055764693382338140859 245023583647040073507211289)
  ·
    refine ⟨183767687735280055130408467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245023583647040073507211289 183767687735280055130408467)
    ·
      refine ⟨275651531602920082695612701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183767687735280055130408467 275651531602920082695612701)
      ·
        refine ⟨103369324351095031010854763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 275651531602920082695612701 103369324351095031010854763)
        ·
          refine ⟨155053986526642546516282145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103369324351095031010854763 155053986526642546516282145)
          ·
            refine ⟨116290489894981909887211609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 155053986526642546516282145 116290489894981909887211609)
            ·
              refine ⟨87217867421236432415408707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116290489894981909887211609 87217867421236432415408707)
              ·
                refine ⟨130826801131854648623113061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87217867421236432415408707 130826801131854648623113061)
                ·
                  refine ⟨24530025212222746616833699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 130826801131854648623113061 24530025212222746616833699)
                  ·
                    refine ⟨36795037818334119925250549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24530025212222746616833699 36795037818334119925250549)
                    ·
                      refine ⟨3449534795468823742992239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36795037818334119925250549 3449534795468823742992239)
                      ·
                        rfl

theorem cell23_6717945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 1, 4, 1, 5].length) (baseStart_6717945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6717945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6717945 prefixEnd_6717945 := by exact prefixLift 6717945
  have htrace : WordTrace (prefixWord ++ tailWord_6717945) baseStart_6717945 baseEnd_6717945 := by
    simpa [prefixWord, tailWord_6717945, baseEnd_6717945] using wordTrace_append hprefix tailTrace_6717945
  have hstable : (prefixWord ++ tailWord_6717945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6717945).length < 2 ^ (prefixWord ++ tailWord_6717945).sum := by decide
  have hdescent : baseEnd_6717945 < baseStart_6717945 := by decide
  rcases family_descends (prefixWord ++ tailWord_6717945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6717955 : List Nat := [1, 1, 1, 3, 2, 1, 3, 2, 1, 4, 4]
def baseStart_6717955 : Nat := 118140960795 + 6717955 * 2 ^ 59
def prefixEnd_6717955 : Nat := 4983230072969 + 3 ^ 40 * 6717955 * 2
def baseEnd_6717955 : Nat := 3449539930275368703867193

theorem tailTrace_6717955 : CollatzResearch.WordTrace tailWord_6717955 prefixEnd_6717955 3449539930275368703867193 := by
  unfold tailWord_6717955
  simp only [CollatzResearch.WordTrace]
  refine ⟨245023948377003845215075319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163349298918002563476716879 245023948377003845215075319)
  ·
    refine ⟨367535922565505767822612979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245023948377003845215075319 367535922565505767822612979)
    ·
      refine ⟨551303883848258651733919469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 367535922565505767822612979 551303883848258651733919469)
      ·
        refine ⟨206738956443096994400219801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 551303883848258651733919469 206738956443096994400219801)
        ·
          refine ⟨155054217332322745800164851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 206738956443096994400219801 155054217332322745800164851)
          ·
            refine ⟨232581325998484118700247277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155054217332322745800164851 232581325998484118700247277)
            ·
              refine ⟨87217997249431544512592729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 232581325998484118700247277 87217997249431544512592729)
              ·
                refine ⟨65413497937073658384444547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87217997249431544512592729 65413497937073658384444547)
                ·
                  refine ⟨98120246905610487576666821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65413497937073658384444547 98120246905610487576666821)
                  ·
                    refine ⟨18397546294801966420625029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 98120246905610487576666821 18397546294801966420625029)
                    ·
                      refine ⟨3449539930275368703867193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18397546294801966420625029 3449539930275368703867193)
                      ·
                        rfl

theorem cell23_6717955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 2, 1, 4, 4].length) (baseStart_6717955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6717955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6717955 prefixEnd_6717955 := by exact prefixLift 6717955
  have htrace : WordTrace (prefixWord ++ tailWord_6717955) baseStart_6717955 baseEnd_6717955 := by
    simpa [prefixWord, tailWord_6717955, baseEnd_6717955] using wordTrace_append hprefix tailTrace_6717955
  have hstable : (prefixWord ++ tailWord_6717955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6717955).length < 2 ^ (prefixWord ++ tailWord_6717955).sum := by decide
  have hdescent : baseEnd_6717955 < baseStart_6717955 := by decide
  rcases family_descends (prefixWord ++ tailWord_6717955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6717963 : List Nat := [1, 1, 1, 1, 7, 3, 2, 1, 1, 3, 2]
def baseStart_6717963 : Nat := 118140960795 + 6717963 * 2 ^ 59
def prefixEnd_6717963 : Nat := 4983230072969 + 3 ^ 40 * 6717963 * 2
def baseEnd_6717963 : Nat := 3449544038120604672567157

theorem tailTrace_6717963 : CollatzResearch.WordTrace tailWord_6717963 prefixEnd_6717963 3449544038120604672567157 := by
  unfold tailWord_6717963
  simp only [CollatzResearch.WordTrace]
  refine ⟨245024240160974862581366543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163349493440649908387577695 245024240160974862581366543)
  ·
    refine ⟨367536360241462293872049815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245024240160974862581366543 367536360241462293872049815)
    ·
      refine ⟨551304540362193440808074723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 367536360241462293872049815 551304540362193440808074723)
      ·
        refine ⟨826956810543290161212112085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 551304540362193440808074723 826956810543290161212112085)
        ·
          refine ⟨19381800247108363153408877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 826956810543290161212112085 19381800247108363153408877)
          ·
            refine ⟨7268175092665636182528329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19381800247108363153408877 7268175092665636182528329)
            ·
              refine ⟨5451131319499227136896247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7268175092665636182528329 5451131319499227136896247)
              ·
                refine ⟨8176696979248840705344371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5451131319499227136896247 8176696979248840705344371)
                ·
                  refine ⟨12265045468873261058016557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8176696979248840705344371 12265045468873261058016557)
                  ·
                    refine ⟨4599392050827472896756209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12265045468873261058016557 4599392050827472896756209)
                    ·
                      refine ⟨3449544038120604672567157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4599392050827472896756209 3449544038120604672567157)
                      ·
                        rfl

theorem cell23_6717963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 2, 1, 1, 3, 2].length) (baseStart_6717963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6717963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6717963 prefixEnd_6717963 := by exact prefixLift 6717963
  have htrace : WordTrace (prefixWord ++ tailWord_6717963) baseStart_6717963 baseEnd_6717963 := by
    simpa [prefixWord, tailWord_6717963, baseEnd_6717963] using wordTrace_append hprefix tailTrace_6717963
  have hstable : (prefixWord ++ tailWord_6717963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6717963).length < 2 ^ (prefixWord ++ tailWord_6717963).sum := by decide
  have hdescent : baseEnd_6717963 < baseStart_6717963 := by decide
  rcases family_descends (prefixWord ++ tailWord_6717963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6717976 : List Nat := [2, 1, 2, 3, 3, 2, 1, 1, 4, 2, 2]
def baseStart_6717976 : Nat := 118140960795 + 6717976 * 2 ^ 59
def prefixEnd_6717976 : Nat := 4983230072969 + 3 ^ 40 * 6717976 * 2
def baseEnd_6717976 : Nat := 3449550713369113121704597

theorem tailTrace_6717976 : CollatzResearch.WordTrace tailWord_6717976 prefixEnd_6717976 3449550713369113121704597 := by
  unfold tailWord_6717976
  simp only [CollatzResearch.WordTrace]
  refine ⟨122512357154963882900794891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163349809539951843867726521 122512357154963882900794891)
  ·
    refine ⟨183768535732445824351192337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122512357154963882900794891 183768535732445824351192337)
    ·
      refine ⟨137826401799334368263394253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183768535732445824351192337 137826401799334368263394253)
      ·
        refine ⟨51684900674750388098772845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137826401799334368263394253 51684900674750388098772845)
        ·
          refine ⟨19381837753031395537039817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51684900674750388098772845 19381837753031395537039817)
          ·
            refine ⟨14536378314773546652779863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19381837753031395537039817 14536378314773546652779863)
            ·
              refine ⟨21804567472160319979169795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14536378314773546652779863 21804567472160319979169795)
              ·
                refine ⟨32706851208240479968754693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21804567472160319979169795 32706851208240479968754693)
                ·
                  refine ⟨6132534601545089994141505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32706851208240479968754693 6132534601545089994141505)
                  ·
                    refine ⟨4599400951158817495606129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6132534601545089994141505 4599400951158817495606129)
                    ·
                      refine ⟨3449550713369113121704597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4599400951158817495606129 3449550713369113121704597)
                      ·
                        rfl

theorem cell23_6717976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 1, 4, 2, 2].length) (baseStart_6717976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6717976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6717976 prefixEnd_6717976 := by exact prefixLift 6717976
  have htrace : WordTrace (prefixWord ++ tailWord_6717976) baseStart_6717976 baseEnd_6717976 := by
    simpa [prefixWord, tailWord_6717976, baseEnd_6717976] using wordTrace_append hprefix tailTrace_6717976
  have hstable : (prefixWord ++ tailWord_6717976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6717976).length < 2 ^ (prefixWord ++ tailWord_6717976).sum := by decide
  have hdescent : baseEnd_6717976 < baseStart_6717976 := by decide
  rcases family_descends (prefixWord ++ tailWord_6717976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6717997 : List Nat := [1, 5, 4, 1, 1, 1, 2, 2, 1, 3, 2]
def baseStart_6717997 : Nat := 118140960795 + 6717997 * 2 ^ 59
def prefixEnd_6717997 : Nat := 4983230072969 + 3 ^ 40 * 6717997 * 2
def baseEnd_6717997 : Nat := 3449561496462857539542001

theorem tailTrace_6717997 : CollatzResearch.WordTrace tailWord_6717997 prefixEnd_6717997 3449561496462857539542001 := by
  unfold tailWord_6717997
  simp only [CollatzResearch.WordTrace]
  refine ⟨245025480242851686388104245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163350320161901124258736163 245025480242851686388104245)
  ·
    refine ⟨22971138772767345598884773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 245025480242851686388104245 22971138772767345598884773)
    ·
      refine ⟨4307088519893877299790895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22971138772767345598884773 4307088519893877299790895)
      ·
        refine ⟨6460632779840815949686343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4307088519893877299790895 6460632779840815949686343)
        ·
          refine ⟨9690949169761223924529515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6460632779840815949686343 9690949169761223924529515)
          ·
            refine ⟨14536423754641835886794273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9690949169761223924529515 14536423754641835886794273)
            ·
              refine ⟨10902317815981376915095705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14536423754641835886794273 10902317815981376915095705)
              ·
                refine ⟨8176738361986032686321779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10902317815981376915095705 8176738361986032686321779)
                ·
                  refine ⟨12265107542979049029482669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8176738361986032686321779 12265107542979049029482669)
                  ·
                    refine ⟨4599415328617143386056001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12265107542979049029482669 4599415328617143386056001)
                    ·
                      refine ⟨3449561496462857539542001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4599415328617143386056001 3449561496462857539542001)
                      ·
                        rfl

theorem cell23_6717997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 2, 2, 1, 3, 2].length) (baseStart_6717997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6717997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6717997 prefixEnd_6717997 := by exact prefixLift 6717997
  have htrace : WordTrace (prefixWord ++ tailWord_6717997) baseStart_6717997 baseEnd_6717997 := by
    simpa [prefixWord, tailWord_6717997, baseEnd_6717997] using wordTrace_append hprefix tailTrace_6717997
  have hstable : (prefixWord ++ tailWord_6717997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6717997).length < 2 ^ (prefixWord ++ tailWord_6717997).sum := by decide
  have hdescent : baseEnd_6717997 < baseStart_6717997 := by decide
  rcases family_descends (prefixWord ++ tailWord_6717997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6718012 : List Nat := [2, 2, 2, 2, 3, 1, 2, 1, 1, 7]
def baseStart_6718012 : Nat := 118140960795 + 6718012 * 2 ^ 59
def prefixEnd_6718012 : Nat := 4983230072969 + 3 ^ 40 * 6718012 * 2
def baseEnd_6718012 : Nat := 1149856399557558326951477

theorem tailTrace_6718012 : CollatzResearch.WordTrace tailWord_6718012 prefixEnd_6718012 1149856399557558326951477 := by
  unfold tailWord_6718012
  simp only [CollatzResearch.WordTrace]
  refine ⟨122513013668898671974950145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163350684891864895966600193 122513013668898671974950145)
  ·
    refine ⟨91884760251674003981212609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122513013668898671974950145 91884760251674003981212609)
    ·
      refine ⟨68913570188755502985909457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91884760251674003981212609 68913570188755502985909457)
      ·
        refine ⟨51685177641566627239432093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68913570188755502985909457 51685177641566627239432093)
        ·
          refine ⟨19381941615587485214787035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51685177641566627239432093 19381941615587485214787035)
          ·
            refine ⟨29072912423381227822180553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19381941615587485214787035 29072912423381227822180553)
            ·
              refine ⟨21804684317535920866635415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29072912423381227822180553 21804684317535920866635415)
              ·
                refine ⟨32707026476303881299953123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21804684317535920866635415 32707026476303881299953123)
                ·
                  refine ⟨49060539714455821949929685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32707026476303881299953123 49060539714455821949929685)
                  ·
                    refine ⟨1149856399557558326951477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49060539714455821949929685 1149856399557558326951477)
                    ·
                      rfl

theorem cell23_6718012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 1, 1, 7].length) (baseStart_6718012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6718012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6718012 prefixEnd_6718012 := by exact prefixLift 6718012
  have htrace : WordTrace (prefixWord ++ tailWord_6718012) baseStart_6718012 baseEnd_6718012 := by
    simpa [prefixWord, tailWord_6718012, baseEnd_6718012] using wordTrace_append hprefix tailTrace_6718012
  have hstable : (prefixWord ++ tailWord_6718012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6718012).length < 2 ^ (prefixWord ++ tailWord_6718012).sum := by decide
  have hdescent : baseEnd_6718012 < baseStart_6718012 := by decide
  rcases family_descends (prefixWord ++ tailWord_6718012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6718029 : List Nat := [1, 6, 1, 1, 2, 1, 1, 1, 4, 5]
def baseStart_6718029 : Nat := 118140960795 + 6718029 * 2 ^ 59
def prefixEnd_6718029 : Nat := 4983230072969 + 3 ^ 40 * 6718029 * 2
def baseEnd_6718029 : Nat := 1149859309281267138113951

theorem tailTrace_6718029 : CollatzResearch.WordTrace tailWord_6718029 prefixEnd_6718029 1149859309281267138113951 := by
  unfold tailWord_6718029
  simp only [CollatzResearch.WordTrace]
  refine ⟨245026647378735755853269141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163351098252490503902179427 245026647378735755853269141)
  ·
    refine ⟨11485624095878238555621991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 245026647378735755853269141 11485624095878238555621991)
    ·
      refine ⟨17228436143817357833432987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11485624095878238555621991 17228436143817357833432987)
      ·
        refine ⟨25842654215726036750149481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17228436143817357833432987 25842654215726036750149481)
        ·
          refine ⟨19381990661794527562612111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25842654215726036750149481 19381990661794527562612111)
          ·
            refine ⟨29072985992691791343918167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19381990661794527562612111 29072985992691791343918167)
            ·
              refine ⟨43609478989037687015877251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29072985992691791343918167 43609478989037687015877251)
              ·
                refine ⟨65414218483556530523815877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43609478989037687015877251 65414218483556530523815877)
                ·
                  refine ⟨12265165965666849473215477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65414218483556530523815877 12265165965666849473215477)
                  ·
                    refine ⟨1149859309281267138113951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12265165965666849473215477 1149859309281267138113951)
                    ·
                      rfl

theorem cell23_6718029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 1, 4, 5].length) (baseStart_6718029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6718029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6718029 prefixEnd_6718029 := by exact prefixLift 6718029
  have htrace : WordTrace (prefixWord ++ tailWord_6718029) baseStart_6718029 baseEnd_6718029 := by
    simpa [prefixWord, tailWord_6718029, baseEnd_6718029] using wordTrace_append hprefix tailTrace_6718029
  have hstable : (prefixWord ++ tailWord_6718029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6718029).length < 2 ^ (prefixWord ++ tailWord_6718029).sum := by decide
  have hdescent : baseEnd_6718029 < baseStart_6718029 := by decide
  rcases family_descends (prefixWord ++ tailWord_6718029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6718066 : List Nat := [3, 2, 1, 2, 4, 1, 2, 1, 2, 1, 4]
def baseStart_6718066 : Nat := 118140960795 + 6718066 * 2 ^ 59
def prefixEnd_6718066 : Nat := 4983230072969 + 3 ^ 40 * 6718066 * 2
def baseEnd_6718066 : Nat := 3449596926628017769579183

theorem tailTrace_6718066 : CollatzResearch.WordTrace tailWord_6718066 prefixEnd_6718066 3449596926628017769579183 := by
  unfold tailWord_6718066
  simp only [CollatzResearch.WordTrace]
  refine ⟨61256999219900427793091513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163351997919734474114910701 61256999219900427793091513)
  ·
    refine ⟨45942749414925320844818635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61256999219900427793091513 45942749414925320844818635)
    ·
      refine ⟨68914124122387981267227953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45942749414925320844818635 68914124122387981267227953)
      ·
        refine ⟨51685593091790985950420965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68914124122387981267227953 51685593091790985950420965)
        ·
          refine ⟨9691048704710809865703931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51685593091790985950420965 9691048704710809865703931)
          ·
            refine ⟨14536573057066214798555897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9691048704710809865703931 14536573057066214798555897)
            ·
              refine ⟨10902429792799661098916923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14536573057066214798555897 10902429792799661098916923)
              ·
                refine ⟨16353644689199491648375385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10902429792799661098916923 16353644689199491648375385)
                ·
                  refine ⟨12265233516899618736281539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16353644689199491648375385 12265233516899618736281539)
                  ·
                    refine ⟨18397850275349428104422309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12265233516899618736281539 18397850275349428104422309)
                    ·
                      refine ⟨3449596926628017769579183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18397850275349428104422309 3449596926628017769579183)
                      ·
                        rfl

theorem cell23_6718066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 2, 1, 2, 1, 4].length) (baseStart_6718066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6718066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6718066 prefixEnd_6718066 := by exact prefixLift 6718066
  have htrace : WordTrace (prefixWord ++ tailWord_6718066) baseStart_6718066 baseEnd_6718066 := by
    simpa [prefixWord, tailWord_6718066, baseEnd_6718066] using wordTrace_append hprefix tailTrace_6718066
  have hstable : (prefixWord ++ tailWord_6718066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6718066).length < 2 ^ (prefixWord ++ tailWord_6718066).sum := by decide
  have hdescent : baseEnd_6718066 < baseStart_6718066 := by decide
  rcases family_descends (prefixWord ++ tailWord_6718066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6718116 : List Nat := [2, 3, 1, 2, 2, 1, 3, 2, 3, 1, 3]
def baseStart_6718116 : Nat := 118140960795 + 6718116 * 2 ^ 59
def prefixEnd_6718116 : Nat := 4983230072969 + 3 ^ 40 * 6718116 * 2
def baseEnd_6718116 : Nat := 3449622600660742573953953

theorem tailTrace_6718116 : CollatzResearch.WordTrace tailWord_6718116 prefixEnd_6718116 3449622600660742573953953 := by
  unfold tailWord_6718116
  simp only [CollatzResearch.WordTrace]
  refine ⟨122514910264710284855843101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163353213686280379807790801 122514910264710284855843101)
  ·
    refine ⟨45943091349266356820941163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122514910264710284855843101 45943091349266356820941163)
    ·
      refine ⟨68914637023899535231411745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45943091349266356820941163 68914637023899535231411745)
      ·
        refine ⟨51685977767924651423558809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68914637023899535231411745 51685977767924651423558809)
        ·
          refine ⟨38764483325943488567669107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51685977767924651423558809 38764483325943488567669107)
          ·
            refine ⟨58146724988915232851503661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38764483325943488567669107 58146724988915232851503661)
            ·
              refine ⟨21805021870843212319313873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58146724988915232851503661 21805021870843212319313873)
              ·
                refine ⟨16353766403132409239485405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21805021870843212319313873 16353766403132409239485405)
                ·
                  refine ⟨6132662401174653464807027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16353766403132409239485405 6132662401174653464807027)
                  ·
                    refine ⟨9198993601761980197210541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6132662401174653464807027 9198993601761980197210541)
                    ·
                      refine ⟨3449622600660742573953953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9198993601761980197210541 3449622600660742573953953)
                      ·
                        rfl

theorem cell23_6718116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 2, 3, 1, 3].length) (baseStart_6718116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6718116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6718116 prefixEnd_6718116 := by exact prefixLift 6718116
  have htrace : WordTrace (prefixWord ++ tailWord_6718116) baseStart_6718116 baseEnd_6718116 := by
    simpa [prefixWord, tailWord_6718116, baseEnd_6718116] using wordTrace_append hprefix tailTrace_6718116
  have hstable : (prefixWord ++ tailWord_6718116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6718116).length < 2 ^ (prefixWord ++ tailWord_6718116).sum := by decide
  have hdescent : baseEnd_6718116 < baseStart_6718116 := by decide
  rcases family_descends (prefixWord ++ tailWord_6718116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6718179 : List Nat := [1, 1, 1, 7, 1, 2, 1, 9]
def baseStart_6718179 : Nat := 118140960795 + 6718179 * 2 ^ 59
def prefixEnd_6718179 : Nat := 4983230072969 + 3 ^ 40 * 6718179 * 2
def baseEnd_6718179 : Nat := 127764998145999104720969

theorem tailTrace_6718179 : CollatzResearch.WordTrace tailWord_6718179 prefixEnd_6718179 127764998145999104720969 := by
  unfold tailWord_6718179
  simp only [CollatzResearch.WordTrace]
  refine ⟨245032118328192331471229591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163354745552128220980819727 245032118328192331471229591)
  ·
    refine ⟨367548177492288497206844387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245032118328192331471229591 367548177492288497206844387)
    ·
      refine ⟨551322266238432745810266581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 367548177492288497206844387 551322266238432745810266581)
      ·
        refine ⟨12921615614963267479928123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 551322266238432745810266581 12921615614963267479928123)
        ·
          refine ⟨19382423422444901219892185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12921615614963267479928123 19382423422444901219892185)
          ·
            refine ⟨14536817566833675914919139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19382423422444901219892185 14536817566833675914919139)
            ·
              refine ⟨21805226350250513872378709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14536817566833675914919139 21805226350250513872378709)
              ·
                refine ⟨127764998145999104720969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 21805226350250513872378709 127764998145999104720969)
                ·
                  rfl

theorem cell23_6718179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 9].length) (baseStart_6718179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6718179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6718179 prefixEnd_6718179 := by exact prefixLift 6718179
  have htrace : WordTrace (prefixWord ++ tailWord_6718179) baseStart_6718179 baseEnd_6718179 := by
    simpa [prefixWord, tailWord_6718179, baseEnd_6718179] using wordTrace_append hprefix tailTrace_6718179
  have hstable : (prefixWord ++ tailWord_6718179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6718179).length < 2 ^ (prefixWord ++ tailWord_6718179).sum := by decide
  have hdescent : baseEnd_6718179 < baseStart_6718179 := by decide
  rcases family_descends (prefixWord ++ tailWord_6718179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6718273 : List Nat := [1, 2, 5, 3, 1, 1, 1, 1, 2, 6]
def baseStart_6718273 : Nat := 118140960795 + 6718273 * 2 ^ 59
def prefixEnd_6718273 : Nat := 4983230072969 + 3 ^ 40 * 6718273 * 2
def baseEnd_6718273 : Nat := 1149901072374499486563577

theorem tailTrace_6718273 : CollatzResearch.WordTrace tailWord_6718273 prefixEnd_6718273 1149901072374499486563577 := by
  unfold tailWord_6718273
  simp only [CollatzResearch.WordTrace]
  refine ⟨245035546789851785525151473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163357031193234523683434315 245035546789851785525151473)
  ·
    refine ⟨183776660092388839143863605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245035546789851785525151473 183776660092388839143863605)
    ·
      refine ⟨17229061883661453669737213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 183776660092388839143863605 17229061883661453669737213)
      ·
        refine ⟨6460898206373045126151455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17229061883661453669737213 6460898206373045126151455)
        ·
          refine ⟨9691347309559567689227183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6460898206373045126151455 9691347309559567689227183)
          ·
            refine ⟨14537020964339351533840775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9691347309559567689227183 14537020964339351533840775)
            ·
              refine ⟨21805531446509027300761163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14537020964339351533840775 21805531446509027300761163)
              ·
                refine ⟨32708297169763540951141745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21805531446509027300761163 32708297169763540951141745)
                ·
                  refine ⟨24531222877322655713356309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32708297169763540951141745 24531222877322655713356309)
                  ·
                    refine ⟨1149901072374499486563577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24531222877322655713356309 1149901072374499486563577)
                    ·
                      rfl

theorem cell23_6718273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 1, 2, 6].length) (baseStart_6718273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6718273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6718273 prefixEnd_6718273 := by exact prefixLift 6718273
  have htrace : WordTrace (prefixWord ++ tailWord_6718273) baseStart_6718273 baseEnd_6718273 := by
    simpa [prefixWord, tailWord_6718273, baseEnd_6718273] using wordTrace_append hprefix tailTrace_6718273
  have hstable : (prefixWord ++ tailWord_6718273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6718273).length < 2 ^ (prefixWord ++ tailWord_6718273).sum := by decide
  have hdescent : baseEnd_6718273 < baseStart_6718273 := by decide
  rcases family_descends (prefixWord ++ tailWord_6718273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6718309 : List Nat := [1, 3, 1, 3, 1, 1, 2, 1, 3, 2, 5]
def baseStart_6718309 : Nat := 118140960795 + 6718309 * 2 ^ 59
def prefixEnd_6718309 : Nat := 4983230072969 + 3 ^ 40 * 6718309 * 2
def baseEnd_6718309 : Nat := 3449721702427060318840565

theorem tailTrace_6718309 : CollatzResearch.WordTrace tailWord_6718309 prefixEnd_6718309 3449721702427060318840565 := by
  unfold tailWord_6718309
  simp only [CollatzResearch.WordTrace]
  refine ⟨245036859817721363673461981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163357906545147575782307987 245036859817721363673461981)
  ·
    refine ⟨91888822431645511377548243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 245036859817721363673461981 91888822431645511377548243)
    ·
      refine ⟨137833233647468267066322365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91888822431645511377548243 137833233647468267066322365)
      ·
        refine ⟨51687462617800600149870887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137833233647468267066322365 51687462617800600149870887)
        ·
          refine ⟨77531193926700900224806331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51687462617800600149870887 77531193926700900224806331)
          ·
            refine ⟨116296790890051350337209497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77531193926700900224806331 116296790890051350337209497)
            ·
              refine ⟨87222593167538512752907123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116296790890051350337209497 87222593167538512752907123)
              ·
                refine ⟨130833889751307769129360685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87222593167538512752907123 130833889751307769129360685)
                ·
                  refine ⟨49062708656740413423510257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 130833889751307769129360685 49062708656740413423510257)
                  ·
                    refine ⟨36797031492555310067632693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49062708656740413423510257 36797031492555310067632693)
                    ·
                      refine ⟨3449721702427060318840565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36797031492555310067632693 3449721702427060318840565)
                      ·
                        rfl

theorem cell23_6718309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 1, 3, 2, 5].length) (baseStart_6718309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6718309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6718309 prefixEnd_6718309 := by exact prefixLift 6718309
  have htrace : WordTrace (prefixWord ++ tailWord_6718309) baseStart_6718309 baseEnd_6718309 := by
    simpa [prefixWord, tailWord_6718309, baseEnd_6718309] using wordTrace_append hprefix tailTrace_6718309
  have hstable : (prefixWord ++ tailWord_6718309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6718309).length < 2 ^ (prefixWord ++ tailWord_6718309).sum := by decide
  have hdescent : baseEnd_6718309 < baseStart_6718309 := by decide
  rcases family_descends (prefixWord ++ tailWord_6718309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6718336 : List Nat := [2, 1, 1, 2, 1, 2, 2, 3, 1, 6, 2]
def baseStart_6718336 : Nat := 118140960795 + 6718336 * 2 ^ 59
def prefixEnd_6718336 : Nat := 4983230072969 + 3 ^ 40 * 6718336 * 2
def baseEnd_6718336 : Nat := 3449735566404731713202941

theorem tailTrace_6718336 : CollatzResearch.WordTrace tailWord_6718336 prefixEnd_6718336 3449735566404731713202941 := by
  unfold tailWord_6718336
  simp only [CollatzResearch.WordTrace]
  refine ⟨122518922294311773642347431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163358563059082364856463241 122518922294311773642347431)
  ·
    refine ⟨183778383441467660463521147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122518922294311773642347431 183778383441467660463521147)
    ·
      refine ⟨275667575162201490695281721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183778383441467660463521147 275667575162201490695281721)
      ·
        refine ⟨206750681371651118021461291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 275667575162201490695281721 206750681371651118021461291)
        ·
          refine ⟨310126022057476677032191937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206750681371651118021461291 310126022057476677032191937)
          ·
            refine ⟨232594516543107507774143953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 310126022057476677032191937 232594516543107507774143953)
            ·
              refine ⟨174445887407330630830607965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 232594516543107507774143953 174445887407330630830607965)
              ·
                refine ⟨65417207777748986561477987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 174445887407330630830607965 65417207777748986561477987)
                ·
                  refine ⟨98125811666623479842216981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65417207777748986561477987 98125811666623479842216981)
                  ·
                    refine ⟨4599647421872975617603921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 98125811666623479842216981 4599647421872975617603921)
                    ·
                      refine ⟨3449735566404731713202941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4599647421872975617603921 3449735566404731713202941)
                      ·
                        rfl

theorem cell23_6718336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 3, 1, 6, 2].length) (baseStart_6718336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6718336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6718336 prefixEnd_6718336 := by exact prefixLift 6718336
  have htrace : WordTrace (prefixWord ++ tailWord_6718336) baseStart_6718336 baseEnd_6718336 := by
    simpa [prefixWord, tailWord_6718336, baseEnd_6718336] using wordTrace_append hprefix tailTrace_6718336
  have hstable : (prefixWord ++ tailWord_6718336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6718336).length < 2 ^ (prefixWord ++ tailWord_6718336).sum := by decide
  have hdescent : baseEnd_6718336 < baseStart_6718336 := by decide
  rcases family_descends (prefixWord ++ tailWord_6718336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6718359 : List Nat := [1, 1, 3, 3, 1, 2, 1, 1, 10]
def baseStart_6718359 : Nat := 118140960795 + 6718359 * 2 ^ 59
def prefixEnd_6718359 : Nat := 4983230072969 + 3 ^ 40 * 6718359 * 2
def baseEnd_6718359 : Nat := 383305264051087235912815

theorem tailTrace_6718359 : CollatzResearch.WordTrace tailWord_6718359 prefixEnd_6718359 383305264051087235912815 := by
  unfold tailWord_6718359
  simp only [CollatzResearch.WordTrace]
  refine ⟨245038683467540222212782131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163359122311693481475188087 245038683467540222212782131)
  ·
    refine ⟨367558025201310333319173197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245038683467540222212782131 367558025201310333319173197)
    ·
      refine ⟨137834259450491374994689949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 367558025201310333319173197 137834259450491374994689949)
      ·
        refine ⟨51687847293934265623008731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137834259450491374994689949 51687847293934265623008731)
        ·
          refine ⟨77531770940901398434513097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51687847293934265623008731 77531770940901398434513097)
          ·
            refine ⟨58148828205676048825884823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77531770940901398434513097 58148828205676048825884823)
            ·
              refine ⟨87223242308514073238827235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58148828205676048825884823 87223242308514073238827235)
              ·
                refine ⟨130834863462771109858240853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87223242308514073238827235 130834863462771109858240853)
                ·
                  refine ⟨383305264051087235912815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 130834863462771109858240853 383305264051087235912815)
                  ·
                    rfl

theorem cell23_6718359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 1, 10].length) (baseStart_6718359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6718359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6718359 prefixEnd_6718359 := by exact prefixLift 6718359
  have htrace : WordTrace (prefixWord ++ tailWord_6718359) baseStart_6718359 baseEnd_6718359 := by
    simpa [prefixWord, tailWord_6718359, baseEnd_6718359] using wordTrace_append hprefix tailTrace_6718359
  have hstable : (prefixWord ++ tailWord_6718359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6718359).length < 2 ^ (prefixWord ++ tailWord_6718359).sum := by decide
  have hdescent : baseEnd_6718359 < baseStart_6718359 := by decide
  rcases family_descends (prefixWord ++ tailWord_6718359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6718393 : List Nat := [1, 2, 1, 4, 2, 2, 4, 1, 6]
def baseStart_6718393 : Nat := 118140960795 + 6718393 * 2 ^ 59
def prefixEnd_6718393 : Nat := 4983230072969 + 3 ^ 40 * 6718393 * 2
def baseEnd_6718393 : Nat := 383307203866893110021131

theorem tailTrace_6718393 : CollatzResearch.WordTrace tailWord_6718393 prefixEnd_6718393 383307203866893110021131 := by
  unfold tailWord_6718393
  simp only [CollatzResearch.WordTrace]
  refine ⟨245039923549417046019519833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163359949032944697346346555 245039923549417046019519833)
  ·
    refine ⟨183779942662062784514639875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245039923549417046019519833 183779942662062784514639875)
    ·
      refine ⟨275669913993094176771959813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183779942662062784514639875 275669913993094176771959813)
      ·
        refine ⟨51688108873705158144742465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 275669913993094176771959813 51688108873705158144742465)
        ·
          refine ⟨38766081655278868608556849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51688108873705158144742465 38766081655278868608556849)
          ·
            refine ⟨29074561241459151456417637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38766081655278868608556849 29074561241459151456417637)
            ·
              refine ⟨5451480232773590898078307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29074561241459151456417637 5451480232773590898078307)
              ·
                refine ⟨8177220349160386347117461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5451480232773590898078307 8177220349160386347117461)
                ·
                  refine ⟨383307203866893110021131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8177220349160386347117461 383307203866893110021131)
                  ·
                    rfl

theorem cell23_6718393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 4, 1, 6].length) (baseStart_6718393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6718393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6718393 prefixEnd_6718393 := by exact prefixLift 6718393
  have htrace : WordTrace (prefixWord ++ tailWord_6718393) baseStart_6718393 baseEnd_6718393 := by
    simpa [prefixWord, tailWord_6718393, baseEnd_6718393] using wordTrace_append hprefix tailTrace_6718393
  have hstable : (prefixWord ++ tailWord_6718393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6718393).length < 2 ^ (prefixWord ++ tailWord_6718393).sum := by decide
  have hdescent : baseEnd_6718393 < baseStart_6718393 := by decide
  rcases family_descends (prefixWord ++ tailWord_6718393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6718399 : List Nat := [1, 1, 2, 2, 2, 1, 2, 1, 1, 3, 7]
def baseStart_6718399 : Nat := 118140960795 + 6718399 * 2 ^ 59
def prefixEnd_6718399 : Nat := 4983230072969 + 3 ^ 40 * 6718399 * 2
def baseEnd_6718399 : Nat := 3449767915685964966715151

theorem tailTrace_6718399 : CollatzResearch.WordTrace tailWord_6718399 prefixEnd_6718399 3449767915685964966715151 := by
  unfold tailWord_6718399
  simp only [CollatzResearch.WordTrace]
  refine ⟨245040142387395309044238251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163360094924930206029492167 245040142387395309044238251)
  ·
    refine ⟨367560213581092963566357377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245040142387395309044238251 367560213581092963566357377)
    ·
      refine ⟨275670160185819722674768033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 367560213581092963566357377 275670160185819722674768033)
      ·
        refine ⟨206752620139364792006076025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 275670160185819722674768033 206752620139364792006076025)
        ·
          refine ⟨155064465104523594004557019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 206752620139364792006076025 155064465104523594004557019)
          ·
            refine ⟨232596697656785391006835529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155064465104523594004557019 232596697656785391006835529)
            ·
              refine ⟨174447523242589043255126647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 232596697656785391006835529 174447523242589043255126647)
              ·
                refine ⟨261671284863883564882689971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 174447523242589043255126647 261671284863883564882689971)
                ·
                  refine ⟨392506927295825347324034957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 261671284863883564882689971 392506927295825347324034957)
                  ·
                    refine ⟨147190097735934505246513109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 392506927295825347324034957 147190097735934505246513109)
                    ·
                      refine ⟨3449767915685964966715151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 147190097735934505246513109 3449767915685964966715151)
                      ·
                        rfl

theorem cell23_6718399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1, 3, 7].length) (baseStart_6718399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6718399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6718399 prefixEnd_6718399 := by exact prefixLift 6718399
  have htrace : WordTrace (prefixWord ++ tailWord_6718399) baseStart_6718399 baseEnd_6718399 := by
    simpa [prefixWord, tailWord_6718399, baseEnd_6718399] using wordTrace_append hprefix tailTrace_6718399
  have hstable : (prefixWord ++ tailWord_6718399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6718399).length < 2 ^ (prefixWord ++ tailWord_6718399).sum := by decide
  have hdescent : baseEnd_6718399 < baseStart_6718399 := by decide
  rcases family_descends (prefixWord ++ tailWord_6718399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6718460 : List Nat := [2, 2, 2, 1, 2, 3, 1, 1, 5, 2, 2]
def baseStart_6718460 : Nat := 118140960795 + 6718460 * 2 ^ 59
def prefixEnd_6718460 : Nat := 4983230072969 + 3 ^ 40 * 6718460 * 2
def baseEnd_6718460 : Nat := 3449799238005889228052371

theorem tailTrace_6718460 : CollatzResearch.WordTrace tailWord_6718460 prefixEnd_6718460 3449799238005889228052371 := by
  unfold tailWord_6718460
  simp only [CollatzResearch.WordTrace]
  refine ⟨122521183620087158231104417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163361578160116210974805889 122521183620087158231104417)
  ·
    refine ⟨91890887715065368673328313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122521183620087158231104417 91890887715065368673328313)
    ·
      refine ⟨68918165786299026504996235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91890887715065368673328313 68918165786299026504996235)
      ·
        refine ⟨103377248679448539757494353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68918165786299026504996235 103377248679448539757494353)
        ·
          refine ⟨77532936509586404818120765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103377248679448539757494353 77532936509586404818120765)
          ·
            refine ⟨29074851191094901806795287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77532936509586404818120765 29074851191094901806795287)
            ·
              refine ⟨43612276786642352710192931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29074851191094901806795287 43612276786642352710192931)
              ·
                refine ⟨65418415179963529065289397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43612276786642352710192931 65418415179963529065289397)
                ·
                  refine ⟨6132976423121580849870881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 65418415179963529065289397 6132976423121580849870881)
                  ·
                    refine ⟨4599732317341185637403161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6132976423121580849870881 4599732317341185637403161)
                    ·
                      refine ⟨3449799238005889228052371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4599732317341185637403161 3449799238005889228052371)
                      ·
                        rfl

theorem cell23_6718460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 1, 5, 2, 2].length) (baseStart_6718460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6718460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6718460 prefixEnd_6718460 := by exact prefixLift 6718460
  have htrace : WordTrace (prefixWord ++ tailWord_6718460) baseStart_6718460 baseEnd_6718460 := by
    simpa [prefixWord, tailWord_6718460, baseEnd_6718460] using wordTrace_append hprefix tailTrace_6718460
  have hstable : (prefixWord ++ tailWord_6718460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6718460).length < 2 ^ (prefixWord ++ tailWord_6718460).sum := by decide
  have hdescent : baseEnd_6718460 < baseStart_6718460 := by decide
  rcases family_descends (prefixWord ++ tailWord_6718460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6718487 : List Nat := [1, 1, 3, 5, 1, 3, 1, 2, 2, 4]
def baseStart_6718487 : Nat := 118140960795 + 6718487 * 2 ^ 59
def prefixEnd_6718487 : Nat := 4983230072969 + 3 ^ 40 * 6718487 * 2
def baseEnd_6718487 : Nat := 1149937700661186874138249

theorem tailTrace_6718487 : CollatzResearch.WordTrace tailWord_6718487 prefixEnd_6718487 1149937700661186874138249 := by
  unfold tailWord_6718487
  simp only [CollatzResearch.WordTrace]
  refine ⟨245043352011076500073441715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163362234674051000048961143 245043352011076500073441715)
  ·
    refine ⟨367565028016614750110162573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245043352011076500073441715 367565028016614750110162573)
    ·
      refine ⟨137836885506230531291310965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 367565028016614750110162573 137836885506230531291310965)
      ·
        refine ⟨12922208016209112308560403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 137836885506230531291310965 12922208016209112308560403)
        ·
          refine ⟨19383312024313668462840605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12922208016209112308560403 19383312024313668462840605)
          ·
            refine ⟨7268742009117625673565227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19383312024313668462840605 7268742009117625673565227)
            ·
              refine ⟨10903113013676438510347841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7268742009117625673565227 10903113013676438510347841)
              ·
                refine ⟨8177334760257328882760881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10903113013676438510347841 8177334760257328882760881)
                ·
                  refine ⟨6133001070192996662070661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8177334760257328882760881 6133001070192996662070661)
                  ·
                    refine ⟨1149937700661186874138249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6133001070192996662070661 1149937700661186874138249)
                    ·
                      rfl

theorem cell23_6718487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 1, 2, 2, 4].length) (baseStart_6718487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6718487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6718487 prefixEnd_6718487 := by exact prefixLift 6718487
  have htrace : WordTrace (prefixWord ++ tailWord_6718487) baseStart_6718487 baseEnd_6718487 := by
    simpa [prefixWord, tailWord_6718487, baseEnd_6718487] using wordTrace_append hprefix tailTrace_6718487
  have hstable : (prefixWord ++ tailWord_6718487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6718487).length < 2 ^ (prefixWord ++ tailWord_6718487).sum := by decide
  have hdescent : baseEnd_6718487 < baseStart_6718487 := by decide
  rcases family_descends (prefixWord ++ tailWord_6718487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6718653 : List Nat := [1, 4, 1, 2, 1, 1, 3, 1, 2, 1, 6]
def baseStart_6718653 : Nat := 118140960795 + 6718653 * 2 ^ 59
def prefixEnd_6718653 : Nat := 4983230072969 + 3 ^ 40 * 6718653 * 2
def baseEnd_6718653 : Nat := 3449898339772206972938983

theorem tailTrace_6718653 : CollatzResearch.WordTrace tailWord_6718653 prefixEnd_6718653 3449898339772206972938983 := by
  unfold tailWord_6718653
  simp only [CollatzResearch.WordTrace]
  refine ⟨245049406528475110423984613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163366271018983406949323075 245049406528475110423984613)
  ·
    refine ⟨45946763724089083204497115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 245049406528475110423984613 45946763724089083204497115)
    ·
      refine ⟨68920145586133624806745673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45946763724089083204497115 68920145586133624806745673)
      ·
        refine ⟨51690109189600218605059255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68920145586133624806745673 51690109189600218605059255)
        ·
          refine ⟨77535163784400327907588883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51690109189600218605059255 77535163784400327907588883)
          ·
            refine ⟨116302745676600491861383325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77535163784400327907588883 116302745676600491861383325)
            ·
              refine ⟨43613529628725184448018747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 116302745676600491861383325 43613529628725184448018747)
              ·
                refine ⟨65420294443087776672028121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43613529628725184448018747 65420294443087776672028121)
                ·
                  refine ⟨49065220832315832504021091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65420294443087776672028121 49065220832315832504021091)
                  ·
                    refine ⟨73597831248473748756031637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49065220832315832504021091 73597831248473748756031637)
                    ·
                      refine ⟨3449898339772206972938983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 73597831248473748756031637 3449898339772206972938983)
                      ·
                        rfl

theorem cell23_6718653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 1, 2, 1, 6].length) (baseStart_6718653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6718653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6718653 prefixEnd_6718653 := by exact prefixLift 6718653
  have htrace : WordTrace (prefixWord ++ tailWord_6718653) baseStart_6718653 baseEnd_6718653 := by
    simpa [prefixWord, tailWord_6718653, baseEnd_6718653] using wordTrace_append hprefix tailTrace_6718653
  have hstable : (prefixWord ++ tailWord_6718653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6718653).length < 2 ^ (prefixWord ++ tailWord_6718653).sum := by decide
  have hdescent : baseEnd_6718653 < baseStart_6718653 := by decide
  rcases family_descends (prefixWord ++ tailWord_6718653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6718701 : List Nat := [1, 5, 1, 2, 2, 3, 1, 3, 1, 4]
def baseStart_6718701 : Nat := 118140960795 + 6718701 * 2 ^ 59
def prefixEnd_6718701 : Nat := 4983230072969 + 3 ^ 40 * 6718701 * 2
def baseEnd_6718701 : Nat := 1149974328947874261712921

theorem tailTrace_6718701 : CollatzResearch.WordTrace tailWord_6718701 prefixEnd_6718701 1149974328947874261712921 := by
  unfold tailWord_6718701
  simp only [CollatzResearch.WordTrace]
  refine ⟨245051157232301214621731957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163367438154867476414487971 245051157232301214621731957)
  ·
    refine ⟨22973545990528238870787371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 245051157232301214621731957 22973545990528238870787371)
    ·
      refine ⟨34460318985792358306181057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22973545990528238870787371 34460318985792358306181057)
      ·
        refine ⟨25845239239344268729635793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34460318985792358306181057 25845239239344268729635793)
        ·
          refine ⟨19383929429508201547226845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25845239239344268729635793 19383929429508201547226845)
          ·
            refine ⟨7268973536065575580210067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19383929429508201547226845 7268973536065575580210067)
            ·
              refine ⟨10903460304098363370315101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7268973536065575580210067 10903460304098363370315101)
              ·
                refine ⟨4088797614036886263868163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10903460304098363370315101 4088797614036886263868163)
                ·
                  refine ⟨6133196421055329395802245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4088797614036886263868163 6133196421055329395802245)
                  ·
                    refine ⟨1149974328947874261712921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6133196421055329395802245 1149974328947874261712921)
                    ·
                      rfl

theorem cell23_6718701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 1, 3, 1, 4].length) (baseStart_6718701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6718701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6718701 prefixEnd_6718701 := by exact prefixLift 6718701
  have htrace : WordTrace (prefixWord ++ tailWord_6718701) baseStart_6718701 baseEnd_6718701 := by
    simpa [prefixWord, tailWord_6718701, baseEnd_6718701] using wordTrace_append hprefix tailTrace_6718701
  have hstable : (prefixWord ++ tailWord_6718701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6718701).length < 2 ^ (prefixWord ++ tailWord_6718701).sum := by decide
  have hdescent : baseEnd_6718701 < baseStart_6718701 := by decide
  rcases family_descends (prefixWord ++ tailWord_6718701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6718710 : List Nat := [5, 1, 1, 1, 1, 1, 1, 2, 5, 5]
def baseStart_6718710 : Nat := 118140960795 + 6718710 * 2 ^ 59
def prefixEnd_6718710 : Nat := 4983230072969 + 3 ^ 40 * 6718710 * 2
def baseEnd_6718710 : Nat := 1149975869389837749975407

theorem tailTrace_6718710 : CollatzResearch.WordTrace tailWord_6718710 prefixEnd_6718710 1149975869389837749975407 := by
  unfold tailWord_6718710
  simp only [CollatzResearch.WordTrace]
  refine ⟨15315717843079288072425599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 163367656992845739439206389 15315717843079288072425599)
  ·
    refine ⟨22973576764618932108638399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15315717843079288072425599 22973576764618932108638399)
    ·
      refine ⟨34460365146928398162957599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22973576764618932108638399 34460365146928398162957599)
      ·
        refine ⟨51690547720392597244436399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34460365146928398162957599 51690547720392597244436399)
        ·
          refine ⟨77535821580588895866654599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51690547720392597244436399 77535821580588895866654599)
          ·
            refine ⟨116303732370883343799981899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77535821580588895866654599 116303732370883343799981899)
            ·
              refine ⟨174455598556325015699972849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116303732370883343799981899 174455598556325015699972849)
              ·
                refine ⟨130841698917243761774979637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 174455598556325015699972849 130841698917243761774979637)
                ·
                  refine ⟨12266409273491602666404341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 130841698917243761774979637 12266409273491602666404341)
                  ·
                    refine ⟨1149975869389837749975407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12266409273491602666404341 1149975869389837749975407)
                    ·
                      rfl

theorem cell23_6718710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 2, 5, 5].length) (baseStart_6718710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6718710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6718710 prefixEnd_6718710 := by exact prefixLift 6718710
  have htrace : WordTrace (prefixWord ++ tailWord_6718710) baseStart_6718710 baseEnd_6718710 := by
    simpa [prefixWord, tailWord_6718710, baseEnd_6718710] using wordTrace_append hprefix tailTrace_6718710
  have hstable : (prefixWord ++ tailWord_6718710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6718710).length < 2 ^ (prefixWord ++ tailWord_6718710).sum := by decide
  have hdescent : baseEnd_6718710 < baseStart_6718710 := by decide
  rcases family_descends (prefixWord ++ tailWord_6718710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6718724 : List Nat := [2, 3, 2, 2, 2, 1, 3, 1, 3, 1, 3]
def baseStart_6718724 : Nat := 118140960795 + 6718724 * 2 ^ 59
def prefixEnd_6718724 : Nat := 4983230072969 + 3 ^ 40 * 6718724 * 2
def baseEnd_6718724 : Nat := 3449934796898676195151157

theorem tailTrace_6718724 : CollatzResearch.WordTrace tailWord_6718724 prefixEnd_6718724 3449934796898676195151157 := by
  unfold tailWord_6718724
  simp only [CollatzResearch.WordTrace]
  refine ⟨122525998055608944774909613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163367997407478593033212817 122525998055608944774909613)
  ·
    refine ⟨45947249270853354290591105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122525998055608944774909613 45947249270853354290591105)
    ·
      refine ⟨34460436953140015717943329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45947249270853354290591105 34460436953140015717943329)
      ·
        refine ⟨25845327714855011788457497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34460436953140015717943329 25845327714855011788457497)
        ·
          refine ⟨19383995786141258841343123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25845327714855011788457497 19383995786141258841343123)
          ·
            refine ⟨29075993679211888262014685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19383995786141258841343123 29075993679211888262014685)
            ·
              refine ⟨10903497629704458098255507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29075993679211888262014685 10903497629704458098255507)
              ·
                refine ⟨16355246444556687147383261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10903497629704458098255507 16355246444556687147383261)
                ·
                  refine ⟨6133217416708757680268723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16355246444556687147383261 6133217416708757680268723)
                  ·
                    refine ⟨9199826125063136520403085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6133217416708757680268723 9199826125063136520403085)
                    ·
                      refine ⟨3449934796898676195151157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9199826125063136520403085 3449934796898676195151157)
                      ·
                        rfl

theorem cell23_6718724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 3, 1, 3, 1, 3].length) (baseStart_6718724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6718724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6718724 prefixEnd_6718724 := by exact prefixLift 6718724
  have htrace : WordTrace (prefixWord ++ tailWord_6718724) baseStart_6718724 baseEnd_6718724 := by
    simpa [prefixWord, tailWord_6718724, baseEnd_6718724] using wordTrace_append hprefix tailTrace_6718724
  have hstable : (prefixWord ++ tailWord_6718724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6718724).length < 2 ^ (prefixWord ++ tailWord_6718724).sum := by decide
  have hdescent : baseEnd_6718724 < baseStart_6718724 := by decide
  rcases family_descends (prefixWord ++ tailWord_6718724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6718730 : List Nat := [3, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4]
def baseStart_6718730 : Nat := 118140960795 + 6718730 * 2 ^ 59
def prefixEnd_6718730 : Nat := 4983230072969 + 3 ^ 40 * 6718730 * 2
def baseEnd_6718730 : Nat := 3449937877782603171676129

theorem tailTrace_6718730 : CollatzResearch.WordTrace tailWord_6718730 prefixEnd_6718730 3449937877782603171676129 := by
  unfold tailWord_6718730
  simp only [CollatzResearch.WordTrace]
  refine ⟨61263053737299038143634411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163368143299464101716358429 61263053737299038143634411)
  ·
    refine ⟨91894580605948557215451617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61263053737299038143634411 91894580605948557215451617)
    ·
      refine ⟨68920935454461417911588713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91894580605948557215451617 68920935454461417911588713)
      ·
        refine ⟨51690701590846063433691535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68920935454461417911588713 51690701590846063433691535)
        ·
          refine ⟨77536052386269095150537303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51690701590846063433691535 77536052386269095150537303)
          ·
            refine ⟨116304078579403642725805955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77536052386269095150537303 116304078579403642725805955)
            ·
              refine ⟨174456117869105464088708933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116304078579403642725805955 174456117869105464088708933)
              ·
                refine ⟨32710522100457274516632925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 174456117869105464088708933 32710522100457274516632925)
                ·
                  refine ⟨12266445787671477943737347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32710522100457274516632925 12266445787671477943737347)
                  ·
                    refine ⟨18399668681507216915606021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12266445787671477943737347 18399668681507216915606021)
                    ·
                      refine ⟨3449937877782603171676129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18399668681507216915606021 3449937877782603171676129)
                      ·
                        rfl

theorem cell23_6718730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4].length) (baseStart_6718730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6718730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6718730 prefixEnd_6718730 := by exact prefixLift 6718730
  have htrace : WordTrace (prefixWord ++ tailWord_6718730) baseStart_6718730 baseEnd_6718730 := by
    simpa [prefixWord, tailWord_6718730, baseEnd_6718730] using wordTrace_append hprefix tailTrace_6718730
  have hstable : (prefixWord ++ tailWord_6718730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6718730).length < 2 ^ (prefixWord ++ tailWord_6718730).sum := by decide
  have hdescent : baseEnd_6718730 < baseStart_6718730 := by decide
  rcases family_descends (prefixWord ++ tailWord_6718730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6718747 : List Nat := [1, 1, 1, 1, 1, 1, 5, 3, 5, 2, 2]
def baseStart_6718747 : Nat := 118140960795 + 6718747 * 2 ^ 59
def prefixEnd_6718747 : Nat := 4983230072969 + 3 ^ 40 * 6718747 * 2
def baseEnd_6718747 : Nat := 3449946606953729605163551

theorem tailTrace_6718747 : CollatzResearch.WordTrace tailWord_6718747 prefixEnd_6718747 3449946606953729605163551 := by
  unfold tailWord_6718747
  simp only [CollatzResearch.WordTrace]
  refine ⟨245052834990134564477906495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163368556660089709651937663 245052834990134564477906495)
  ·
    refine ⟨367579252485201846716859743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245052834990134564477906495 367579252485201846716859743)
    ·
      refine ⟨551368878727802770075289615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 367579252485201846716859743 551368878727802770075289615)
      ·
        refine ⟨827053318091704155112934423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 551368878727802770075289615 827053318091704155112934423)
        ·
          refine ⟨1240579977137556232669401635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 827053318091704155112934423 1240579977137556232669401635)
          ·
            refine ⟨1860869965706334349004102453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1240579977137556232669401635 1860869965706334349004102453)
            ·
              refine ⟨174456559284968845219134605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1860869965706334349004102453 174456559284968845219134605)
              ·
                refine ⟨65421209731863316957175477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 174456559284968845219134605 65421209731863316957175477)
                ·
                  refine ⟨6133238412362185964735201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 65421209731863316957175477 6133238412362185964735201)
                  ·
                    refine ⟨4599928809271639473551401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6133238412362185964735201 4599928809271639473551401)
                    ·
                      refine ⟨3449946606953729605163551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4599928809271639473551401 3449946606953729605163551)
                      ·
                        rfl

theorem cell23_6718747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 3, 5, 2, 2].length) (baseStart_6718747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6718747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6718747 prefixEnd_6718747 := by exact prefixLift 6718747
  have htrace : WordTrace (prefixWord ++ tailWord_6718747) baseStart_6718747 baseEnd_6718747 := by
    simpa [prefixWord, tailWord_6718747, baseEnd_6718747] using wordTrace_append hprefix tailTrace_6718747
  have hstable : (prefixWord ++ tailWord_6718747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6718747).length < 2 ^ (prefixWord ++ tailWord_6718747).sum := by decide
  have hdescent : baseEnd_6718747 < baseStart_6718747 := by decide
  rcases family_descends (prefixWord ++ tailWord_6718747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6718860 : List Nat := [2, 2, 1, 2, 1, 3, 1, 4, 7]
def baseStart_6718860 : Nat := 118140960795 + 6718860 * 2 ^ 59
def prefixEnd_6718860 : Nat := 4983230072969 + 3 ^ 40 * 6718860 * 2
def baseEnd_6718860 : Nat := 383333847807520851450059

theorem tailTrace_6718860 : CollatzResearch.WordTrace tailWord_6718860 prefixEnd_6718860 383333847807520851450059 := by
  unfold tailWord_6718860
  simp only [CollatzResearch.WordTrace]
  refine ⟨122528478219362592388385017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163371304292483456517846689 122528478219362592388385017)
  ·
    refine ⟨91896358664521944291288763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122528478219362592388385017 91896358664521944291288763)
    ·
      refine ⟨137844537996782916436933145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91896358664521944291288763 137844537996782916436933145)
      ·
        refine ⟨103383403497587187327699859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137844537996782916436933145 103383403497587187327699859)
        ·
          refine ⟨155075105246380780991549789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103383403497587187327699859 155075105246380780991549789)
          ·
            refine ⟨58153164467392792871831171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 155075105246380780991549789 58153164467392792871831171)
            ·
              refine ⟨87229746701089189307746757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58153164467392792871831171 87229746701089189307746757)
              ·
                refine ⟨16355577506454222995202517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 87229746701089189307746757 16355577506454222995202517)
                ·
                  refine ⟨383333847807520851450059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16355577506454222995202517 383333847807520851450059)
                  ·
                    rfl

theorem cell23_6718860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 4, 7].length) (baseStart_6718860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6718860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6718860 prefixEnd_6718860 := by exact prefixLift 6718860
  have htrace : WordTrace (prefixWord ++ tailWord_6718860) baseStart_6718860 baseEnd_6718860 := by
    simpa [prefixWord, tailWord_6718860, baseEnd_6718860] using wordTrace_append hprefix tailTrace_6718860
  have hstable : (prefixWord ++ tailWord_6718860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6718860).length < 2 ^ (prefixWord ++ tailWord_6718860).sum := by decide
  have hdescent : baseEnd_6718860 < baseStart_6718860 := by decide
  rcases family_descends (prefixWord ++ tailWord_6718860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6718905 : List Nat := [1, 2, 1, 4, 4, 2, 2, 1, 2, 2, 2]
def baseStart_6718905 : Nat := 118140960795 + 6718905 * 2 ^ 59
def prefixEnd_6718905 : Nat := 4983230072969 + 3 ^ 40 * 6718905 * 2
def baseEnd_6718905 : Nat := 3450027736897139986987825

theorem tailTrace_6718905 : CollatzResearch.WordTrace tailWord_6718905 prefixEnd_6718905 3450027736897139986987825 := by
  unfold tailWord_6718905
  simp only [CollatzResearch.WordTrace]
  refine ⟨245058597723562157462158169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163372398482374771641438779 245058597723562157462158169)
  ·
    refine ⟨183793948292671618096618627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245058597723562157462158169 183793948292671618096618627)
    ·
      refine ⟨275690922439007427144927941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183793948292671618096618627 275690922439007427144927941)
      ·
        refine ⟨51692047957313892589673989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 275690922439007427144927941 51692047957313892589673989)
        ·
          refine ⟨9692258991996354860563873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51692047957313892589673989 9692258991996354860563873)
          ·
            refine ⟨7269194243997266145422905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9692258991996354860563873 7269194243997266145422905)
            ·
              refine ⟨5451895682997949609067179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7269194243997266145422905 5451895682997949609067179)
              ·
                refine ⟨8177843524496924413600769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5451895682997949609067179 8177843524496924413600769)
                ·
                  refine ⟨6133382643372693310200577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8177843524496924413600769 6133382643372693310200577)
                  ·
                    refine ⟨4600036982529519982650433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6133382643372693310200577 4600036982529519982650433)
                    ·
                      refine ⟨3450027736897139986987825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4600036982529519982650433 3450027736897139986987825)
                      ·
                        rfl

theorem cell23_6718905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 2, 1, 2, 2, 2].length) (baseStart_6718905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6718905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6718905 prefixEnd_6718905 := by exact prefixLift 6718905
  have htrace : WordTrace (prefixWord ++ tailWord_6718905) baseStart_6718905 baseEnd_6718905 := by
    simpa [prefixWord, tailWord_6718905, baseEnd_6718905] using wordTrace_append hprefix tailTrace_6718905
  have hstable : (prefixWord ++ tailWord_6718905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6718905).length < 2 ^ (prefixWord ++ tailWord_6718905).sum := by decide
  have hdescent : baseEnd_6718905 < baseStart_6718905 := by decide
  rcases family_descends (prefixWord ++ tailWord_6718905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6718924 : List Nat := [2, 2, 1, 4, 2, 2, 2, 1, 2, 5]
def baseStart_6718924 : Nat := 118140960795 + 6718924 * 2 ^ 59
def prefixEnd_6718924 : Nat := 4983230072969 + 3 ^ 40 * 6718924 * 2
def baseEnd_6718924 : Nat := 1150012497676525137550079

theorem tailTrace_6718924 : CollatzResearch.WordTrace tailWord_6718924 prefixEnd_6718924 1150012497676525137550079 := by
  unfold tailWord_6718924
  simp only [CollatzResearch.WordTrace]
  refine ⟨122529645355246661853549913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163372860473662215804733217 122529645355246661853549913)
  ·
    refine ⟨91897234016434996390162435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122529645355246661853549913 91897234016434996390162435)
    ·
      refine ⟨137845851024652494585243653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91897234016434996390162435 137845851024652494585243653)
      ·
        refine ⟨25846097067122342734733185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 137845851024652494585243653 25846097067122342734733185)
        ·
          refine ⟨19384572800341757051049889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25846097067122342734733185 19384572800341757051049889)
          ·
            refine ⟨14538429600256317788287417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19384572800341757051049889 14538429600256317788287417)
            ·
              refine ⟨10903822200192238341215563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14538429600256317788287417 10903822200192238341215563)
              ·
                refine ⟨16355733300288357511823345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10903822200192238341215563 16355733300288357511823345)
                ·
                  refine ⟨12266799975216268133867509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16355733300288357511823345 12266799975216268133867509)
                  ·
                    refine ⟨1150012497676525137550079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12266799975216268133867509 1150012497676525137550079)
                    ·
                      rfl

theorem cell23_6718924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 2, 1, 2, 5].length) (baseStart_6718924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6718924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6718924 prefixEnd_6718924 := by exact prefixLift 6718924
  have htrace : WordTrace (prefixWord ++ tailWord_6718924) baseStart_6718924 baseEnd_6718924 := by
    simpa [prefixWord, tailWord_6718924, baseEnd_6718924] using wordTrace_append hprefix tailTrace_6718924
  have hstable : (prefixWord ++ tailWord_6718924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6718924).length < 2 ^ (prefixWord ++ tailWord_6718924).sum := by decide
  have hdescent : baseEnd_6718924 < baseStart_6718924 := by decide
  rcases family_descends (prefixWord ++ tailWord_6718924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6718927 : List Nat := [1, 1, 2, 1, 1, 4, 3, 3, 2, 1, 4]
def baseStart_6718927 : Nat := 118140960795 + 6718927 * 2 ^ 59
def prefixEnd_6718927 : Nat := 4983230072969 + 3 ^ 40 * 6718927 * 2
def baseEnd_6718927 : Nat := 3450039033471538900912723

theorem tailTrace_6718927 : CollatzResearch.WordTrace tailWord_6718927 prefixEnd_6718927 3450039033471538900912723 := by
  unfold tailWord_6718927
  simp only [CollatzResearch.WordTrace]
  refine ⟨245059400129482455219459035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163372933419654970146306023 245059400129482455219459035)
  ·
    refine ⟨367589100194223682829188553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245059400129482455219459035 367589100194223682829188553)
    ·
      refine ⟨275691825145667762121891415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 367589100194223682829188553 275691825145667762121891415)
      ·
        refine ⟨413537737718501643182837123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275691825145667762121891415 413537737718501643182837123)
        ·
          refine ⟨620306606577752464774255685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 413537737718501643182837123 620306606577752464774255685)
          ·
            refine ⟨116307488733328587145172941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 620306606577752464774255685 116307488733328587145172941)
            ·
              refine ⟨43615308274998220179439853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 116307488733328587145172941 43615308274998220179439853)
              ·
                refine ⟨16355740603124332567289945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43615308274998220179439853 16355740603124332567289945)
                ·
                  refine ⟨12266805452343249425467459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16355740603124332567289945 12266805452343249425467459)
                  ·
                    refine ⟨18400208178514874138201189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12266805452343249425467459 18400208178514874138201189)
                    ·
                      refine ⟨3450039033471538900912723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18400208178514874138201189 3450039033471538900912723)
                      ·
                        rfl

theorem cell23_6718927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 3, 2, 1, 4].length) (baseStart_6718927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6718927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6718927 prefixEnd_6718927 := by exact prefixLift 6718927
  have htrace : WordTrace (prefixWord ++ tailWord_6718927) baseStart_6718927 baseEnd_6718927 := by
    simpa [prefixWord, tailWord_6718927, baseEnd_6718927] using wordTrace_append hprefix tailTrace_6718927
  have hstable : (prefixWord ++ tailWord_6718927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6718927).length < 2 ^ (prefixWord ++ tailWord_6718927).sum := by decide
  have hdescent : baseEnd_6718927 < baseStart_6718927 := by decide
  rcases family_descends (prefixWord ++ tailWord_6718927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6718934 : List Nat := [5, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5]
def baseStart_6718934 : Nat := 118140960795 + 6718934 * 2 ^ 59
def prefixEnd_6718934 : Nat := 4983230072969 + 3 ^ 40 * 6718934 * 2
def baseEnd_6718934 : Nat := 3450042627836120373525191

theorem tailTrace_6718934 : CollatzResearch.WordTrace tailWord_6718934 prefixEnd_6718934 3450042627836120373525191 := by
  unfold tailWord_6718934
  simp only [CollatzResearch.WordTrace]
  refine ⟨15316228465028568463435241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 163373103626971396943309237 15316228465028568463435241)
  ·
    refine ⟨11487171348771426347576431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15316228465028568463435241 11487171348771426347576431)
    ·
      refine ⟨17230757023157139521364647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11487171348771426347576431 17230757023157139521364647)
      ·
        refine ⟨25846135534735709282046971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17230757023157139521364647 25846135534735709282046971)
        ·
          refine ⟨38769203302103563923070457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25846135534735709282046971 38769203302103563923070457)
          ·
            refine ⟨29076902476577672942302843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38769203302103563923070457 29076902476577672942302843)
            ·
              refine ⟨43615353714866509413454265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29076902476577672942302843 43615353714866509413454265)
              ·
                refine ⟨32711515286149882060090699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43615353714866509413454265 32711515286149882060090699)
                ·
                  refine ⟨49067272929224823090136049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32711515286149882060090699 49067272929224823090136049)
                  ·
                    refine ⟨36800454696918617317602037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49067272929224823090136049 36800454696918617317602037)
                    ·
                      refine ⟨3450042627836120373525191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36800454696918617317602037 3450042627836120373525191)
                      ·
                        rfl

theorem cell23_6718934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5].length) (baseStart_6718934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6718934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6718934 prefixEnd_6718934 := by exact prefixLift 6718934
  have htrace : WordTrace (prefixWord ++ tailWord_6718934) baseStart_6718934 baseEnd_6718934 := by
    simpa [prefixWord, tailWord_6718934, baseEnd_6718934] using wordTrace_append hprefix tailTrace_6718934
  have hstable : (prefixWord ++ tailWord_6718934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6718934).length < 2 ^ (prefixWord ++ tailWord_6718934).sum := by decide
  have hdescent : baseEnd_6718934 < baseStart_6718934 := by decide
  rcases family_descends (prefixWord ++ tailWord_6718934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6718978 : List Nat := [3, 4, 1, 2, 1, 3, 1, 1, 2, 1, 4]
def baseStart_6718978 : Nat := 118140960795 + 6718978 * 2 ^ 59
def prefixEnd_6718978 : Nat := 4983230072969 + 3 ^ 40 * 6718978 * 2
def baseEnd_6718978 : Nat := 3450065220984918201374989

theorem tailTrace_6718978 : CollatzResearch.WordTrace tailWord_6718978 prefixEnd_6718978 3450065220984918201374989 := by
  unfold tailWord_6718978
  simp only [CollatzResearch.WordTrace]
  refine ⟨61265315063074422732391397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163374173501531793953043725 61265315063074422732391397)
  ·
    refine ⟨11487246574326454262323387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61265315063074422732391397 11487246574326454262323387)
    ·
      refine ⟨17230869861489681393485081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11487246574326454262323387 17230869861489681393485081)
      ·
        refine ⟨12923152396117261045113811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17230869861489681393485081 12923152396117261045113811)
        ·
          refine ⟨19384728594175891567670717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12923152396117261045113811 19384728594175891567670717)
          ·
            refine ⟨7269273222815959337876519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19384728594175891567670717 7269273222815959337876519)
            ·
              refine ⟨10903909834223939006814779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7269273222815959337876519 10903909834223939006814779)
              ·
                refine ⟨16355864751335908510222169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10903909834223939006814779 16355864751335908510222169)
                ·
                  refine ⟨12266898563501931382666627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16355864751335908510222169 12266898563501931382666627)
                  ·
                    refine ⟨18400347845252897073999941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12266898563501931382666627 18400347845252897073999941)
                    ·
                      refine ⟨3450065220984918201374989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18400347845252897073999941 3450065220984918201374989)
                      ·
                        rfl

theorem cell23_6718978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 1, 1, 2, 1, 4].length) (baseStart_6718978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6718978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6718978 prefixEnd_6718978 := by exact prefixLift 6718978
  have htrace : WordTrace (prefixWord ++ tailWord_6718978) baseStart_6718978 baseEnd_6718978 := by
    simpa [prefixWord, tailWord_6718978, baseEnd_6718978] using wordTrace_append hprefix tailTrace_6718978
  have hstable : (prefixWord ++ tailWord_6718978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6718978).length < 2 ^ (prefixWord ++ tailWord_6718978).sum := by decide
  have hdescent : baseEnd_6718978 < baseStart_6718978 := by decide
  rcases family_descends (prefixWord ++ tailWord_6718978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6718988 : List Nat := [2, 2, 1, 2, 5, 1, 2, 3, 1, 4]
def baseStart_6718988 : Nat := 118140960795 + 6718988 * 2 ^ 59
def prefixEnd_6718988 : Nat := 4983230072969 + 3 ^ 40 * 6718988 * 2
def baseEnd_6718988 : Nat := 1150023451930487720749981

theorem tailTrace_6718988 : CollatzResearch.WordTrace tailWord_6718988 prefixEnd_6718988 1150023451930487720749981 := by
  unfold tailWord_6718988
  simp only [CollatzResearch.WordTrace]
  refine ⟨122530812491130731318714809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163374416654840975091619745 122530812491130731318714809)
  ·
    refine ⟨91898109368348048489036107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122530812491130731318714809 91898109368348048489036107)
    ·
      refine ⟨137847164052522072733554161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91898109368348048489036107 137847164052522072733554161)
      ·
        refine ⟨103385373039391554550165621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137847164052522072733554161 103385373039391554550165621)
        ·
          refine ⟨9692378722442958239078027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 103385373039391554550165621 9692378722442958239078027)
          ·
            refine ⟨14538568083664437358617041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9692378722442958239078027 14538568083664437358617041)
            ·
              refine ⟨10903926062748328018962781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14538568083664437358617041 10903926062748328018962781)
              ·
                refine ⟨4088972273530623007111043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10903926062748328018962781 4088972273530623007111043)
                ·
                  refine ⟨6133458410295934510666565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4088972273530623007111043 6133458410295934510666565)
                  ·
                    refine ⟨1150023451930487720749981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6133458410295934510666565 1150023451930487720749981)
                    ·
                      rfl

theorem cell23_6718988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 2, 3, 1, 4].length) (baseStart_6718988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6718988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6718988 prefixEnd_6718988 := by exact prefixLift 6718988
  have htrace : WordTrace (prefixWord ++ tailWord_6718988) baseStart_6718988 baseEnd_6718988 := by
    simpa [prefixWord, tailWord_6718988, baseEnd_6718988] using wordTrace_append hprefix tailTrace_6718988
  have hstable : (prefixWord ++ tailWord_6718988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6718988).length < 2 ^ (prefixWord ++ tailWord_6718988).sum := by decide
  have hdescent : baseEnd_6718988 < baseStart_6718988 := by decide
  rcases family_descends (prefixWord ++ tailWord_6718988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6719034 : List Nat := [3, 1, 1, 1, 3, 2, 1, 1, 2, 6, 2]
def baseStart_6719034 : Nat := 118140960795 + 6719034 * 2 ^ 59
def prefixEnd_6719034 : Nat := 4983230072969 + 3 ^ 40 * 6719034 * 2
def baseEnd_6719034 : Nat := 3450093975901569982274731

theorem tailTrace_6719034 : CollatzResearch.WordTrace tailWord_6719034 prefixEnd_6719034 3450093975901569982274731 := by
  unfold tailWord_6719034
  simp only [CollatzResearch.WordTrace]
  refine ⟨61265825685023703123401039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163375535160063208329069437 61265825685023703123401039)
  ·
    refine ⟨91898738527535554685101559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61265825685023703123401039 91898738527535554685101559)
    ·
      refine ⟨137848107791303332027652339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91898738527535554685101559 137848107791303332027652339)
      ·
        refine ⟨206772161686954998041478509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137848107791303332027652339 206772161686954998041478509)
        ·
          refine ⟨77539560632608124265554441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 206772161686954998041478509 77539560632608124265554441)
          ·
            refine ⟨58154670474456093199165831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77539560632608124265554441 58154670474456093199165831)
            ·
              refine ⟨87232005711684139798748747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58154670474456093199165831 87232005711684139798748747)
              ·
                refine ⟨130848008567526209698123121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87232005711684139798748747 130848008567526209698123121)
                ·
                  refine ⟨98136006425644657273592341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 130848008567526209698123121 98136006425644657273592341)
                  ·
                    refine ⟨4600125301202093309699641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 98136006425644657273592341 4600125301202093309699641)
                    ·
                      refine ⟨3450093975901569982274731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4600125301202093309699641 3450093975901569982274731)
                      ·
                        rfl

theorem cell23_6719034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 1, 2, 6, 2].length) (baseStart_6719034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6719034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6719034 prefixEnd_6719034 := by exact prefixLift 6719034
  have htrace : WordTrace (prefixWord ++ tailWord_6719034) baseStart_6719034 baseEnd_6719034 := by
    simpa [prefixWord, tailWord_6719034, baseEnd_6719034] using wordTrace_append hprefix tailTrace_6719034
  have hstable : (prefixWord ++ tailWord_6719034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6719034).length < 2 ^ (prefixWord ++ tailWord_6719034).sum := by decide
  have hdescent : baseEnd_6719034 < baseStart_6719034 := by decide
  rcases family_descends (prefixWord ++ tailWord_6719034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6719054 : List Nat := [4, 1, 1, 1, 1, 2, 1, 2, 5, 2, 3]
def baseStart_6719054 : Nat := 118140960795 + 6719054 * 2 ^ 59
def prefixEnd_6719054 : Nat := 4983230072969 + 3 ^ 40 * 6719054 * 2
def baseEnd_6719054 : Nat := 3450104245514659904024639

theorem tailTrace_6719054 : CollatzResearch.WordTrace tailWord_6719054 prefixEnd_6719054 3450104245514659904024639 := by
  unfold tailWord_6719054
  simp only [CollatzResearch.WordTrace]
  refine ⟨30633004025002794488666527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 163376021466681570606221477 30633004025002794488666527)
  ·
    refine ⟨45949506037504191732999791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30633004025002794488666527 45949506037504191732999791)
    ·
      refine ⟨68924259056256287599499687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45949506037504191732999791 68924259056256287599499687)
      ·
        refine ⟨103386388584384431399249531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68924259056256287599499687 103386388584384431399249531)
        ·
          refine ⟨155079582876576647098874297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103386388584384431399249531 155079582876576647098874297)
          ·
            refine ⟨116309687157432485324155723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 155079582876576647098874297 116309687157432485324155723)
            ·
              refine ⟨174464530736148727986233585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116309687157432485324155723 174464530736148727986233585)
              ·
                refine ⟨130848398052111545989675189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 174464530736148727986233585 130848398052111545989675189)
                ·
                  refine ⟨12267037317385457436532049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 130848398052111545989675189 12267037317385457436532049)
                  ·
                    refine ⟨9200277988039093077399037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12267037317385457436532049 9200277988039093077399037)
                    ·
                      refine ⟨3450104245514659904024639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9200277988039093077399037 3450104245514659904024639)
                      ·
                        rfl

theorem cell23_6719054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 2, 5, 2, 3].length) (baseStart_6719054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6719054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6719054 prefixEnd_6719054 := by exact prefixLift 6719054
  have htrace : WordTrace (prefixWord ++ tailWord_6719054) baseStart_6719054 baseEnd_6719054 := by
    simpa [prefixWord, tailWord_6719054, baseEnd_6719054] using wordTrace_append hprefix tailTrace_6719054
  have hstable : (prefixWord ++ tailWord_6719054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6719054).length < 2 ^ (prefixWord ++ tailWord_6719054).sum := by decide
  have hdescent : baseEnd_6719054 < baseStart_6719054 := by decide
  rcases family_descends (prefixWord ++ tailWord_6719054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6719084 : List Nat := [2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 3]
def baseStart_6719084 : Nat := 118140960795 + 6719084 * 2 ^ 59
def prefixEnd_6719084 : Nat := 4983230072969 + 3 ^ 40 * 6719084 * 2
def baseEnd_6719084 : Nat := 3450119649934294786649501

theorem tailTrace_6719084 : CollatzResearch.WordTrace tailWord_6719084 prefixEnd_6719084 3450119649934294786649501 := by
  unfold tailWord_6719084
  simp only [CollatzResearch.WordTrace]
  refine ⟨122532563194956835516462153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163376750926609114021949537 122532563194956835516462153)
  ·
    refine ⟨91899422396217626637346615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122532563194956835516462153 91899422396217626637346615)
    ·
      refine ⟨137849133594326439956019923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91899422396217626637346615 137849133594326439956019923)
      ·
        refine ⟨206773700391489659934029885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137849133594326439956019923 206773700391489659934029885)
        ·
          refine ⟨77540137646808622475261207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 206773700391489659934029885 77540137646808622475261207)
          ·
            refine ⟨116310206470212933712891811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77540137646808622475261207 116310206470212933712891811)
            ·
              refine ⟨174465309705319400569337717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116310206470212933712891811 174465309705319400569337717)
              ·
                refine ⟨16356122784873693803375411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 174465309705319400569337717 16356122784873693803375411)
                ·
                  refine ⟨24534184177310540705063117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16356122784873693803375411 24534184177310540705063117)
                  ·
                    refine ⟨9200319066491452764398669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24534184177310540705063117 9200319066491452764398669)
                    ·
                      refine ⟨3450119649934294786649501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9200319066491452764398669 3450119649934294786649501)
                      ·
                        rfl

theorem cell23_6719084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 3].length) (baseStart_6719084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6719084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6719084 prefixEnd_6719084 := by exact prefixLift 6719084
  have htrace : WordTrace (prefixWord ++ tailWord_6719084) baseStart_6719084 baseEnd_6719084 := by
    simpa [prefixWord, tailWord_6719084, baseEnd_6719084] using wordTrace_append hprefix tailTrace_6719084
  have hstable : (prefixWord ++ tailWord_6719084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6719084).length < 2 ^ (prefixWord ++ tailWord_6719084).sum := by decide
  have hdescent : baseEnd_6719084 < baseStart_6719084 := by decide
  rcases family_descends (prefixWord ++ tailWord_6719084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6719085 : List Nat := [1, 5, 1, 1, 5, 1, 1, 2, 1, 1, 4]
def baseStart_6719085 : Nat := 118140960795 + 6719085 * 2 ^ 59
def prefixEnd_6719085 : Nat := 4983230072969 + 3 ^ 40 * 6719085 * 2
def baseEnd_6719085 : Nat := 3450120163414949282736997

theorem tailTrace_6719085 : CollatzResearch.WordTrace tailWord_6719085 prefixEnd_6719085 3450120163414949282736997 := by
  unfold tailWord_6719085
  simp only [CollatzResearch.WordTrace]
  refine ⟨245065162862910048203710709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163376775241940032135807139 245065162862910048203710709)
  ·
    refine ⟨22974859018397817019097879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 245065162862910048203710709 22974859018397817019097879)
    ·
      refine ⟨34462288527596725528646819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22974859018397817019097879 34462288527596725528646819)
      ·
        refine ⟨51693432791395088292970229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34462288527596725528646819 51693432791395088292970229)
        ·
          refine ⟨4846259324193289527465959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 51693432791395088292970229 4846259324193289527465959)
          ·
            refine ⟨7269388986289934291198939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4846259324193289527465959 7269388986289934291198939)
            ·
              refine ⟨10904083479434901436798409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7269388986289934291198939 10904083479434901436798409)
              ·
                refine ⟨8178062609576176077598807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10904083479434901436798409 8178062609576176077598807)
                ·
                  refine ⟨12267093914364264116398211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8178062609576176077598807 12267093914364264116398211)
                  ·
                    refine ⟨18400640871546396174597317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12267093914364264116398211 18400640871546396174597317)
                    ·
                      refine ⟨3450120163414949282736997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18400640871546396174597317 3450120163414949282736997)
                      ·
                        rfl

theorem cell23_6719085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 1, 2, 1, 1, 4].length) (baseStart_6719085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6719085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6719085 prefixEnd_6719085 := by exact prefixLift 6719085
  have htrace : WordTrace (prefixWord ++ tailWord_6719085) baseStart_6719085 baseEnd_6719085 := by
    simpa [prefixWord, tailWord_6719085, baseEnd_6719085] using wordTrace_append hprefix tailTrace_6719085
  have hstable : (prefixWord ++ tailWord_6719085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6719085).length < 2 ^ (prefixWord ++ tailWord_6719085).sum := by decide
  have hdescent : baseEnd_6719085 < baseStart_6719085 := by decide
  rcases family_descends (prefixWord ++ tailWord_6719085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6719088 : List Nat := [2, 1, 1, 1, 6, 3, 1, 2, 1, 2, 3]
def baseStart_6719088 : Nat := 118140960795 + 6719088 * 2 ^ 59
def prefixEnd_6719088 : Nat := 4983230072969 + 3 ^ 40 * 6719088 * 2
def baseEnd_6719088 : Nat := 3450121703856912770999483

theorem tailTrace_6719088 : CollatzResearch.WordTrace tailWord_6719088 prefixEnd_6719088 3450121703856912770999483 := by
  unfold tailWord_6719088
  simp only [CollatzResearch.WordTrace]
  refine ⟨122532636140949589858034959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163376848187932786477379945 122532636140949589858034959)
  ·
    refine ⟨183798954211424384787052439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122532636140949589858034959 183798954211424384787052439)
    ·
      refine ⟨275698431317136577180578659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183798954211424384787052439 275698431317136577180578659)
      ·
        refine ⟨413547646975704865770867989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275698431317136577180578659 413547646975704865770867989)
        ·
          refine ⟨19385045951986165583009437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 413547646975704865770867989 19385045951986165583009437)
          ·
            refine ⟨7269392231994812093628539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19385045951986165583009437 7269392231994812093628539)
            ·
              refine ⟨10904088347992218140442809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7269392231994812093628539 10904088347992218140442809)
              ·
                refine ⟨8178066260994163605332107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10904088347992218140442809 8178066260994163605332107)
                ·
                  refine ⟨12267099391491245407998161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8178066260994163605332107 12267099391491245407998161)
                  ·
                    refine ⟨9200324543618434055998621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12267099391491245407998161 9200324543618434055998621)
                    ·
                      refine ⟨3450121703856912770999483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9200324543618434055998621 3450121703856912770999483)
                      ·
                        rfl

theorem cell23_6719088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 1, 2, 1, 2, 3].length) (baseStart_6719088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6719088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6719088 prefixEnd_6719088 := by exact prefixLift 6719088
  have htrace : WordTrace (prefixWord ++ tailWord_6719088) baseStart_6719088 baseEnd_6719088 := by
    simpa [prefixWord, tailWord_6719088, baseEnd_6719088] using wordTrace_append hprefix tailTrace_6719088
  have hstable : (prefixWord ++ tailWord_6719088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6719088).length < 2 ^ (prefixWord ++ tailWord_6719088).sum := by decide
  have hdescent : baseEnd_6719088 < baseStart_6719088 := by decide
  rcases family_descends (prefixWord ++ tailWord_6719088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6719101 : List Nat := [1, 4, 1, 1, 4, 2, 1, 2, 1, 3, 3]
def baseStart_6719101 : Nat := 118140960795 + 6719101 * 2 ^ 59
def prefixEnd_6719101 : Nat := 4983230072969 + 3 ^ 40 * 6719101 * 2
def baseEnd_6719101 : Nat := 3450128379105421220136923

theorem tailTrace_6719101 : CollatzResearch.WordTrace tailWord_6719101 prefixEnd_6719101 3450128379105421220136923 := by
  unfold tailWord_6719101
  simp only [CollatzResearch.WordTrace]
  refine ⟨245065746430852082936293157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163377164287234721957528771 245065746430852082936293157)
  ·
    refine ⟨45949827455784765550554967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 245065746430852082936293157 45949827455784765550554967)
    ·
      refine ⟨68924741183677148325832451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45949827455784765550554967 68924741183677148325832451)
      ·
        refine ⟨103387111775515722488748677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68924741183677148325832451 103387111775515722488748677)
        ·
          refine ⟨19385083457909197966640377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 103387111775515722488748677 19385083457909197966640377)
          ·
            refine ⟨14538812593431898474980283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19385083457909197966640377 14538812593431898474980283)
            ·
              refine ⟨21808218890147847712470425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14538812593431898474980283 21808218890147847712470425)
              ·
                refine ⟨16356164167610885784352819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21808218890147847712470425 16356164167610885784352819)
                ·
                  refine ⟨24534246251416328676529229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16356164167610885784352819 24534246251416328676529229)
                  ·
                    refine ⟨9200342344281123253698461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24534246251416328676529229 9200342344281123253698461)
                    ·
                      refine ⟨3450128379105421220136923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9200342344281123253698461 3450128379105421220136923)
                      ·
                        rfl

theorem cell23_6719101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 2, 1, 3, 3].length) (baseStart_6719101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6719101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6719101 prefixEnd_6719101 := by exact prefixLift 6719101
  have htrace : WordTrace (prefixWord ++ tailWord_6719101) baseStart_6719101 baseEnd_6719101 := by
    simpa [prefixWord, tailWord_6719101, baseEnd_6719101] using wordTrace_append hprefix tailTrace_6719101
  have hstable : (prefixWord ++ tailWord_6719101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6719101).length < 2 ^ (prefixWord ++ tailWord_6719101).sum := by decide
  have hdescent : baseEnd_6719101 < baseStart_6719101 := by decide
  rcases family_descends (prefixWord ++ tailWord_6719101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6719118 : List Nat := [4, 1, 1, 3, 1, 2, 1, 4, 2, 1, 3]
def baseStart_6719118 : Nat := 118140960795 + 6719118 * 2 ^ 59
def prefixEnd_6719118 : Nat := 4983230072969 + 3 ^ 40 * 6719118 * 2
def baseEnd_6719118 : Nat := 3450137108276547653624345

theorem tailTrace_6719118 : CollatzResearch.WordTrace tailWord_6719118 prefixEnd_6719118 3450137108276547653624345 := by
  unfold tailWord_6719118
  simp only [CollatzResearch.WordTrace]
  refine ⟨30633295808973811854957751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 163377577647860329893108005 30633295808973811854957751)
  ·
    refine ⟨45949943713460717782436627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30633295808973811854957751 45949943713460717782436627)
    ·
      refine ⟨68924915570191076673654941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45949943713460717782436627 68924915570191076673654941)
      ·
        refine ⟨25846843338821653752620603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68924915570191076673654941 25846843338821653752620603)
        ·
          refine ⟨38770265008232480628930905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25846843338821653752620603 38770265008232480628930905)
          ·
            refine ⟨29077698756174360471698179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38770265008232480628930905 29077698756174360471698179)
            ·
              refine ⟨43616548134261540707547269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29077698756174360471698179 43616548134261540707547269)
              ·
                refine ⟨8178102775174038882665113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43616548134261540707547269 8178102775174038882665113)
                ·
                  refine ⟨6133577081380529161998835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8178102775174038882665113 6133577081380529161998835)
                  ·
                    refine ⟨9200365622070793742998253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6133577081380529161998835 9200365622070793742998253)
                    ·
                      refine ⟨3450137108276547653624345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9200365622070793742998253 3450137108276547653624345)
                      ·
                        rfl

theorem cell23_6719118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 4, 2, 1, 3].length) (baseStart_6719118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6719118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6719118 prefixEnd_6719118 := by exact prefixLift 6719118
  have htrace : WordTrace (prefixWord ++ tailWord_6719118) baseStart_6719118 baseEnd_6719118 := by
    simpa [prefixWord, tailWord_6719118, baseEnd_6719118] using wordTrace_append hprefix tailTrace_6719118
  have hstable : (prefixWord ++ tailWord_6719118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6719118).length < 2 ^ (prefixWord ++ tailWord_6719118).sum := by decide
  have hdescent : baseEnd_6719118 < baseStart_6719118 := by decide
  rcases family_descends (prefixWord ++ tailWord_6719118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6719141 : List Nat := [1, 3, 1, 2, 1, 2, 3, 3, 1, 4, 2]
def baseStart_6719141 : Nat := 118140960795 + 6719141 * 2 ^ 59
def prefixEnd_6719141 : Nat := 4983230072969 + 3 ^ 40 * 6719141 * 2
def baseEnd_6719141 : Nat := 3450148918331601063636739

theorem tailTrace_6719141 : CollatzResearch.WordTrace tailWord_6719141 prefixEnd_6719141 3450148918331601063636739 := by
  unfold tailWord_6719141
  simp only [CollatzResearch.WordTrace]
  refine ⟨245067205350707169767749277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163378136900471446511832851 245067205350707169767749277)
  ·
    refine ⟨91900202006515188662905979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 245067205350707169767749277 91900202006515188662905979)
    ·
      refine ⟨137850303009772782994358969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91900202006515188662905979 137850303009772782994358969)
      ·
        refine ⟨103387727257329587245769227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137850303009772782994358969 103387727257329587245769227)
        ·
          refine ⟨155081590885994380868653841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103387727257329587245769227 155081590885994380868653841)
          ·
            refine ⟨116311193164495785651490381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 155081590885994380868653841 116311193164495785651490381)
            ·
              refine ⟨43616697436685919619308893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 116311193164495785651490381 43616697436685919619308893)
              ·
                refine ⟨16356261538757219857240835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43616697436685919619308893 16356261538757219857240835)
                ·
                  refine ⟨24534392308135829785861253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16356261538757219857240835 24534392308135829785861253)
                  ·
                    refine ⟨4600198557775468084848985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24534392308135829785861253 4600198557775468084848985)
                    ·
                      refine ⟨3450148918331601063636739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4600198557775468084848985 3450148918331601063636739)
                      ·
                        rfl

theorem cell23_6719141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 3, 1, 4, 2].length) (baseStart_6719141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6719141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6719141 prefixEnd_6719141 := by exact prefixLift 6719141
  have htrace : WordTrace (prefixWord ++ tailWord_6719141) baseStart_6719141 baseEnd_6719141 := by
    simpa [prefixWord, tailWord_6719141, baseEnd_6719141] using wordTrace_append hprefix tailTrace_6719141
  have hstable : (prefixWord ++ tailWord_6719141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6719141).length < 2 ^ (prefixWord ++ tailWord_6719141).sum := by decide
  have hdescent : baseEnd_6719141 < baseStart_6719141 := by decide
  rcases family_descends (prefixWord ++ tailWord_6719141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6719194 : List Nat := [3, 1, 1, 2, 2, 3, 1, 2, 1, 7]
def baseStart_6719194 : Nat := 118140960795 + 6719194 * 2 ^ 59
def prefixEnd_6719194 : Nat := 4983230072969 + 3 ^ 40 * 6719194 * 2
def baseEnd_6719194 : Nat := 1150058710935429785424665

theorem tailTrace_6719194 : CollatzResearch.WordTrace tailWord_6719194 prefixEnd_6719194 1150058710935429785424665 := by
  unfold tailWord_6719194
  simp only [CollatzResearch.WordTrace]
  refine ⟨61267284604878789954857159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163379425613010106546285757 61267284604878789954857159)
  ·
    refine ⟨91900926907318184932285739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61267284604878789954857159 91900926907318184932285739)
    ·
      refine ⟨137851390360977277398428609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91900926907318184932285739 137851390360977277398428609)
      ·
        refine ⟨103388542770732958048821457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137851390360977277398428609 103388542770732958048821457)
        ·
          refine ⟨77541407078049718536616093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103388542770732958048821457 77541407078049718536616093)
          ·
            refine ⟨29078027654268644451231035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77541407078049718536616093 29078027654268644451231035)
            ·
              refine ⟨43617041481402966676846553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29078027654268644451231035 43617041481402966676846553)
              ·
                refine ⟨32712781111052225007634915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43617041481402966676846553 32712781111052225007634915)
                ·
                  refine ⟨49069171666578337511452373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32712781111052225007634915 49069171666578337511452373)
                  ·
                    refine ⟨1150058710935429785424665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49069171666578337511452373 1150058710935429785424665)
                    ·
                      rfl

theorem cell23_6719194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 2, 1, 7].length) (baseStart_6719194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6719194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6719194 prefixEnd_6719194 := by exact prefixLift 6719194
  have htrace : WordTrace (prefixWord ++ tailWord_6719194) baseStart_6719194 baseEnd_6719194 := by
    simpa [prefixWord, tailWord_6719194, baseEnd_6719194] using wordTrace_append hprefix tailTrace_6719194
  have hstable : (prefixWord ++ tailWord_6719194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6719194).length < 2 ^ (prefixWord ++ tailWord_6719194).sum := by decide
  have hdescent : baseEnd_6719194 < baseStart_6719194 := by decide
  rcases family_descends (prefixWord ++ tailWord_6719194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6719231 : List Nat := [1, 1, 2, 2, 1, 3, 2, 1, 4, 4, 2]
def baseStart_6719231 : Nat := 118140960795 + 6719231 * 2 ^ 59
def prefixEnd_6719231 : Nat := 4983230072969 + 3 ^ 40 * 6719231 * 2
def baseEnd_6719231 : Nat := 3450195131590505711511325

theorem tailTrace_6719231 : CollatzResearch.WordTrace tailWord_6719231 prefixEnd_6719231 3450195131590505711511325 := by
  unfold tailWord_6719231
  simp only [CollatzResearch.WordTrace]
  refine ⟨245070487920381115138525547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163380325280254076759017031 245070487920381115138525547)
  ·
    refine ⟨367605731880571672707788321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245070487920381115138525547 367605731880571672707788321)
    ·
      refine ⟨275704298910428754530841241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 367605731880571672707788321 275704298910428754530841241)
      ·
        refine ⟨206778224182821565898130931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 275704298910428754530841241 206778224182821565898130931)
        ·
          refine ⟨310167336274232348847196397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206778224182821565898130931 310167336274232348847196397)
          ·
            refine ⟨116312751102837130817698649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 310167336274232348847196397 116312751102837130817698649)
            ·
              refine ⟨87234563327127848113273987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116312751102837130817698649 87234563327127848113273987)
              ·
                refine ⟨130851844990691772169910981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87234563327127848113273987 130851844990691772169910981)
                ·
                  refine ⟨24534720935754707281858309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 130851844990691772169910981 24534720935754707281858309)
                  ·
                    refine ⟨4600260175454007615348433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24534720935754707281858309 4600260175454007615348433)
                    ·
                      refine ⟨3450195131590505711511325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4600260175454007615348433 3450195131590505711511325)
                      ·
                        rfl

theorem cell23_6719231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 1, 4, 4, 2].length) (baseStart_6719231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6719231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6719231 prefixEnd_6719231 := by exact prefixLift 6719231
  have htrace : WordTrace (prefixWord ++ tailWord_6719231) baseStart_6719231 baseEnd_6719231 := by
    simpa [prefixWord, tailWord_6719231, baseEnd_6719231] using wordTrace_append hprefix tailTrace_6719231
  have hstable : (prefixWord ++ tailWord_6719231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6719231).length < 2 ^ (prefixWord ++ tailWord_6719231).sum := by decide
  have hdescent : baseEnd_6719231 < baseStart_6719231 := by decide
  rcases family_descends (prefixWord ++ tailWord_6719231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6719244 : List Nat := [2, 2, 1, 2, 2, 1, 2, 2, 2, 1, 6]
def baseStart_6719244 : Nat := 118140960795 + 6719244 * 2 ^ 59
def prefixEnd_6719244 : Nat := 4983230072969 + 3 ^ 40 * 6719244 * 2
def baseEnd_6719244 : Nat := 3450201806839014160648765

theorem tailTrace_6719244 : CollatzResearch.WordTrace tailWord_6719244 prefixEnd_6719244 3450201806839014160648765 := by
  unfold tailWord_6719244
  simp only [CollatzResearch.WordTrace]
  refine ⟨122535481034667009179374393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163380641379556012239165857 122535481034667009179374393)
  ·
    refine ⟨91901610776000256884530795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122535481034667009179374393 91901610776000256884530795)
    ·
      refine ⟨137852416164000385326796193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91901610776000256884530795 137852416164000385326796193)
      ·
        refine ⟨103389312123000288995097145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137852416164000385326796193 103389312123000288995097145)
        ·
          refine ⟨77541984092250216746322859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103389312123000288995097145 77541984092250216746322859)
          ·
            refine ⟨116312976138375325119484289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77541984092250216746322859 116312976138375325119484289)
            ·
              refine ⟨87234732103781493839613217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116312976138375325119484289 87234732103781493839613217)
              ·
                refine ⟨65426049077836120379709913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87234732103781493839613217 65426049077836120379709913)
                ·
                  refine ⟨49069536808377090284782435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65426049077836120379709913 49069536808377090284782435)
                  ·
                    refine ⟨73604305212565635427173653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49069536808377090284782435 73604305212565635427173653)
                    ·
                      refine ⟨3450201806839014160648765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 73604305212565635427173653 3450201806839014160648765)
                      ·
                        rfl

theorem cell23_6719244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 2, 2, 1, 6].length) (baseStart_6719244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6719244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6719244 prefixEnd_6719244 := by exact prefixLift 6719244
  have htrace : WordTrace (prefixWord ++ tailWord_6719244) baseStart_6719244 baseEnd_6719244 := by
    simpa [prefixWord, tailWord_6719244, baseEnd_6719244] using wordTrace_append hprefix tailTrace_6719244
  have hstable : (prefixWord ++ tailWord_6719244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6719244).length < 2 ^ (prefixWord ++ tailWord_6719244).sum := by decide
  have hdescent : baseEnd_6719244 < baseStart_6719244 := by decide
  rcases family_descends (prefixWord ++ tailWord_6719244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6719262 : List Nat := [4, 3, 2, 2, 1, 1, 2, 1, 2, 5]
def baseStart_6719262 : Nat := 118140960795 + 6719262 * 2 ^ 59
def prefixEnd_6719262 : Nat := 4983230072969 + 3 ^ 40 * 6719262 * 2
def baseEnd_6719262 : Nat := 1150070349830265030074561

theorem tailTrace_6719262 : CollatzResearch.WordTrace tailWord_6719262 prefixEnd_6719262 1150070349830265030074561 := by
  unfold tailWord_6719262
  simp only [CollatzResearch.WordTrace]
  refine ⟨30633952322908600929113005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 163381079055512538288602693 30633952322908600929113005)
  ·
    refine ⟨11487732121090725348417377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30633952322908600929113005 11487732121090725348417377)
    ·
      refine ⟨8615799090818044011313033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11487732121090725348417377 8615799090818044011313033)
      ·
        refine ⟨6461849318113533008484775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8615799090818044011313033 6461849318113533008484775)
        ·
          refine ⟨9692773977170299512727163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6461849318113533008484775 9692773977170299512727163)
          ·
            refine ⟨14539160965755449269090745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9692773977170299512727163 14539160965755449269090745)
            ·
              refine ⟨10904370724316586951818059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14539160965755449269090745 10904370724316586951818059)
              ·
                refine ⟨16356556086474880427727089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10904370724316586951818059 16356556086474880427727089)
                ·
                  refine ⟨12267417064856160320795317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16356556086474880427727089 12267417064856160320795317)
                  ·
                    refine ⟨1150070349830265030074561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12267417064856160320795317 1150070349830265030074561)
                    ·
                      rfl

theorem cell23_6719262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 2, 1, 2, 5].length) (baseStart_6719262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6719262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6719262 prefixEnd_6719262 := by exact prefixLift 6719262
  have htrace : WordTrace (prefixWord ++ tailWord_6719262) baseStart_6719262 baseEnd_6719262 := by
    simpa [prefixWord, tailWord_6719262, baseEnd_6719262] using wordTrace_append hprefix tailTrace_6719262
  have hstable : (prefixWord ++ tailWord_6719262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6719262).length < 2 ^ (prefixWord ++ tailWord_6719262).sum := by decide
  have hdescent : baseEnd_6719262 < baseStart_6719262 := by decide
  rcases family_descends (prefixWord ++ tailWord_6719262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6719268 : List Nat := [2, 3, 1, 3, 2, 1, 1, 3, 2, 2, 3]
def baseStart_6719268 : Nat := 118140960795 + 6719268 * 2 ^ 59
def prefixEnd_6719268 : Nat := 4983230072969 + 3 ^ 40 * 6719268 * 2
def baseEnd_6719268 : Nat := 3450214130374722066748655

theorem tailTrace_6719268 : CollatzResearch.WordTrace tailWord_6719268 prefixEnd_6719268 3450214130374722066748655 := by
  unfold tailWord_6719268
  simp only [CollatzResearch.WordTrace]
  refine ⟨122535918710623535228811229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163381224947498046971748305 122535918710623535228811229)
  ·
    refine ⟨45950969516483825710804211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122535918710623535228811229 45950969516483825710804211)
    ·
      refine ⟨68926454274725738566206317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45950969516483825710804211 68926454274725738566206317)
      ·
        refine ⟨25847420353022151962327369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68926454274725738566206317 25847420353022151962327369)
        ·
          refine ⟨19385565264766613971745527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25847420353022151962327369 19385565264766613971745527)
          ·
            refine ⟨29078347897149920957618291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19385565264766613971745527 29078347897149920957618291)
            ·
              refine ⟨43617521845724881436427437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29078347897149920957618291 43617521845724881436427437)
              ·
                refine ⟨16356570692146830538660289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43617521845724881436427437 16356570692146830538660289)
                ·
                  refine ⟨12267428019110122903995217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16356570692146830538660289 12267428019110122903995217)
                  ·
                    refine ⟨9200571014332592177996413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12267428019110122903995217 9200571014332592177996413)
                    ·
                      refine ⟨3450214130374722066748655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9200571014332592177996413 3450214130374722066748655)
                      ·
                        rfl

theorem cell23_6719268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 3, 2, 2, 3].length) (baseStart_6719268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6719268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6719268 prefixEnd_6719268 := by exact prefixLift 6719268
  have htrace : WordTrace (prefixWord ++ tailWord_6719268) baseStart_6719268 baseEnd_6719268 := by
    simpa [prefixWord, tailWord_6719268, baseEnd_6719268] using wordTrace_append hprefix tailTrace_6719268
  have hstable : (prefixWord ++ tailWord_6719268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6719268).length < 2 ^ (prefixWord ++ tailWord_6719268).sum := by decide
  have hdescent : baseEnd_6719268 < baseStart_6719268 := by decide
  rcases family_descends (prefixWord ++ tailWord_6719268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6719321 : List Nat := [1, 2, 1, 2, 2, 3, 1, 3, 3, 1, 4]
def baseStart_6719321 : Nat := 118140960795 + 6719321 * 2 ^ 59
def prefixEnd_6719321 : Nat := 4983230072969 + 3 ^ 40 * 6719321 * 2
def baseEnd_6719321 : Nat := 3450241344849410359385911

theorem tailTrace_6719321 : CollatzResearch.WordTrace tailWord_6719321 prefixEnd_6719321 3450241344849410359385911 := by
  unfold tailWord_6719321
  simp only [CollatzResearch.WordTrace]
  refine ⟨245073770490055060509301817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163382513660036707006201211 245073770490055060509301817)
  ·
    refine ⟨183805327867541295381976363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245073770490055060509301817 183805327867541295381976363)
    ·
      refine ⟨275707991801311943072964545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183805327867541295381976363 275707991801311943072964545)
      ·
        refine ⟨206780993850983957304723409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 275707991801311943072964545 206780993850983957304723409)
        ·
          refine ⟨155085745388237967978542557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 206780993850983957304723409 155085745388237967978542557)
          ·
            refine ⟨58157154520589237991953459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 155085745388237967978542557 58157154520589237991953459)
            ·
              refine ⟨87235731780883856987930189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58157154520589237991953459 87235731780883856987930189)
              ·
                refine ⟨32713399417831446370473821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 87235731780883856987930189 32713399417831446370473821)
                ·
                  refine ⟨12267524781686792388927683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32713399417831446370473821 12267524781686792388927683)
                  ·
                    refine ⟨18401287172530188583391525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12267524781686792388927683 18401287172530188583391525)
                    ·
                      refine ⟨3450241344849410359385911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18401287172530188583391525 3450241344849410359385911)
                      ·
                        rfl

theorem cell23_6719321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 3, 3, 1, 4].length) (baseStart_6719321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6719321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6719321 prefixEnd_6719321 := by exact prefixLift 6719321
  have htrace : WordTrace (prefixWord ++ tailWord_6719321) baseStart_6719321 baseEnd_6719321 := by
    simpa [prefixWord, tailWord_6719321, baseEnd_6719321] using wordTrace_append hprefix tailTrace_6719321
  have hstable : (prefixWord ++ tailWord_6719321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6719321).length < 2 ^ (prefixWord ++ tailWord_6719321).sum := by decide
  have hdescent : baseEnd_6719321 < baseStart_6719321 := by decide
  rcases family_descends (prefixWord ++ tailWord_6719321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6719365 : List Nat := [1, 3, 1, 1, 3, 2, 5, 1, 2, 4]
def baseStart_6719365 : Nat := 118140960795 + 6719365 * 2 ^ 59
def prefixEnd_6719365 : Nat := 4983230072969 + 3 ^ 40 * 6719365 * 2
def baseEnd_6719365 : Nat := 1150087979332736062411903

theorem tailTrace_6719365 : CollatzResearch.WordTrace tailWord_6719365 prefixEnd_6719365 1150087979332736062411903 := by
  unfold tailWord_6719365
  simp only [CollatzResearch.WordTrace]
  refine ⟨245075375301895656023903549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163383583534597104015935699 245075375301895656023903549)
  ·
    refine ⟨91903265738210871008963831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 245075375301895656023903549 91903265738210871008963831)
    ·
      refine ⟨137854898607316306513445747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91903265738210871008963831 137854898607316306513445747)
      ·
        refine ⟨206782347910974459770168621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137854898607316306513445747 206782347910974459770168621)
        ·
          refine ⟨77543380466615422413813233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 206782347910974459770168621 77543380466615422413813233)
          ·
            refine ⟨58157535349961566810359925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77543380466615422413813233 58157535349961566810359925)
            ·
              refine ⟨5452268939058896888471243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 58157535349961566810359925 5452268939058896888471243)
              ·
                refine ⟨8178403408588345332706865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5452268939058896888471243 8178403408588345332706865)
                ·
                  refine ⟨6133802556441258999530149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8178403408588345332706865 6133802556441258999530149)
                  ·
                    refine ⟨1150087979332736062411903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6133802556441258999530149 1150087979332736062411903)
                    ·
                      rfl

theorem cell23_6719365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 5, 1, 2, 4].length) (baseStart_6719365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6719365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6719365 prefixEnd_6719365 := by exact prefixLift 6719365
  have htrace : WordTrace (prefixWord ++ tailWord_6719365) baseStart_6719365 baseEnd_6719365 := by
    simpa [prefixWord, tailWord_6719365, baseEnd_6719365] using wordTrace_append hprefix tailTrace_6719365
  have hstable : (prefixWord ++ tailWord_6719365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6719365).length < 2 ^ (prefixWord ++ tailWord_6719365).sum := by decide
  have hdescent : baseEnd_6719365 < baseStart_6719365 := by decide
  rcases family_descends (prefixWord ++ tailWord_6719365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6719368 : List Nat := [2, 1, 3, 3, 3, 1, 1, 1, 1, 1, 6]
def baseStart_6719368 : Nat := 118140960795 + 6719368 * 2 ^ 59
def prefixEnd_6719368 : Nat := 4983230072969 + 3 ^ 40 * 6719368 * 2
def baseEnd_6719368 : Nat := 3450265478440171675498195

theorem tailTrace_6719368 : CollatzResearch.WordTrace tailWord_6719368 prefixEnd_6719368 3450265478440171675498195 := by
  unfold tailWord_6719368
  simp only [CollatzResearch.WordTrace]
  refine ⟨122537742360442393768131379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163383656480589858357508505 122537742360442393768131379)
  ·
    refine ⟨183806613540663590652197069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122537742360442393768131379 183806613540663590652197069)
    ·
      refine ⟨68927480077748846494573901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 183806613540663590652197069 68927480077748846494573901)
      ·
        refine ⟨25847805029155817435465213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68927480077748846494573901 25847805029155817435465213)
        ·
          refine ⟨9692926885933431538299455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25847805029155817435465213 9692926885933431538299455)
          ·
            refine ⟨14539390328900147307449183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9692926885933431538299455 14539390328900147307449183)
            ·
              refine ⟨21809085493350220961173775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14539390328900147307449183 21809085493350220961173775)
              ·
                refine ⟨32713628240025331441760663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21809085493350220961173775 32713628240025331441760663)
                ·
                  refine ⟨49070442360037997162640995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32713628240025331441760663 49070442360037997162640995)
                  ·
                    refine ⟨73605663540056995743961493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49070442360037997162640995 73605663540056995743961493)
                    ·
                      refine ⟨3450265478440171675498195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 73605663540056995743961493 3450265478440171675498195)
                      ·
                        rfl

theorem cell23_6719368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 1, 1, 1, 6].length) (baseStart_6719368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6719368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6719368 prefixEnd_6719368 := by exact prefixLift 6719368
  have htrace : WordTrace (prefixWord ++ tailWord_6719368) baseStart_6719368 baseEnd_6719368 := by
    simpa [prefixWord, tailWord_6719368, baseEnd_6719368] using wordTrace_append hprefix tailTrace_6719368
  have hstable : (prefixWord ++ tailWord_6719368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6719368).length < 2 ^ (prefixWord ++ tailWord_6719368).sum := by decide
  have hdescent : baseEnd_6719368 < baseStart_6719368 := by decide
  rcases family_descends (prefixWord ++ tailWord_6719368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6719378 : List Nat := [3, 2, 3, 2, 1, 2, 1, 9]
def baseStart_6719378 : Nat := 118140960795 + 6719378 * 2 ^ 59
def prefixEnd_6719378 : Nat := 4983230072969 + 3 ^ 40 * 6719378 * 2
def baseEnd_6719378 : Nat := 127787800490619134680487

theorem tailTrace_6719378 : CollatzResearch.WordTrace tailWord_6719378 prefixEnd_6719378 127787800490619134680487 := by
  unfold tailWord_6719378
  simp only [CollatzResearch.WordTrace]
  refine ⟨61268962362712139811031697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163383899633899039496084525 61268962362712139811031697)
  ·
    refine ⟨45951721772034104858273773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61268962362712139811031697 45951721772034104858273773)
    ·
      refine ⟨17231895664512789321852665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45951721772034104858273773 17231895664512789321852665)
      ·
        refine ⟨12923921748384591991389499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17231895664512789321852665 12923921748384591991389499)
        ·
          refine ⟨19385882622576887987084249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12923921748384591991389499 19385882622576887987084249)
          ·
            refine ⟨14539411966932665990313187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19385882622576887987084249 14539411966932665990313187)
            ·
              refine ⟨21809117950398998985469781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14539411966932665990313187 21809117950398998985469781)
              ·
                refine ⟨127787800490619134680487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 21809117950398998985469781 127787800490619134680487)
                ·
                  rfl

theorem cell23_6719378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 9].length) (baseStart_6719378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6719378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6719378 prefixEnd_6719378 := by exact prefixLift 6719378
  have htrace : WordTrace (prefixWord ++ tailWord_6719378) baseStart_6719378 baseEnd_6719378 := by
    simpa [prefixWord, tailWord_6719378, baseEnd_6719378] using wordTrace_append hprefix tailTrace_6719378
  have hstable : (prefixWord ++ tailWord_6719378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6719378).length < 2 ^ (prefixWord ++ tailWord_6719378).sum := by decide
  have hdescent : baseEnd_6719378 < baseStart_6719378 := by decide
  rcases family_descends (prefixWord ++ tailWord_6719378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6719389 : List Nat := [1, 4, 2, 1, 2, 2, 3, 3, 1, 2, 2]
def baseStart_6719389 : Nat := 118140960795 + 6719389 * 2 ^ 59
def prefixEnd_6719389 : Nat := 4983230072969 + 3 ^ 40 * 6719389 * 2
def baseEnd_6719389 : Nat := 3450276261533916093335599

theorem tailTrace_6719389 : CollatzResearch.WordTrace tailWord_6719389 prefixEnd_6719389 3450276261533916093335599 := by
  unfold tailWord_6719389
  simp only [CollatzResearch.WordTrace]
  refine ⟨245076250653808708122777221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163384167102539138748518147 245076250653808708122777221)
  ·
    refine ⟨45951796997589132773020729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 245076250653808708122777221 45951796997589132773020729)
    ·
      refine ⟨34463847748191849579765547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45951796997589132773020729 34463847748191849579765547)
      ·
        refine ⟨51695771622287774369648321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34463847748191849579765547 51695771622287774369648321)
        ·
          refine ⟨38771828716715830777236241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51695771622287774369648321 38771828716715830777236241)
          ·
            refine ⟨29078871537536873082927181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38771828716715830777236241 29078871537536873082927181)
            ·
              refine ⟨10904576826576327406097693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29078871537536873082927181 10904576826576327406097693)
              ·
                refine ⟨4089216309966122777286635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10904576826576327406097693 4089216309966122777286635)
                ·
                  refine ⟨6133824464949184165929953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4089216309966122777286635 6133824464949184165929953)
                  ·
                    refine ⟨4600368348711888124447465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6133824464949184165929953 4600368348711888124447465)
                    ·
                      refine ⟨3450276261533916093335599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4600368348711888124447465 3450276261533916093335599)
                      ·
                        rfl

theorem cell23_6719389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 3, 3, 1, 2, 2].length) (baseStart_6719389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6719389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6719389 prefixEnd_6719389 := by exact prefixLift 6719389
  have htrace : WordTrace (prefixWord ++ tailWord_6719389) baseStart_6719389 baseEnd_6719389 := by
    simpa [prefixWord, tailWord_6719389, baseEnd_6719389] using wordTrace_append hprefix tailTrace_6719389
  have hstable : (prefixWord ++ tailWord_6719389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6719389).length < 2 ^ (prefixWord ++ tailWord_6719389).sum := by decide
  have hdescent : baseEnd_6719389 < baseStart_6719389 := by decide
  rcases family_descends (prefixWord ++ tailWord_6719389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6719411 : List Nat := [1, 1, 1, 2, 3, 1, 4, 1, 2, 3, 4]
def baseStart_6719411 : Nat := 118140960795 + 6719411 * 2 ^ 59
def prefixEnd_6719411 : Nat := 4983230072969 + 3 ^ 40 * 6719411 * 2
def baseEnd_6719411 : Nat := 3450287558108315007260497

theorem tailTrace_6719411 : CollatzResearch.WordTrace tailWord_6719411 prefixEnd_6719411 3450287558108315007260497 := by
  unfold tailWord_6719411
  simp only [CollatzResearch.WordTrace]
  refine ⟨245077053059729005880078087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163384702039819337253385391 245077053059729005880078087)
  ·
    refine ⟨367615579589593508820117131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245077053059729005880078087 367615579589593508820117131)
    ·
      refine ⟨551423369384390263230175697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 367615579589593508820117131 551423369384390263230175697)
      ·
        refine ⟨413567527038292697422631773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 551423369384390263230175697 413567527038292697422631773)
        ·
          refine ⟨155087822639359761533486915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 413567527038292697422631773 155087822639359761533486915)
          ·
            refine ⟨232631733959039642300230373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155087822639359761533486915 232631733959039642300230373)
            ·
              refine ⟨43618450117319932931293195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 232631733959039642300230373 43618450117319932931293195)
              ·
                refine ⟨65427675175979899396939793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43618450117319932931293195 65427675175979899396939793)
                ·
                  refine ⟨49070756381984924547704845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65427675175979899396939793 49070756381984924547704845)
                  ·
                    refine ⟨18401533643244346705389317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49070756381984924547704845 18401533643244346705389317)
                    ·
                      refine ⟨3450287558108315007260497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18401533643244346705389317 3450287558108315007260497)
                      ·
                        rfl

theorem cell23_6719411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 1, 2, 3, 4].length) (baseStart_6719411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6719411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6719411 prefixEnd_6719411 := by exact prefixLift 6719411
  have htrace : WordTrace (prefixWord ++ tailWord_6719411) baseStart_6719411 baseEnd_6719411 := by
    simpa [prefixWord, tailWord_6719411, baseEnd_6719411] using wordTrace_append hprefix tailTrace_6719411
  have hstable : (prefixWord ++ tailWord_6719411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6719411).length < 2 ^ (prefixWord ++ tailWord_6719411).sum := by decide
  have hdescent : baseEnd_6719411 < baseStart_6719411 := by decide
  rcases family_descends (prefixWord ++ tailWord_6719411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6719422 : List Nat := [4, 2, 1, 1, 1, 4, 1, 3, 2, 1, 3]
def baseStart_6719422 : Nat := 118140960795 + 6719422 * 2 ^ 59
def prefixEnd_6719422 : Nat := 4983230072969 + 3 ^ 40 * 6719422 * 2
def baseEnd_6719422 : Nat := 3450293206395514464222947

theorem tailTrace_6719422 : CollatzResearch.WordTrace tailWord_6719422 prefixEnd_6719422 3450293206395514464222947 := by
  unfold tailWord_6719422
  simp only [CollatzResearch.WordTrace]
  refine ⟨30634681782836144344841065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 163384969508459436505819013 30634681782836144344841065)
  ·
    refine ⟨22976011337127108258630799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30634681782836144344841065 22976011337127108258630799)
    ·
      refine ⟨34464017005690662387946199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22976011337127108258630799 34464017005690662387946199)
      ·
        refine ⟨51696025508535993581919299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34464017005690662387946199 51696025508535993581919299)
        ·
          refine ⟨77544038262803990372878949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51696025508535993581919299 77544038262803990372878949)
          ·
            refine ⟨14539507174275748194914803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 77544038262803990372878949 14539507174275748194914803)
            ·
              refine ⟨21809260761413622292372205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14539507174275748194914803 21809260761413622292372205)
              ·
                refine ⟨8178472785530108359639577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21809260761413622292372205 8178472785530108359639577)
                ·
                  refine ⟨6133854589147581269729683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8178472785530108359639577 6133854589147581269729683)
                  ·
                    refine ⟨9200781883721371904594525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6133854589147581269729683 9200781883721371904594525)
                    ·
                      refine ⟨3450293206395514464222947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9200781883721371904594525 3450293206395514464222947)
                      ·
                        rfl

theorem cell23_6719422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 3, 2, 1, 3].length) (baseStart_6719422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6719422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6719422 prefixEnd_6719422 := by exact prefixLift 6719422
  have htrace : WordTrace (prefixWord ++ tailWord_6719422) baseStart_6719422 baseEnd_6719422 := by
    simpa [prefixWord, tailWord_6719422, baseEnd_6719422] using wordTrace_append hprefix tailTrace_6719422
  have hstable : (prefixWord ++ tailWord_6719422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6719422).length < 2 ^ (prefixWord ++ tailWord_6719422).sum := by decide
  have hdescent : baseEnd_6719422 < baseStart_6719422 := by decide
  rcases family_descends (prefixWord ++ tailWord_6719422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6719432 : List Nat := [2, 1, 3, 1, 4, 1, 3, 2, 1, 3, 2]
def baseStart_6719432 : Nat := 118140960795 + 6719432 * 2 ^ 59
def prefixEnd_6719432 : Nat := 4983230072969 + 3 ^ 40 * 6719432 * 2
def baseEnd_6719432 : Nat := 3450298341202059425097901

theorem tailTrace_6719432 : CollatzResearch.WordTrace tailWord_6719432 prefixEnd_6719432 3450298341202059425097901 := by
  unfold tailWord_6719432
  simp only [CollatzResearch.WordTrace]
  refine ⟨122538909496326463233296275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163385212661768617644395033 122538909496326463233296275)
  ·
    refine ⟨183808364244489694849944413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122538909496326463233296275 183808364244489694849944413)
    ·
      refine ⟨68928136591683635568729155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 183808364244489694849944413 68928136591683635568729155)
      ·
        refine ⟨103392204887525453353093733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68928136591683635568729155 103392204887525453353093733)
        ·
          refine ⟨19386038416411022503705075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 103392204887525453353093733 19386038416411022503705075)
          ·
            refine ⟨29079057624616533755557613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19386038416411022503705075 29079057624616533755557613)
            ·
              refine ⟨10904646609231200158334105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29079057624616533755557613 10904646609231200158334105)
              ·
                refine ⟨8178484956923400118750579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10904646609231200158334105 8178484956923400118750579)
                ·
                  refine ⟨12267727435385100178125869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8178484956923400118750579 12267727435385100178125869)
                  ·
                    refine ⟨4600397788269412566797201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12267727435385100178125869 4600397788269412566797201)
                    ·
                      refine ⟨3450298341202059425097901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4600397788269412566797201 3450298341202059425097901)
                      ·
                        rfl

theorem cell23_6719432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 3, 2, 1, 3, 2].length) (baseStart_6719432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6719432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6719432 prefixEnd_6719432 := by exact prefixLift 6719432
  have htrace : WordTrace (prefixWord ++ tailWord_6719432) baseStart_6719432 baseEnd_6719432 := by
    simpa [prefixWord, tailWord_6719432, baseEnd_6719432] using wordTrace_append hprefix tailTrace_6719432
  have hstable : (prefixWord ++ tailWord_6719432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6719432).length < 2 ^ (prefixWord ++ tailWord_6719432).sum := by decide
  have hdescent : baseEnd_6719432 < baseStart_6719432 := by decide
  rcases family_descends (prefixWord ++ tailWord_6719432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6719441 : List Nat := [1, 2, 2, 1, 2, 1, 2, 1, 3, 4, 4]
def baseStart_6719441 : Nat := 118140960795 + 6719441 * 2 ^ 59
def prefixEnd_6719441 : Nat := 4983230072969 + 3 ^ 40 * 6719441 * 2
def baseEnd_6719441 : Nat := 3450302962527949889885359

theorem tailTrace_6719441 : CollatzResearch.WordTrace tailWord_6719441 prefixEnd_6719441 3450302962527949889885359 := by
  unfold tailWord_6719441
  simp only [CollatzResearch.WordTrace]
  refine ⟨245078147249620321003670177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163385431499746880669113451 245078147249620321003670177)
  ·
    refine ⟨183808610437215240752752633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245078147249620321003670177 183808610437215240752752633)
    ·
      refine ⟨137856457827911430564564475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183808610437215240752752633 137856457827911430564564475)
      ·
        refine ⟨206784686741867145846846713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137856457827911430564564475 206784686741867145846846713)
        ·
          refine ⟨155088515056400359385135035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 206784686741867145846846713 155088515056400359385135035)
          ·
            refine ⟨232632772584600539077702553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155088515056400359385135035 232632772584600539077702553)
            ·
              refine ⟨174474579438450404308276915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 232632772584600539077702553 174474579438450404308276915)
              ·
                refine ⟨261711869157675606462415373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 174474579438450404308276915 261711869157675606462415373)
                ·
                  refine ⟨98141950934128352423405765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 261711869157675606462415373 98141950934128352423405765)
                  ·
                    refine ⟨18401615800149066079388581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 98141950934128352423405765 18401615800149066079388581)
                    ·
                      refine ⟨3450302962527949889885359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18401615800149066079388581 3450302962527949889885359)
                      ·
                        rfl

theorem cell23_6719441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 3, 4, 4].length) (baseStart_6719441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6719441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6719441 prefixEnd_6719441 := by exact prefixLift 6719441
  have htrace : WordTrace (prefixWord ++ tailWord_6719441) baseStart_6719441 baseEnd_6719441 := by
    simpa [prefixWord, tailWord_6719441, baseEnd_6719441] using wordTrace_append hprefix tailTrace_6719441
  have hstable : (prefixWord ++ tailWord_6719441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6719441).length < 2 ^ (prefixWord ++ tailWord_6719441).sum := by decide
  have hdescent : baseEnd_6719441 < baseStart_6719441 := by decide
  rcases family_descends (prefixWord ++ tailWord_6719441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6719445 : List Nat := [1, 3, 2, 3, 2, 1, 1, 1, 3, 4, 2]
def baseStart_6719445 : Nat := 118140960795 + 6719445 * 2 ^ 59
def prefixEnd_6719445 : Nat := 4983230072969 + 3 ^ 40 * 6719445 * 2
def baseEnd_6719445 : Nat := 3450305016450567874235341

theorem tailTrace_6719445 : CollatzResearch.WordTrace tailWord_6719445 prefixEnd_6719445 3450305016450567874235341 := by
  unfold tailWord_6719445
  simp only [CollatzResearch.WordTrace]
  refine ⟨245078293141605829686815789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163385528761070553124543859 245078293141605829686815789)
  ·
    refine ⟨91904359928102186132555921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 245078293141605829686815789 91904359928102186132555921)
    ·
      refine ⟨68928269946076639599416941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91904359928102186132555921 68928269946076639599416941)
      ·
        refine ⟨25848101229778739849781353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68928269946076639599416941 25848101229778739849781353)
        ·
          refine ⟨19386075922334054887336015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25848101229778739849781353 19386075922334054887336015)
          ·
            refine ⟨29079113883501082331004023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19386075922334054887336015 29079113883501082331004023)
            ·
              refine ⟨43618670825251623496506035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29079113883501082331004023 43618670825251623496506035)
              ·
                refine ⟨65428006237877435244759053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43618670825251623496506035 65428006237877435244759053)
                ·
                  refine ⟨24535502339204038216784645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65428006237877435244759053 24535502339204038216784645)
                  ·
                    refine ⟨4600406688600757165647121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24535502339204038216784645 4600406688600757165647121)
                    ·
                      refine ⟨3450305016450567874235341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4600406688600757165647121 3450305016450567874235341)
                      ·
                        rfl

theorem cell23_6719445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 1, 3, 4, 2].length) (baseStart_6719445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6719445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6719445 prefixEnd_6719445 := by exact prefixLift 6719445
  have htrace : WordTrace (prefixWord ++ tailWord_6719445) baseStart_6719445 baseEnd_6719445 := by
    simpa [prefixWord, tailWord_6719445, baseEnd_6719445] using wordTrace_append hprefix tailTrace_6719445
  have hstable : (prefixWord ++ tailWord_6719445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6719445).length < 2 ^ (prefixWord ++ tailWord_6719445).sum := by decide
  have hdescent : baseEnd_6719445 < baseStart_6719445 := by decide
  rcases family_descends (prefixWord ++ tailWord_6719445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6719449 : List Nat := [1, 2, 1, 2, 6, 1, 3, 1, 1, 3, 2]
def baseStart_6719449 : Nat := 118140960795 + 6719449 * 2 ^ 59
def prefixEnd_6719449 : Nat := 4983230072969 + 3 ^ 40 * 6719449 * 2
def baseEnd_6719449 : Nat := 3450307070373185858585323

theorem tailTrace_6719449 : CollatzResearch.WordTrace tailWord_6719449 prefixEnd_6719449 3450307070373185858585323 := by
  unfold tailWord_6719449
  simp only [CollatzResearch.WordTrace]
  refine ⟨245078439033591338369961401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163385626022394225579974267 245078439033591338369961401)
  ·
    refine ⟨183808829275193503777471051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245078439033591338369961401 183808829275193503777471051)
    ·
      refine ⟨275713243912790255666206577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183808829275193503777471051 275713243912790255666206577)
      ·
        refine ⟨206784932934592691749654933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 275713243912790255666206577 206784932934592691749654933)
        ·
          refine ⟨9693043731309032425765075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 206784932934592691749654933 9693043731309032425765075)
          ·
            refine ⟨14539565596963548638647613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9693043731309032425765075 14539565596963548638647613)
            ·
              refine ⟨5452337098861330739492855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14539565596963548638647613 5452337098861330739492855)
              ·
                refine ⟨8178505648291996109239283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5452337098861330739492855 8178505648291996109239283)
                ·
                  refine ⟨12267758472437994163858925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8178505648291996109239283 12267758472437994163858925)
                  ·
                    refine ⟨4600409427164247811447097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12267758472437994163858925 4600409427164247811447097)
                    ·
                      refine ⟨3450307070373185858585323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4600409427164247811447097 3450307070373185858585323)
                      ·
                        rfl

theorem cell23_6719449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 3, 1, 1, 3, 2].length) (baseStart_6719449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6719449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6719449 prefixEnd_6719449 := by exact prefixLift 6719449
  have htrace : WordTrace (prefixWord ++ tailWord_6719449) baseStart_6719449 baseEnd_6719449 := by
    simpa [prefixWord, tailWord_6719449, baseEnd_6719449] using wordTrace_append hprefix tailTrace_6719449
  have hstable : (prefixWord ++ tailWord_6719449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6719449).length < 2 ^ (prefixWord ++ tailWord_6719449).sum := by decide
  have hdescent : baseEnd_6719449 < baseStart_6719449 := by decide
  rcases family_descends (prefixWord ++ tailWord_6719449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6719491 : List Nat := [1, 1, 1, 3, 2, 1, 1, 4, 1, 1, 7]
def baseStart_6719491 : Nat := 118140960795 + 6719491 * 2 ^ 59
def prefixEnd_6719491 : Nat := 4983230072969 + 3 ^ 40 * 6719491 * 2
def baseEnd_6719491 : Nat := 3450328636560674694260129

theorem tailTrace_6719491 : CollatzResearch.WordTrace tailWord_6719491 prefixEnd_6719491 3450328636560674694260129 := by
  unfold tailWord_6719491
  simp only [CollatzResearch.WordTrace]
  refine ⟨245079970899439179542990327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163386647266292786361993551 245079970899439179542990327)
  ·
    refine ⟨367619956349158769314485491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245079970899439179542990327 367619956349158769314485491)
    ·
      refine ⟨551429934523738153971728237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 367619956349158769314485491 551429934523738153971728237)
      ·
        refine ⟨206786225446401807739398089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 551429934523738153971728237 206786225446401807739398089)
        ·
          refine ⟨155089669084801355804548567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 206786225446401807739398089 155089669084801355804548567)
          ·
            refine ⟨232634503627202033706822851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155089669084801355804548567 232634503627202033706822851)
            ·
              refine ⟨348951755440803050560234277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 232634503627202033706822851 348951755440803050560234277)
              ·
                refine ⟨65428454145150571980043927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 348951755440803050560234277 65428454145150571980043927)
                ·
                  refine ⟨98142681217725857970065891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65428454145150571980043927 98142681217725857970065891)
                  ·
                    refine ⟨147214021826588786955098837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 98142681217725857970065891 147214021826588786955098837)
                    ·
                      refine ⟨3450328636560674694260129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 147214021826588786955098837 3450328636560674694260129)
                      ·
                        rfl

theorem cell23_6719491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 4, 1, 1, 7].length) (baseStart_6719491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6719491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6719491 prefixEnd_6719491 := by exact prefixLift 6719491
  have htrace : WordTrace (prefixWord ++ tailWord_6719491) baseStart_6719491 baseEnd_6719491 := by
    simpa [prefixWord, tailWord_6719491, baseEnd_6719491] using wordTrace_append hprefix tailTrace_6719491
  have hstable : (prefixWord ++ tailWord_6719491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6719491).length < 2 ^ (prefixWord ++ tailWord_6719491).sum := by decide
  have hdescent : baseEnd_6719491 < baseStart_6719491 := by decide
  rcases family_descends (prefixWord ++ tailWord_6719491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6719548 : List Nat := [2, 2, 2, 2, 2, 1, 1, 1, 2, 4, 4]
def baseStart_6719548 : Nat := 118140960795 + 6719548 * 2 ^ 59
def prefixEnd_6719548 : Nat := 4983230072969 + 3 ^ 40 * 6719548 * 2
def baseEnd_6719548 : Nat := 3450357904957980971247367

theorem tailTrace_6719548 : CollatzResearch.WordTrace tailWord_6719548 prefixEnd_6719548 3450357904957980971247367 := by
  unfold tailWord_6719548
  simp only [CollatzResearch.WordTrace]
  refine ⟨122541024930116339138907649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163388033240155118851876865 122541024930116339138907649)
  ·
    refine ⟨91905768697587254354180737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122541024930116339138907649 91905768697587254354180737)
    ·
      refine ⟨68929326523190440765635553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91905768697587254354180737 68929326523190440765635553)
      ·
        refine ⟨51696994892392830574226665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68929326523190440765635553 51696994892392830574226665)
        ·
          refine ⟨38772746169294622930669999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51696994892392830574226665 38772746169294622930669999)
          ·
            refine ⟨58159119253941934396004999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38772746169294622930669999 58159119253941934396004999)
            ·
              refine ⟨87238678880912901594007499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58159119253941934396004999 87238678880912901594007499)
              ·
                refine ⟨130858018321369352391011249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87238678880912901594007499 130858018321369352391011249)
                ·
                  refine ⟨98143513741027014293258437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 130858018321369352391011249 98143513741027014293258437)
                  ·
                    refine ⟨18401908826442565179985957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 98143513741027014293258437 18401908826442565179985957)
                    ·
                      refine ⟨3450357904957980971247367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18401908826442565179985957 3450357904957980971247367)
                      ·
                        rfl

theorem cell23_6719548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 1, 2, 4, 4].length) (baseStart_6719548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6719548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6719548 prefixEnd_6719548 := by exact prefixLift 6719548
  have htrace : WordTrace (prefixWord ++ tailWord_6719548) baseStart_6719548 baseEnd_6719548 := by
    simpa [prefixWord, tailWord_6719548, baseEnd_6719548] using wordTrace_append hprefix tailTrace_6719548
  have hstable : (prefixWord ++ tailWord_6719548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6719548).length < 2 ^ (prefixWord ++ tailWord_6719548).sum := by decide
  have hdescent : baseEnd_6719548 < baseStart_6719548 := by decide
  rcases family_descends (prefixWord ++ tailWord_6719548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6719612 : List Nat := [2, 2, 2, 1, 1, 4, 1, 3, 2, 3, 2]
def baseStart_6719612 : Nat := 118140960795 + 6719612 * 2 ^ 59
def prefixEnd_6719612 : Nat := 4983230072969 + 3 ^ 40 * 6719612 * 2
def baseEnd_6719612 : Nat := 3450390767719868720847073

theorem tailTrace_6719612 : CollatzResearch.WordTrace tailWord_6719612 prefixEnd_6719612 3450390767719868720847073 := by
  unfold tailWord_6719612
  simp only [CollatzResearch.WordTrace]
  refine ⟨122542192066000408604072545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163389589421333878138763393 122542192066000408604072545)
  ·
    refine ⟨91906644049500306453054409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122542192066000408604072545 91906644049500306453054409)
    ·
      refine ⟨68929983037125229839790807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91906644049500306453054409 68929983037125229839790807)
      ·
        refine ⟨103394974555687844759686211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68929983037125229839790807 103394974555687844759686211)
        ·
          refine ⟨155092461833531767139529317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103394974555687844759686211 155092461833531767139529317)
          ·
            refine ⟨29079836593787206338661747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 155092461833531767139529317 29079836593787206338661747)
            ·
              refine ⟨43619754890680809507992621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29079836593787206338661747 43619754890680809507992621)
              ·
                refine ⟨16357408084005303565497233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43619754890680809507992621 16357408084005303565497233)
                ·
                  refine ⟨12268056063003977674122925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16357408084005303565497233 12268056063003977674122925)
                  ·
                    refine ⟨4600521023626491627796097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12268056063003977674122925 4600521023626491627796097)
                    ·
                      refine ⟨3450390767719868720847073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4600521023626491627796097 3450390767719868720847073)
                      ·
                        rfl

theorem cell23_6719612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 3, 2, 3, 2].length) (baseStart_6719612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6719612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6719612 prefixEnd_6719612 := by exact prefixLift 6719612
  have htrace : WordTrace (prefixWord ++ tailWord_6719612) baseStart_6719612 baseEnd_6719612 := by
    simpa [prefixWord, tailWord_6719612, baseEnd_6719612] using wordTrace_append hprefix tailTrace_6719612
  have hstable : (prefixWord ++ tailWord_6719612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6719612).length < 2 ^ (prefixWord ++ tailWord_6719612).sum := by decide
  have hdescent : baseEnd_6719612 < baseStart_6719612 := by decide
  rcases family_descends (prefixWord ++ tailWord_6719612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6719652 : List Nat := [2, 3, 1, 2, 4, 1, 2, 1, 1, 6]
def baseStart_6719652 : Nat := 118140960795 + 6719652 * 2 ^ 59
def prefixEnd_6719652 : Nat := 4983230072969 + 3 ^ 40 * 6719652 * 2
def baseEnd_6719652 : Nat := 1150137102315349521448963

theorem tailTrace_6719652 : CollatzResearch.WordTrace tailWord_6719652 prefixEnd_6719652 1150137102315349521448963 := by
  unfold tailWord_6719652
  simp only [CollatzResearch.WordTrace]
  refine ⟨122542921525927952019800605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163390562034570602693067473 122542921525927952019800605)
  ·
    refine ⟨45953595572222982007425227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122542921525927952019800605 45953595572222982007425227)
    ·
      refine ⟨68930393358334473011137841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45953595572222982007425227 68930393358334473011137841)
      ·
        refine ⟨51697795018750854758353381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68930393358334473011137841 51697795018750854758353381)
        ·
          refine ⟨9693336566015785267191259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51697795018750854758353381 9693336566015785267191259)
          ·
            refine ⟨14540004849023677900786889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9693336566015785267191259 14540004849023677900786889)
            ·
              refine ⟨10905003636767758425590167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14540004849023677900786889 10905003636767758425590167)
              ·
                refine ⟨16357505455151637638385251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10905003636767758425590167 16357505455151637638385251)
                ·
                  refine ⟨24536258182727456457577877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16357505455151637638385251 24536258182727456457577877)
                  ·
                    refine ⟨1150137102315349521448963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24536258182727456457577877 1150137102315349521448963)
                    ·
                      rfl

theorem cell23_6719652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 2, 1, 1, 6].length) (baseStart_6719652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6719652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6719652 prefixEnd_6719652 := by exact prefixLift 6719652
  have htrace : WordTrace (prefixWord ++ tailWord_6719652) baseStart_6719652 baseEnd_6719652 := by
    simpa [prefixWord, tailWord_6719652, baseEnd_6719652] using wordTrace_append hprefix tailTrace_6719652
  have hstable : (prefixWord ++ tailWord_6719652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6719652).length < 2 ^ (prefixWord ++ tailWord_6719652).sum := by decide
  have hdescent : baseEnd_6719652 < baseStart_6719652 := by decide
  rcases family_descends (prefixWord ++ tailWord_6719652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6719675 : List Nat := [1, 1, 1, 1, 1, 2, 5, 4, 1, 3, 3]
def baseStart_6719675 : Nat := 118140960795 + 6719675 * 2 ^ 59
def prefixEnd_6719675 : Nat := 4983230072969 + 3 ^ 40 * 6719675 * 2
def baseEnd_6719675 : Nat := 3450423117001101974359283

theorem tailTrace_6719675 : CollatzResearch.WordTrace tailWord_6719675 prefixEnd_6719675 3450423117001101974359283 := by
  unfold tailWord_6719675
  simp only [CollatzResearch.WordTrace]
  refine ⟨245086681930772578967688479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163391121287181719311792319 245086681930772578967688479)
  ·
    refine ⟨367630022896158868451532719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245086681930772578967688479 367630022896158868451532719)
    ·
      refine ⟨551445034344238302677299079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 367630022896158868451532719 551445034344238302677299079)
      ·
        refine ⟨827167551516357454015948619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 551445034344238302677299079 827167551516357454015948619)
        ·
          refine ⟨1240751327274536181023922929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 827167551516357454015948619 1240751327274536181023922929)
          ·
            refine ⟨930563495455902135767942197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1240751327274536181023922929 930563495455902135767942197)
            ·
              refine ⟨87240327698990825228244581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 930563495455902135767942197 87240327698990825228244581)
              ·
                refine ⟨16357561443560779730295859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 87240327698990825228244581 16357561443560779730295859)
                ·
                  refine ⟨24536342165341169595443789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16357561443560779730295859 24536342165341169595443789)
                  ·
                    refine ⟨9201128312002938598291421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24536342165341169595443789 9201128312002938598291421)
                    ·
                      refine ⟨3450423117001101974359283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9201128312002938598291421 3450423117001101974359283)
                      ·
                        rfl

theorem cell23_6719675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 4, 1, 3, 3].length) (baseStart_6719675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6719675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6719675 prefixEnd_6719675 := by exact prefixLift 6719675
  have htrace : WordTrace (prefixWord ++ tailWord_6719675) baseStart_6719675 baseEnd_6719675 := by
    simpa [prefixWord, tailWord_6719675, baseEnd_6719675] using wordTrace_append hprefix tailTrace_6719675
  have hstable : (prefixWord ++ tailWord_6719675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6719675).length < 2 ^ (prefixWord ++ tailWord_6719675).sum := by decide
  have hdescent : baseEnd_6719675 < baseStart_6719675 := by decide
  rcases family_descends (prefixWord ++ tailWord_6719675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6719676 : List Nat := [2, 2, 2, 3, 3, 2, 2, 1, 1, 1, 4]
def baseStart_6719676 : Nat := 118140960795 + 6719676 * 2 ^ 59
def prefixEnd_6719676 : Nat := 4983230072969 + 3 ^ 40 * 6719676 * 2
def baseEnd_6719676 : Nat := 3450423630481756470446779

theorem tailTrace_6719676 : CollatzResearch.WordTrace tailWord_6719676 prefixEnd_6719676 3450423630481756470446779 := by
  unfold tailWord_6719676
  simp only [CollatzResearch.WordTrace]
  refine ⟨122543359201884478069237441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163391145602512637425649921 122543359201884478069237441)
  ·
    refine ⟨91907519401413358551928081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122543359201884478069237441 91907519401413358551928081)
    ·
      refine ⟨68930639551060018913946061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91907519401413358551928081 68930639551060018913946061)
      ·
        refine ⟨25848989831647507092729773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68930639551060018913946061 25848989831647507092729773)
        ·
          refine ⟨9693371186867815159773665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25848989831647507092729773 9693371186867815159773665)
          ·
            refine ⟨7270028390150861369830249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9693371186867815159773665 7270028390150861369830249)
            ·
              refine ⟨5452521292613146027372687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7270028390150861369830249 5452521292613146027372687)
              ·
                refine ⟨8178781938919719041059031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5452521292613146027372687 8178781938919719041059031)
                ·
                  refine ⟨12268172908379578561588547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8178781938919719041059031 12268172908379578561588547)
                  ·
                    refine ⟨18402259362569367842382821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12268172908379578561588547 18402259362569367842382821)
                    ·
                      refine ⟨3450423630481756470446779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18402259362569367842382821 3450423630481756470446779)
                      ·
                        rfl

theorem cell23_6719676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 2, 1, 1, 1, 4].length) (baseStart_6719676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6719676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6719676 prefixEnd_6719676 := by exact prefixLift 6719676
  have htrace : WordTrace (prefixWord ++ tailWord_6719676) baseStart_6719676 baseEnd_6719676 := by
    simpa [prefixWord, tailWord_6719676, baseEnd_6719676] using wordTrace_append hprefix tailTrace_6719676
  have hstable : (prefixWord ++ tailWord_6719676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6719676).length < 2 ^ (prefixWord ++ tailWord_6719676).sum := by decide
  have hdescent : baseEnd_6719676 < baseStart_6719676 := by decide
  rcases family_descends (prefixWord ++ tailWord_6719676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6719709 : List Nat := [1, 4, 3, 2, 1, 1, 3, 1, 1, 3, 3]
def baseStart_6719709 : Nat := 118140960795 + 6719709 * 2 ^ 59
def prefixEnd_6719709 : Nat := 4983230072969 + 3 ^ 40 * 6719709 * 2
def baseEnd_6719709 : Nat := 3450440575343354841334127

theorem tailTrace_6719709 : CollatzResearch.WordTrace tailWord_6719709 prefixEnd_6719709 3450440575343354841334127 := by
  unfold tailWord_6719709
  simp only [CollatzResearch.WordTrace]
  refine ⟨245087922012649402774426181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163391948008432935182950787 245087922012649402774426181)
  ·
    refine ⟨45953985377371763020204909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 245087922012649402774426181 45953985377371763020204909)
    ·
      refine ⟨17232744516514411132576841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45953985377371763020204909 17232744516514411132576841)
      ·
        refine ⟨12924558387385808349432631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17232744516514411132576841 12924558387385808349432631)
        ·
          refine ⟨19386837581078712524148947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12924558387385808349432631 19386837581078712524148947)
          ·
            refine ⟨29080256371618068786223421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19386837581078712524148947 29080256371618068786223421)
            ·
              refine ⟨10905096139356775794833783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29080256371618068786223421 10905096139356775794833783)
              ·
                refine ⟨16357644209035163692250675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10905096139356775794833783 16357644209035163692250675)
                ·
                  refine ⟨24536466313552745538376013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16357644209035163692250675 24536466313552745538376013)
                  ·
                    refine ⟨9201174867582279576891005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24536466313552745538376013 9201174867582279576891005)
                    ·
                      refine ⟨3450440575343354841334127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9201174867582279576891005 3450440575343354841334127)
                      ·
                        rfl

theorem cell23_6719709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 3, 1, 1, 3, 3].length) (baseStart_6719709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6719709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6719709 prefixEnd_6719709 := by exact prefixLift 6719709
  have htrace : WordTrace (prefixWord ++ tailWord_6719709) baseStart_6719709 baseEnd_6719709 := by
    simpa [prefixWord, tailWord_6719709, baseEnd_6719709] using wordTrace_append hprefix tailTrace_6719709
  have hstable : (prefixWord ++ tailWord_6719709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6719709).length < 2 ^ (prefixWord ++ tailWord_6719709).sum := by decide
  have hdescent : baseEnd_6719709 < baseStart_6719709 := by decide
  rcases family_descends (prefixWord ++ tailWord_6719709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6719795 : List Nat := [1, 1, 1, 2, 5, 1, 1, 1, 3, 2, 5]
def baseStart_6719795 : Nat := 118140960795 + 6719795 * 2 ^ 59
def prefixEnd_6719795 : Nat := 4983230072969 + 3 ^ 40 * 6719795 * 2
def baseEnd_6719795 : Nat := 3450484734679641504858731

theorem tailTrace_6719795 : CollatzResearch.WordTrace tailWord_6719795 prefixEnd_6719795 3450484734679641504858731 := by
  unfold tailWord_6719795
  simp only [CollatzResearch.WordTrace]
  refine ⟨245091058690337839462056839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163394039126891892974704559 245091058690337839462056839)
  ·
    refine ⟨367636588035506759193085259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245091058690337839462056839 367636588035506759193085259)
    ·
      refine ⟨551454882053260138789627889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 367636588035506759193085259 551454882053260138789627889)
      ·
        refine ⟨413591161539945104092220917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 551454882053260138789627889 413591161539945104092220917)
        ·
          refine ⟨38774171394369853508645711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 413591161539945104092220917 38774171394369853508645711)
          ·
            refine ⟨58161257091554780262968567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38774171394369853508645711 58161257091554780262968567)
            ·
              refine ⟨87241885637332170394452851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58161257091554780262968567 87241885637332170394452851)
              ·
                refine ⟨130862828455998255591679277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87241885637332170394452851 130862828455998255591679277)
                ·
                  refine ⟨49073560670999345846879729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 130862828455998255591679277 49073560670999345846879729)
                  ·
                    refine ⟨36805170503249509385159797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49073560670999345846879729 36805170503249509385159797)
                    ·
                      refine ⟨3450484734679641504858731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36805170503249509385159797 3450484734679641504858731)
                      ·
                        rfl

theorem cell23_6719795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 1, 3, 2, 5].length) (baseStart_6719795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6719795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6719795 prefixEnd_6719795 := by exact prefixLift 6719795
  have htrace : WordTrace (prefixWord ++ tailWord_6719795) baseStart_6719795 baseEnd_6719795 := by
    simpa [prefixWord, tailWord_6719795, baseEnd_6719795] using wordTrace_append hprefix tailTrace_6719795
  have hstable : (prefixWord ++ tailWord_6719795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6719795).length < 2 ^ (prefixWord ++ tailWord_6719795).sum := by decide
  have hdescent : baseEnd_6719795 < baseStart_6719795 := by decide
  rcases family_descends (prefixWord ++ tailWord_6719795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6719802 : List Nat := [3, 1, 1, 1, 4, 2, 2, 2, 2, 5]
def baseStart_6719802 : Nat := 118140960795 + 6719802 * 2 ^ 59
def prefixEnd_6719802 : Nat := 4983230072969 + 3 ^ 40 * 6719802 * 2
def baseEnd_6719802 : Nat := 1150162776348074325823733

theorem tailTrace_6719802 : CollatzResearch.WordTrace tailWord_6719802 prefixEnd_6719802 1150162776348074325823733 := by
  unfold tailWord_6719802
  simp only [CollatzResearch.WordTrace]
  refine ⟨61272828500328119914390415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163394209334208319771707773 61272828500328119914390415)
  ·
    refine ⟨91909242750492179871585623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61272828500328119914390415 91909242750492179871585623)
    ·
      refine ⟨137863864125738269807378435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91909242750492179871585623 137863864125738269807378435)
      ·
        refine ⟨206795796188607404711067653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137863864125738269807378435 206795796188607404711067653)
        ·
          refine ⟨38774211785363888383325185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 206795796188607404711067653 38774211785363888383325185)
          ·
            refine ⟨29080658839022916287493889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38774211785363888383325185 29080658839022916287493889)
            ·
              refine ⟨21810494129267187215620417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29080658839022916287493889 21810494129267187215620417)
              ·
                refine ⟨16357870596950390411715313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21810494129267187215620417 16357870596950390411715313)
                ·
                  refine ⟨12268402947712792808786485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16357870596950390411715313 12268402947712792808786485)
                  ·
                    refine ⟨1150162776348074325823733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12268402947712792808786485 1150162776348074325823733)
                    ·
                      rfl

theorem cell23_6719802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 2, 2, 5].length) (baseStart_6719802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6719802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6719802 prefixEnd_6719802 := by exact prefixLift 6719802
  have htrace : WordTrace (prefixWord ++ tailWord_6719802) baseStart_6719802 baseEnd_6719802 := by
    simpa [prefixWord, tailWord_6719802, baseEnd_6719802] using wordTrace_append hprefix tailTrace_6719802
  have hstable : (prefixWord ++ tailWord_6719802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6719802).length < 2 ^ (prefixWord ++ tailWord_6719802).sum := by decide
  have hdescent : baseEnd_6719802 < baseStart_6719802 := by decide
  rcases family_descends (prefixWord ++ tailWord_6719802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6719806 : List Nat := [4, 2, 1, 2, 1, 2, 4, 2, 5]
def baseStart_6719806 : Nat := 118140960795 + 6719806 * 2 ^ 59
def prefixEnd_6719806 : Nat := 4983230072969 + 3 ^ 40 * 6719806 * 2
def baseEnd_6719806 : Nat := 383387820329648995757909

theorem tailTrace_6719806 : CollatzResearch.WordTrace tailWord_6719806 prefixEnd_6719806 383387820329648995757909 := by
  unfold tailWord_6719806
  simp only [CollatzResearch.WordTrace]
  refine ⟨30636432486662248542588409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 163394306595531992227138181 30636432486662248542588409)
  ·
    refine ⟨22977324364996686406941307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30636432486662248542588409 22977324364996686406941307)
    ·
      refine ⟨34465986547495029610411961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22977324364996686406941307 34465986547495029610411961)
      ·
        refine ⟨25849489910621272207808971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34465986547495029610411961 25849489910621272207808971)
        ·
          refine ⟨38774234865931908311713457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25849489910621272207808971 38774234865931908311713457)
          ·
            refine ⟨29080676149448931233785093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38774234865931908311713457 29080676149448931233785093)
            ·
              refine ⟨5452626778021674606334705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29080676149448931233785093 5452626778021674606334705)
              ·
                refine ⟨4089470083516255954751029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5452626778021674606334705 4089470083516255954751029)
                ·
                  refine ⟨383387820329648995757909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4089470083516255954751029 383387820329648995757909)
                  ·
                    rfl

theorem cell23_6719806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 4, 2, 5].length) (baseStart_6719806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6719806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6719806 prefixEnd_6719806 := by exact prefixLift 6719806
  have htrace : WordTrace (prefixWord ++ tailWord_6719806) baseStart_6719806 baseEnd_6719806 := by
    simpa [prefixWord, tailWord_6719806, baseEnd_6719806] using wordTrace_append hprefix tailTrace_6719806
  have hstable : (prefixWord ++ tailWord_6719806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6719806).length < 2 ^ (prefixWord ++ tailWord_6719806).sum := by decide
  have hdescent : baseEnd_6719806 < baseStart_6719806 := by decide
  rcases family_descends (prefixWord ++ tailWord_6719806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6719879 : List Nat := [1, 1, 4, 2, 2, 1, 5, 1, 6]
def baseStart_6719879 : Nat := 118140960795 + 6719879 * 2 ^ 59
def prefixEnd_6719879 : Nat := 4983230072969 + 3 ^ 40 * 6719879 * 2
def baseEnd_6719879 : Nat := 383391985228291019578705

theorem tailTrace_6719879 : CollatzResearch.WordTrace tailWord_6719879 prefixEnd_6719879 383391985228291019578705 := by
  unfold tailWord_6719879
  simp only [CollatzResearch.WordTrace]
  refine ⟨245094122422033521808114691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163396081614689014538743127 245094122422033521808114691)
  ·
    refine ⟨367641183633050282712172037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245094122422033521808114691 367641183633050282712172037)
    ·
      refine ⟨68932721931196928008532257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 367641183633050282712172037 68932721931196928008532257)
      ·
        refine ⟨51699541448397696006399193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68932721931196928008532257 51699541448397696006399193)
        ·
          refine ⟨38774656086298272004799395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51699541448397696006399193 38774656086298272004799395)
          ·
            refine ⟨58161984129447408007199093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38774656086298272004799395 58161984129447408007199093)
            ·
              refine ⟨5452686012135694500674915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 58161984129447408007199093 5452686012135694500674915)
              ·
                refine ⟨8179029018203541751012373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5452686012135694500674915 8179029018203541751012373)
                ·
                  refine ⟨383391985228291019578705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8179029018203541751012373 383391985228291019578705)
                  ·
                    rfl

theorem cell23_6719879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 5, 1, 6].length) (baseStart_6719879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6719879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6719879 prefixEnd_6719879 := by exact prefixLift 6719879
  have htrace : WordTrace (prefixWord ++ tailWord_6719879) baseStart_6719879 baseEnd_6719879 := by
    simpa [prefixWord, tailWord_6719879, baseEnd_6719879] using wordTrace_append hprefix tailTrace_6719879
  have hstable : (prefixWord ++ tailWord_6719879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6719879).length < 2 ^ (prefixWord ++ tailWord_6719879).sum := by decide
  have hdescent : baseEnd_6719879 < baseStart_6719879 := by decide
  rcases family_descends (prefixWord ++ tailWord_6719879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6719946 : List Nat := [3, 1, 2, 1, 2, 2, 2, 1, 5, 2, 2]
def baseStart_6719946 : Nat := 118140960795 + 6719946 * 2 ^ 59
def prefixEnd_6719946 : Nat := 4983230072969 + 3 ^ 40 * 6719946 * 2
def baseEnd_6719946 : Nat := 3450562270258470414070537

theorem tailTrace_6719946 : CollatzResearch.WordTrace tailWord_6719946 prefixEnd_6719946 3450562270258470414070537 := by
  unfold tailWord_6719946
  simp only [CollatzResearch.WordTrace]
  refine ⟨61274141528197698062700923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163397710741860528167202461 61274141528197698062700923)
  ·
    refine ⟨91911212292296547094051385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61274141528197698062700923 91911212292296547094051385)
    ·
      refine ⟨68933409219222410320538539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91911212292296547094051385 68933409219222410320538539)
      ·
        refine ⟨103400113828833615480807809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68933409219222410320538539 103400113828833615480807809)
        ·
          refine ⟨77550085371625211610605857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103400113828833615480807809 77550085371625211610605857)
          ·
            refine ⟨58162564028718908707954393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77550085371625211610605857 58162564028718908707954393)
            ·
              refine ⟨43621923021539181530965795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58162564028718908707954393 43621923021539181530965795)
              ·
                refine ⟨65432884532308772296448693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43621923021539181530965795 65432884532308772296448693)
                ·
                  refine ⟨6134332924903947402792065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 65432884532308772296448693 6134332924903947402792065)
                  ·
                    refine ⟨4600749693677960552094049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6134332924903947402792065 4600749693677960552094049)
                    ·
                      refine ⟨3450562270258470414070537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4600749693677960552094049 3450562270258470414070537)
                      ·
                        rfl

theorem cell23_6719946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 1, 5, 2, 2].length) (baseStart_6719946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6719946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6719946 prefixEnd_6719946 := by exact prefixLift 6719946
  have htrace : WordTrace (prefixWord ++ tailWord_6719946) baseStart_6719946 baseEnd_6719946 := by
    simpa [prefixWord, tailWord_6719946, baseEnd_6719946] using wordTrace_append hprefix tailTrace_6719946
  have hstable : (prefixWord ++ tailWord_6719946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6719946).length < 2 ^ (prefixWord ++ tailWord_6719946).sum := by decide
  have hdescent : baseEnd_6719946 < baseStart_6719946 := by decide
  rcases family_descends (prefixWord ++ tailWord_6719946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6719973 : List Nat := [1, 3, 1, 5, 2, 1, 2, 2, 2, 4]
def baseStart_6719973 : Nat := 118140960795 + 6719973 * 2 ^ 59
def prefixEnd_6719973 : Nat := 4983230072969 + 3 ^ 40 * 6719973 * 2
def baseEnd_6719973 : Nat := 1150192044745380602810971

theorem tailTrace_6719973 : CollatzResearch.WordTrace tailWord_6719973 prefixEnd_6719973 1150192044745380602810971 := by
  unfold tailWord_6719973
  simp only [CollatzResearch.WordTrace]
  refine ⟨245097550883692975862036573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163398367255795317241357715 245097550883692975862036573)
  ·
    refine ⟨91911581581384865948263715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 245097550883692975862036573 91911581581384865948263715)
    ·
      refine ⟨137867372372077298922395573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91911581581384865948263715 137867372372077298922395573)
      ·
        refine ⟨12925066159882246773974585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 137867372372077298922395573 12925066159882246773974585)
        ·
          refine ⟨9693799619911685080480939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12925066159882246773974585 9693799619911685080480939)
          ·
            refine ⟨14540699429867527620721409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9693799619911685080480939 14540699429867527620721409)
            ·
              refine ⟨10905524572400645715541057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14540699429867527620721409 10905524572400645715541057)
              ·
                refine ⟨8179143429300484286655793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10905524572400645715541057 8179143429300484286655793)
                ·
                  refine ⟨6134357571975363214991845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8179143429300484286655793 6134357571975363214991845)
                  ·
                    refine ⟨1150192044745380602810971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6134357571975363214991845 1150192044745380602810971)
                    ·
                      rfl

theorem cell23_6719973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 2, 2, 2, 4].length) (baseStart_6719973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6719973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6719973 prefixEnd_6719973 := by exact prefixLift 6719973
  have htrace : WordTrace (prefixWord ++ tailWord_6719973) baseStart_6719973 baseEnd_6719973 := by
    simpa [prefixWord, tailWord_6719973, baseEnd_6719973] using wordTrace_append hprefix tailTrace_6719973
  have hstable : (prefixWord ++ tailWord_6719973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6719973).length < 2 ^ (prefixWord ++ tailWord_6719973).sum := by decide
  have hdescent : baseEnd_6719973 < baseStart_6719973 := by decide
  rcases family_descends (prefixWord ++ tailWord_6719973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6719986 : List Nat := [3, 2, 1, 4, 2, 2, 1, 8]
def baseStart_6719986 : Nat := 118140960795 + 6719986 * 2 ^ 59
def prefixEnd_6719986 : Nat := 4983230072969 + 3 ^ 40 * 6719986 * 2
def baseEnd_6719986 : Nat := 127799363314246305835939

theorem tailTrace_6719986 : CollatzResearch.WordTrace tailWord_6719986 prefixEnd_6719986 127799363314246305835939 := by
  unfold tailWord_6719986
  simp only [CollatzResearch.WordTrace]
  refine ⟨61274506258161469770564953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163398683355097252721506541 61274506258161469770564953)
  ·
    refine ⟨45955879693621102327923715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61274506258161469770564953 45955879693621102327923715)
    ·
      refine ⟨68933819540431653491885573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45955879693621102327923715 68933819540431653491885573)
      ·
        refine ⟨12925091163830935029728545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68933819540431653491885573 12925091163830935029728545)
        ·
          refine ⟨9693818372873201272296409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12925091163830935029728545 9693818372873201272296409)
          ·
            refine ⟨7270363779654900954222307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9693818372873201272296409 7270363779654900954222307)
            ·
              refine ⟨10905545669482351431333461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7270363779654900954222307 10905545669482351431333461)
              ·
                refine ⟨127799363314246305835939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10905545669482351431333461 127799363314246305835939)
                ·
                  rfl

theorem cell23_6719986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 1, 8].length) (baseStart_6719986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6719986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6719986 prefixEnd_6719986 := by exact prefixLift 6719986
  have htrace : WordTrace (prefixWord ++ tailWord_6719986) baseStart_6719986 baseEnd_6719986 := by
    simpa [prefixWord, tailWord_6719986, baseEnd_6719986] using wordTrace_append hprefix tailTrace_6719986
  have hstable : (prefixWord ++ tailWord_6719986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6719986).length < 2 ^ (prefixWord ++ tailWord_6719986).sum := by decide
  have hdescent : baseEnd_6719986 < baseStart_6719986 := by decide
  rcases family_descends (prefixWord ++ tailWord_6719986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6720029 : List Nat := [1, 4, 2, 2, 1, 2, 1, 2, 2, 6]
def baseStart_6720029 : Nat := 118140960795 + 6720029 * 2 ^ 59
def prefixEnd_6720029 : Nat := 4983230072969 + 3 ^ 40 * 6720029 * 2
def baseEnd_6720029 : Nat := 1150201629717597863110885

theorem tailTrace_6720029 : CollatzResearch.WordTrace tailWord_6720029 prefixEnd_6720029 1150201629717597863110885 := by
  unfold tailWord_6720029
  simp only [CollatzResearch.WordTrace]
  refine ⟨245099593371490097426075141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163399728914326731617383427 245099593371490097426075141)
  ·
    refine ⟨45956173757154393267389089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 245099593371490097426075141 45956173757154393267389089)
    ·
      refine ⟨34467130317865794950541817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45956173757154393267389089 34467130317865794950541817)
      ·
        refine ⟨25850347738399346212906363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34467130317865794950541817 25850347738399346212906363)
        ·
          refine ⟨38775521607599019319359545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25850347738399346212906363 38775521607599019319359545)
          ·
            refine ⟨29081641205699264489519659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38775521607599019319359545 29081641205699264489519659)
            ·
              refine ⟨43622461808548896734279489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29081641205699264489519659 43622461808548896734279489)
              ·
                refine ⟨32716846356411672550709617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43622461808548896734279489 32716846356411672550709617)
                ·
                  refine ⟨24537634767308754413032213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32716846356411672550709617 24537634767308754413032213)
                  ·
                    refine ⟨1150201629717597863110885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24537634767308754413032213 1150201629717597863110885)
                    ·
                      rfl

theorem cell23_6720029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 2, 2, 6].length) (baseStart_6720029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6720029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6720029 prefixEnd_6720029 := by exact prefixLift 6720029
  have htrace : WordTrace (prefixWord ++ tailWord_6720029) baseStart_6720029 baseEnd_6720029 := by
    simpa [prefixWord, tailWord_6720029, baseEnd_6720029] using wordTrace_append hprefix tailTrace_6720029
  have hstable : (prefixWord ++ tailWord_6720029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6720029).length < 2 ^ (prefixWord ++ tailWord_6720029).sum := by decide
  have hdescent : baseEnd_6720029 < baseStart_6720029 := by decide
  rcases family_descends (prefixWord ++ tailWord_6720029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6720049 : List Nat := [1, 2, 2, 3, 1, 1, 4, 1, 2, 2, 4]
def baseStart_6720049 : Nat := 118140960795 + 6720049 * 2 ^ 59
def prefixEnd_6720049 : Nat := 4983230072969 + 3 ^ 40 * 6720049 * 2
def baseEnd_6720049 : Nat := 3450615158765883511082563

theorem tailTrace_6720049 : CollatzResearch.WordTrace tailWord_6720049 prefixEnd_6720049 3450615158765883511082563 := by
  unfold tailWord_6720049
  simp only [CollatzResearch.WordTrace]
  refine ⟨245100322831417640841803201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163400215220945093894535467 245100322831417640841803201)
  ·
    refine ⟨183825242123563230631352401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245100322831417640841803201 183825242123563230631352401)
    ·
      refine ⟨137868931592672422973514301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183825242123563230631352401 137868931592672422973514301)
      ·
        refine ⟨51700849347252158615067863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137868931592672422973514301 51700849347252158615067863)
        ·
          refine ⟨77551274020878237922601795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51700849347252158615067863 77551274020878237922601795)
          ·
            refine ⟨116326911031317356883902693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77551274020878237922601795 116326911031317356883902693)
            ·
              refine ⟨21811295818372004415731755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 116326911031317356883902693 21811295818372004415731755)
              ·
                refine ⟨32716943727558006623597633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21811295818372004415731755 32716943727558006623597633)
                ·
                  refine ⟨24537707795668504967698225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32716943727558006623597633 24537707795668504967698225)
                  ·
                    refine ⟨18403280846751378725773669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24537707795668504967698225 18403280846751378725773669)
                    ·
                      refine ⟨3450615158765883511082563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18403280846751378725773669 3450615158765883511082563)
                      ·
                        rfl

theorem cell23_6720049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 1, 2, 2, 4].length) (baseStart_6720049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6720049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6720049 prefixEnd_6720049 := by exact prefixLift 6720049
  have htrace : WordTrace (prefixWord ++ tailWord_6720049) baseStart_6720049 baseEnd_6720049 := by
    simpa [prefixWord, tailWord_6720049, baseEnd_6720049] using wordTrace_append hprefix tailTrace_6720049
  have hstable : (prefixWord ++ tailWord_6720049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6720049).length < 2 ^ (prefixWord ++ tailWord_6720049).sum := by decide
  have hdescent : baseEnd_6720049 < baseStart_6720049 := by decide
  rcases family_descends (prefixWord ++ tailWord_6720049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6720099 : List Nat := [1, 1, 1, 5, 1, 2, 3, 1, 1, 2, 5]
def baseStart_6720099 : Nat := 118140960795 + 6720099 * 2 ^ 59
def prefixEnd_6720099 : Nat := 4983230072969 + 3 ^ 40 * 6720099 * 2
def baseEnd_6720099 : Nat := 3450640832798608315457333

theorem tailTrace_6720099 : CollatzResearch.WordTrace tailWord_6720099 prefixEnd_6720099 3450640832798608315457333 := by
  unfold tailWord_6720099
  simp only [CollatzResearch.WordTrace]
  refine ⟨245102146481236499381123351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163401430987490999587415567 245102146481236499381123351)
  ·
    refine ⟨367653219721854749071685027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245102146481236499381123351 367653219721854749071685027)
    ·
      refine ⟨551479829582782123607527541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 367653219721854749071685027 551479829582782123607527541)
      ·
        refine ⟨51701234023385824088205707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 551479829582782123607527541 51701234023385824088205707)
        ·
          refine ⟨77551851035078736132308561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51701234023385824088205707 77551851035078736132308561)
          ·
            refine ⟨58163888276309052099231421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77551851035078736132308561 58163888276309052099231421)
            ·
              refine ⟨21811458103615894537211783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58163888276309052099231421 21811458103615894537211783)
              ·
                refine ⟨32717187155423841805817675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21811458103615894537211783 32717187155423841805817675)
                ·
                  refine ⟨49075780733135762708726513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32717187155423841805817675 49075780733135762708726513)
                  ·
                    refine ⟨36806835549851822031544885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49075780733135762708726513 36806835549851822031544885)
                    ·
                      refine ⟨3450640832798608315457333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36806835549851822031544885 3450640832798608315457333)
                      ·
                        rfl

theorem cell23_6720099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 1, 1, 2, 5].length) (baseStart_6720099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6720099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6720099 prefixEnd_6720099 := by exact prefixLift 6720099
  have htrace : WordTrace (prefixWord ++ tailWord_6720099) baseStart_6720099 baseEnd_6720099 := by
    simpa [prefixWord, tailWord_6720099, baseEnd_6720099] using wordTrace_append hprefix tailTrace_6720099
  have hstable : (prefixWord ++ tailWord_6720099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6720099).length < 2 ^ (prefixWord ++ tailWord_6720099).sum := by decide
  have hdescent : baseEnd_6720099 < baseStart_6720099 := by decide
  rcases family_descends (prefixWord ++ tailWord_6720099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6720104 : List Nat := [2, 1, 4, 3, 2, 2, 2, 1, 2, 2, 2]
def baseStart_6720104 : Nat := 118140960795 + 6720104 * 2 ^ 59
def prefixEnd_6720104 : Nat := 4983230072969 + 3 ^ 40 * 6720104 * 2
def baseEnd_6720104 : Nat := 3450643400201880795894811

theorem tailTrace_6720104 : CollatzResearch.WordTrace tailWord_6720104 prefixEnd_6720104 3450643400201880795894811 := by
  unfold tailWord_6720104
  simp only [CollatzResearch.WordTrace]
  refine ⟨122551164423109192617527683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163401552564145590156703577 122551164423109192617527683)
  ·
    refine ⟨183826746634663788926291525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122551164423109192617527683 183826746634663788926291525)
    ·
      refine ⟨34467514993999460423679661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 183826746634663788926291525 34467514993999460423679661)
      ·
        refine ⟨12925318122749797658879873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34467514993999460423679661 12925318122749797658879873)
        ·
          refine ⟨9693988592062348244159905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12925318122749797658879873 9693988592062348244159905)
          ·
            refine ⟨7270491444046761183119929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9693988592062348244159905 7270491444046761183119929)
            ·
              refine ⟨5452868583035070887339947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7270491444046761183119929 5452868583035070887339947)
              ·
                refine ⟨8179302874552606331009921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5452868583035070887339947 8179302874552606331009921)
                ·
                  refine ⟨6134477155914454748257441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8179302874552606331009921 6134477155914454748257441)
                  ·
                    refine ⟨4600857866935841061193081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6134477155914454748257441 4600857866935841061193081)
                    ·
                      refine ⟨3450643400201880795894811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4600857866935841061193081 3450643400201880795894811)
                      ·
                        rfl

theorem cell23_6720104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 2, 1, 2, 2, 2].length) (baseStart_6720104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6720104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6720104 prefixEnd_6720104 := by exact prefixLift 6720104
  have htrace : WordTrace (prefixWord ++ tailWord_6720104) baseStart_6720104 baseEnd_6720104 := by
    simpa [prefixWord, tailWord_6720104, baseEnd_6720104] using wordTrace_append hprefix tailTrace_6720104
  have hstable : (prefixWord ++ tailWord_6720104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6720104).length < 2 ^ (prefixWord ++ tailWord_6720104).sum := by decide
  have hdescent : baseEnd_6720104 < baseStart_6720104 := by decide
  rcases family_descends (prefixWord ++ tailWord_6720104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6720153 : List Nat := [1, 2, 1, 2, 1, 2, 5, 4, 1, 4]
def baseStart_6720153 : Nat := 118140960795 + 6720153 * 2 ^ 59
def prefixEnd_6720153 : Nat := 4983230072969 + 3 ^ 40 * 6720153 * 2
def baseEnd_6720153 : Nat := 1150222853584650368060695

theorem tailTrace_6720153 : CollatzResearch.WordTrace tailWord_6720153 prefixEnd_6720153 1150222853584650368060695 := by
  unfold tailWord_6720153
  simp only [CollatzResearch.WordTrace]
  refine ⟨245104116023040866603589113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163402744015360577735726075 245104116023040866603589113)
  ·
    refine ⟨183828087017280649952691835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245104116023040866603589113 183828087017280649952691835)
    ·
      refine ⟨275742130525920974929037753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183828087017280649952691835 275742130525920974929037753)
      ·
        refine ⟨206806597894440731196778315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 275742130525920974929037753 206806597894440731196778315)
        ·
          refine ⟨310209896841661096795167473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206806597894440731196778315 310209896841661096795167473)
          ·
            refine ⟨232657422631245822596375605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 310209896841661096795167473 232657422631245822596375605)
            ·
              refine ⟨21811633371679295868410213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 232657422631245822596375605 21811633371679295868410213)
              ·
                refine ⟨4089681257189867975326915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21811633371679295868410213 4089681257189867975326915)
                ·
                  refine ⟨6134521885784801962990373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4089681257189867975326915 6134521885784801962990373)
                  ·
                    refine ⟨1150222853584650368060695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6134521885784801962990373 1150222853584650368060695)
                    ·
                      rfl

theorem cell23_6720153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 4, 1, 4].length) (baseStart_6720153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6720153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6720153 prefixEnd_6720153 := by exact prefixLift 6720153
  have htrace : WordTrace (prefixWord ++ tailWord_6720153) baseStart_6720153 baseEnd_6720153 := by
    simpa [prefixWord, tailWord_6720153, baseEnd_6720153] using wordTrace_append hprefix tailTrace_6720153
  have hstable : (prefixWord ++ tailWord_6720153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6720153).length < 2 ^ (prefixWord ++ tailWord_6720153).sum := by decide
  have hdescent : baseEnd_6720153 < baseStart_6720153 := by decide
  rcases family_descends (prefixWord ++ tailWord_6720153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6720177 : List Nat := [1, 2, 2, 6, 2, 1, 1, 1, 2, 1, 4]
def baseStart_6720177 : Nat := 118140960795 + 6720177 * 2 ^ 59
def prefixEnd_6720177 : Nat := 4983230072969 + 3 ^ 40 * 6720177 * 2
def baseEnd_6720177 : Nat := 3450680884289659010281975

theorem tailTrace_6720177 : CollatzResearch.WordTrace tailWord_6720177 prefixEnd_6720177 3450680884289659010281975 := by
  unfold tailWord_6720177
  simp only [CollatzResearch.WordTrace]
  refine ⟨245104991374953918702462785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163403327583302612468308523 245104991374953918702462785)
  ·
    refine ⟨183828743531215439026847089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245104991374953918702462785 183828743531215439026847089)
    ·
      refine ⟨137871557648411579270135317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183828743531215439026847089 137871557648411579270135317)
      ·
        refine ⟨6462729264769292778287593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 137871557648411579270135317 6462729264769292778287593)
        ·
          refine ⟨4847046948576969583715695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6462729264769292778287593 4847046948576969583715695)
          ·
            refine ⟨7270570422865454375573543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4847046948576969583715695 7270570422865454375573543)
            ·
              refine ⟨10905855634298181563360315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7270570422865454375573543 10905855634298181563360315)
              ·
                refine ⟨16358783451447272345040473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10905855634298181563360315 16358783451447272345040473)
                ·
                  refine ⟨12269087588585454258780355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16358783451447272345040473 12269087588585454258780355)
                  ·
                    refine ⟨18403631382878181388170533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12269087588585454258780355 18403631382878181388170533)
                    ·
                      refine ⟨3450680884289659010281975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18403631382878181388170533 3450680884289659010281975)
                      ·
                        rfl

theorem cell23_6720177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 1, 1, 2, 1, 4].length) (baseStart_6720177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6720177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6720177 prefixEnd_6720177 := by exact prefixLift 6720177
  have htrace : WordTrace (prefixWord ++ tailWord_6720177) baseStart_6720177 baseEnd_6720177 := by
    simpa [prefixWord, tailWord_6720177, baseEnd_6720177] using wordTrace_append hprefix tailTrace_6720177
  have hstable : (prefixWord ++ tailWord_6720177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6720177).length < 2 ^ (prefixWord ++ tailWord_6720177).sum := by decide
  have hdescent : baseEnd_6720177 < baseStart_6720177 := by decide
  rcases family_descends (prefixWord ++ tailWord_6720177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6720220 : List Nat := [2, 2, 5, 1, 1, 1, 1, 2, 1, 5, 2]
def baseStart_6720220 : Nat := 118140960795 + 6720220 * 2 ^ 59
def prefixEnd_6720220 : Nat := 4983230072969 + 3 ^ 40 * 6720220 * 2
def baseEnd_6720220 : Nat := 3450702963957802342044277

theorem tailTrace_6720220 : CollatzResearch.WordTrace tailWord_6720220 prefixEnd_6720220 3450702963957802342044277 := by
  unfold tailWord_6720220
  simp only [CollatzResearch.WordTrace]
  refine ⟨122553279856899068523139057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163404373142532091364185409 122553279856899068523139057)
  ·
    refine ⟨91914959892674301392354293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122553279856899068523139057 91914959892674301392354293)
    ·
      refine ⟨8617027489938215755533215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 91914959892674301392354293 8617027489938215755533215)
      ·
        refine ⟨12925541234907323633299823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8617027489938215755533215 12925541234907323633299823)
        ·
          refine ⟨19388311852360985449949735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12925541234907323633299823 19388311852360985449949735)
          ·
            refine ⟨29082467778541478174924603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19388311852360985449949735 29082467778541478174924603)
            ·
              refine ⟨43623701667812217262386905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29082467778541478174924603 43623701667812217262386905)
              ·
                refine ⟨32717776250859162946790179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43623701667812217262386905 32717776250859162946790179)
                ·
                  refine ⟨49076664376288744420185269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32717776250859162946790179 49076664376288744420185269)
                  ·
                    refine ⟨4600937285277069789392369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49076664376288744420185269 4600937285277069789392369)
                    ·
                      refine ⟨3450702963957802342044277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4600937285277069789392369 3450702963957802342044277)
                      ·
                        rfl

theorem cell23_6720220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 2, 1, 5, 2].length) (baseStart_6720220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6720220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6720220 prefixEnd_6720220 := by exact prefixLift 6720220
  have htrace : WordTrace (prefixWord ++ tailWord_6720220) baseStart_6720220 baseEnd_6720220 := by
    simpa [prefixWord, tailWord_6720220, baseEnd_6720220] using wordTrace_append hprefix tailTrace_6720220
  have hstable : (prefixWord ++ tailWord_6720220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6720220).length < 2 ^ (prefixWord ++ tailWord_6720220).sum := by decide
  have hdescent : baseEnd_6720220 < baseStart_6720220 := by decide
  rcases family_descends (prefixWord ++ tailWord_6720220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6720253 : List Nat := [1, 4, 1, 1, 1, 1, 3, 5, 1, 2, 3]
def baseStart_6720253 : Nat := 118140960795 + 6720253 * 2 ^ 59
def prefixEnd_6720253 : Nat := 4983230072969 + 3 ^ 40 * 6720253 * 2
def baseEnd_6720253 : Nat := 3450719908819400712931625

theorem tailTrace_6720253 : CollatzResearch.WordTrace tailWord_6720253 prefixEnd_6720253 3450719908819400712931625 := by
  unfold tailWord_6720253
  simp only [CollatzResearch.WordTrace]
  refine ⟨245107763322678583682229413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163405175548452389121486275 245107763322678583682229413)
  ·
    refine ⟨45957705623002234440418015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 245107763322678583682229413 45957705623002234440418015)
    ·
      refine ⟨68936558434503351660627023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45957705623002234440418015 68936558434503351660627023)
      ·
        refine ⟨103404837651755027490940535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68936558434503351660627023 103404837651755027490940535)
        ·
          refine ⟨155107256477632541236410803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103404837651755027490940535 155107256477632541236410803)
          ·
            refine ⟨232660884716448811854616205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155107256477632541236410803 232660884716448811854616205)
            ·
              refine ⟨87247831768668304445481077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 232660884716448811854616205 87247831768668304445481077)
              ·
                refine ⟨8179484228312653541763851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 87247831768668304445481077 8179484228312653541763851)
                ·
                  refine ⟨12269226342468980312645777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8179484228312653541763851 12269226342468980312645777)
                  ·
                    refine ⟨9201919756851735234484333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12269226342468980312645777 9201919756851735234484333)
                    ·
                      refine ⟨3450719908819400712931625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9201919756851735234484333 3450719908819400712931625)
                      ·
                        rfl

theorem cell23_6720253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 5, 1, 2, 3].length) (baseStart_6720253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6720253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6720253 prefixEnd_6720253 := by exact prefixLift 6720253
  have htrace : WordTrace (prefixWord ++ tailWord_6720253) baseStart_6720253 baseEnd_6720253 := by
    simpa [prefixWord, tailWord_6720253, baseEnd_6720253] using wordTrace_append hprefix tailTrace_6720253
  have hstable : (prefixWord ++ tailWord_6720253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6720253).length < 2 ^ (prefixWord ++ tailWord_6720253).sum := by decide
  have hdescent : baseEnd_6720253 < baseStart_6720253 := by decide
  rcases family_descends (prefixWord ++ tailWord_6720253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6720316 : List Nat := [2, 2, 2, 2, 1, 1, 1, 4, 2, 6]
def baseStart_6720316 : Nat := 118140960795 + 6720316 * 2 ^ 59
def prefixEnd_6720316 : Nat := 4983230072969 + 3 ^ 40 * 6720316 * 2
def baseEnd_6720316 : Nat := 1150250752700211322147945

theorem tailTrace_6720316 : CollatzResearch.WordTrace tailWord_6720316 prefixEnd_6720316 1150250752700211322147945 := by
  unfold tailWord_6720316
  simp only [CollatzResearch.WordTrace]
  refine ⟨122555030560725172720886401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163406707414300230294515201 122555030560725172720886401)
  ·
    refine ⟨91916272920543879540664801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122555030560725172720886401 91916272920543879540664801)
    ·
      refine ⟨68937204690407909655498601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91916272920543879540664801 68937204690407909655498601)
      ·
        refine ⟨51702903517805932241623951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68937204690407909655498601 51702903517805932241623951)
        ·
          refine ⟨77554355276708898362435927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51702903517805932241623951 77554355276708898362435927)
          ·
            refine ⟨116331532915063347543653891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77554355276708898362435927 116331532915063347543653891)
            ·
              refine ⟨174497299372595021315480837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116331532915063347543653891 174497299372595021315480837)
              ·
                refine ⟨32718243632361566496652657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 174497299372595021315480837 32718243632361566496652657)
                ·
                  refine ⟨24538682724271174872489493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32718243632361566496652657 24538682724271174872489493)
                  ·
                    refine ⟨1150250752700211322147945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24538682724271174872489493 1150250752700211322147945)
                    ·
                      rfl

theorem cell23_6720316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 4, 2, 6].length) (baseStart_6720316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6720316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6720316 prefixEnd_6720316 := by exact prefixLift 6720316
  have htrace : WordTrace (prefixWord ++ tailWord_6720316) baseStart_6720316 baseEnd_6720316 := by
    simpa [prefixWord, tailWord_6720316, baseEnd_6720316] using wordTrace_append hprefix tailTrace_6720316
  have hstable : (prefixWord ++ tailWord_6720316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6720316).length < 2 ^ (prefixWord ++ tailWord_6720316).sum := by decide
  have hdescent : baseEnd_6720316 < baseStart_6720316 := by decide
  rcases family_descends (prefixWord ++ tailWord_6720316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6720318 : List Nat := [4, 2, 1, 2, 3, 2, 2, 2, 1, 2, 2]
def baseStart_6720318 : Nat := 118140960795 + 6720318 * 2 ^ 59
def prefixEnd_6720318 : Nat := 4983230072969 + 3 ^ 40 * 6720318 * 2
def baseEnd_6720318 : Nat := 3450753285061942958618827

theorem tailTrace_6720318 : CollatzResearch.WordTrace tailWord_6720318 prefixEnd_6720318 3450753285061942958618827 := by
  unfold tailWord_6720318
  simp only [CollatzResearch.WordTrace]
  refine ⟨30638766758430387472918201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 163406756044962066522230405 30638766758430387472918201)
  ·
    refine ⟨22979075068822790604688651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30638766758430387472918201 22979075068822790604688651)
    ·
      refine ⟨34468612603234185907032977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22979075068822790604688651 34468612603234185907032977)
      ·
        refine ⟨25851459452425639430274733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34468612603234185907032977 25851459452425639430274733)
        ·
          refine ⟨9694297294659614786353025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25851459452425639430274733 9694297294659614786353025)
          ·
            refine ⟨7270722970994711089764769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9694297294659614786353025 7270722970994711089764769)
            ·
              refine ⟨5453042228246033317323577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7270722970994711089764769 5453042228246033317323577)
              ·
                refine ⟨4089781671184524987992683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5453042228246033317323577 4089781671184524987992683)
                ·
                  refine ⟨6134672506776787481989025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4089781671184524987992683 6134672506776787481989025)
                  ·
                    refine ⟨4601004380082590611491769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6134672506776787481989025 4601004380082590611491769)
                    ·
                      refine ⟨3450753285061942958618827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4601004380082590611491769 3450753285061942958618827)
                      ·
                        rfl

theorem cell23_6720318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 2, 2, 1, 2, 2].length) (baseStart_6720318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6720318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6720318 prefixEnd_6720318 := by exact prefixLift 6720318
  have htrace : WordTrace (prefixWord ++ tailWord_6720318) baseStart_6720318 baseEnd_6720318 := by
    simpa [prefixWord, tailWord_6720318, baseEnd_6720318] using wordTrace_append hprefix tailTrace_6720318
  have hstable : (prefixWord ++ tailWord_6720318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6720318).length < 2 ^ (prefixWord ++ tailWord_6720318).sum := by decide
  have hdescent : baseEnd_6720318 < baseStart_6720318 := by decide
  rcases family_descends (prefixWord ++ tailWord_6720318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6720323 : List Nat := [1, 1, 1, 3, 1, 4, 1, 2, 3, 4, 2]
def baseStart_6720323 : Nat := 118140960795 + 6720323 * 2 ^ 59
def prefixEnd_6720323 : Nat := 4983230072969 + 3 ^ 40 * 6720323 * 2
def baseEnd_6720323 : Nat := 3450755852465215439056303

theorem tailTrace_6720323 : CollatzResearch.WordTrace tailWord_6720323 prefixEnd_6720323 3450755852465215439056303 := by
  unfold tailWord_6720323
  simp only [CollatzResearch.WordTrace]
  refine ⟨245110316432424985637277623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163406877621616657091518415 245110316432424985637277623)
  ·
    refine ⟨367665474648637478455916435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245110316432424985637277623 367665474648637478455916435)
    ·
      refine ⟨551498211972956217683874653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 367665474648637478455916435 551498211972956217683874653)
      ·
        refine ⟨206811829489858581631452995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 551498211972956217683874653 206811829489858581631452995)
        ·
          refine ⟨310217744234787872447179493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206811829489858581631452995 310217744234787872447179493)
          ·
            refine ⟨58165827044022726083846155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 310217744234787872447179493 58165827044022726083846155)
            ·
              refine ⟨87248740566034089125769233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58165827044022726083846155 87248740566034089125769233)
              ·
                refine ⟨65436555424525566844326925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87248740566034089125769233 65436555424525566844326925)
                ·
                  refine ⟨24538708284197087566622597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65436555424525566844326925 24538708284197087566622597)
                  ·
                    refine ⟨4601007803286953918741737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24538708284197087566622597 4601007803286953918741737)
                    ·
                      refine ⟨3450755852465215439056303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4601007803286953918741737 3450755852465215439056303)
                      ·
                        rfl

theorem cell23_6720323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 2, 3, 4, 2].length) (baseStart_6720323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6720323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6720323 prefixEnd_6720323 := by exact prefixLift 6720323
  have htrace : WordTrace (prefixWord ++ tailWord_6720323) baseStart_6720323 baseEnd_6720323 := by
    simpa [prefixWord, tailWord_6720323, baseEnd_6720323] using wordTrace_append hprefix tailTrace_6720323
  have hstable : (prefixWord ++ tailWord_6720323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6720323).length < 2 ^ (prefixWord ++ tailWord_6720323).sum := by decide
  have hdescent : baseEnd_6720323 < baseStart_6720323 := by decide
  rcases family_descends (prefixWord ++ tailWord_6720323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6720336 : List Nat := [2, 1, 1, 1, 1, 4, 3, 1, 1, 4, 4]
def baseStart_6720336 : Nat := 118140960795 + 6720336 * 2 ^ 59
def prefixEnd_6720336 : Nat := 4983230072969 + 3 ^ 40 * 6720336 * 2
def baseEnd_6720336 : Nat := 3450762527713723888193743

theorem tailTrace_6720336 : CollatzResearch.WordTrace tailWord_6720336 prefixEnd_6720336 3450762527713723888193743 := by
  unfold tailWord_6720336
  simp only [CollatzResearch.WordTrace]
  refine ⟨122555395290688944428750431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163407193720918592571667241 122555395290688944428750431)
  ·
    refine ⟨183833092936033416643125647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122555395290688944428750431 183833092936033416643125647)
    ·
      refine ⟨275749639404050124964688471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183833092936033416643125647 275749639404050124964688471)
      ·
        refine ⟨413624459106075187447032707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275749639404050124964688471 413624459106075187447032707)
        ·
          refine ⟨620436688659112781170549061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 413624459106075187447032707 620436688659112781170549061)
          ·
            refine ⟨116331879123583646469477949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 620436688659112781170549061 116331879123583646469477949)
            ·
              refine ⟨43624454671343867426054231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 116331879123583646469477949 43624454671343867426054231)
              ·
                refine ⟨65436682007015801139081347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43624454671343867426054231 65436682007015801139081347)
                ·
                  refine ⟨98155023010523701708622021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65436682007015801139081347 98155023010523701708622021)
                  ·
                    refine ⟨18404066814473194070366629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 98155023010523701708622021 18404066814473194070366629)
                    ·
                      refine ⟨3450762527713723888193743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18404066814473194070366629 3450762527713723888193743)
                      ·
                        rfl

theorem cell23_6720336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 1, 1, 4, 4].length) (baseStart_6720336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6720336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6720336 prefixEnd_6720336 := by exact prefixLift 6720336
  have htrace : WordTrace (prefixWord ++ tailWord_6720336) baseStart_6720336 baseEnd_6720336 := by
    simpa [prefixWord, tailWord_6720336, baseEnd_6720336] using wordTrace_append hprefix tailTrace_6720336
  have hstable : (prefixWord ++ tailWord_6720336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6720336).length < 2 ^ (prefixWord ++ tailWord_6720336).sum := by decide
  have hdescent : baseEnd_6720336 < baseStart_6720336 := by decide
  rcases family_descends (prefixWord ++ tailWord_6720336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6720346 : List Nat := [3, 1, 1, 2, 1, 4, 1, 1, 9]
def baseStart_6720346 : Nat := 118140960795 + 6720346 * 2 ^ 59
def prefixEnd_6720346 : Nat := 4983230072969 + 3 ^ 40 * 6720346 * 2
def baseEnd_6720346 : Nat := 383418629168918761007633

theorem tailTrace_6720346 : CollatzResearch.WordTrace tailWord_6720346 prefixEnd_6720346 383418629168918761007633 := by
  unfold tailWord_6720346
  simp only [CollatzResearch.WordTrace]
  refine ⟨61277788827835415141341223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163407436874227773710243261 61277788827835415141341223)
  ·
    refine ⟨91916683241753122712011835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61277788827835415141341223 91916683241753122712011835)
    ·
      refine ⟨137875024862629684068017753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91916683241753122712011835 137875024862629684068017753)
      ·
        refine ⟨103406268646972263051013315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137875024862629684068017753 103406268646972263051013315)
        ·
          refine ⟨155109402970458394576519973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103406268646972263051013315 155109402970458394576519973)
          ·
            refine ⟨29083013056960948983097495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 155109402970458394576519973 29083013056960948983097495)
            ·
              refine ⟨43624519585441423474646243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29083013056960948983097495 43624519585441423474646243)
              ·
                refine ⟨65436779378162135211969365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43624519585441423474646243 65436779378162135211969365)
                ·
                  refine ⟨383418629168918761007633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 65436779378162135211969365 383418629168918761007633)
                  ·
                    rfl

theorem cell23_6720346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 1, 9].length) (baseStart_6720346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6720346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6720346 prefixEnd_6720346 := by exact prefixLift 6720346
  have htrace : WordTrace (prefixWord ++ tailWord_6720346) baseStart_6720346 baseEnd_6720346 := by
    simpa [prefixWord, tailWord_6720346, baseEnd_6720346] using wordTrace_append hprefix tailTrace_6720346
  have hstable : (prefixWord ++ tailWord_6720346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6720346).length < 2 ^ (prefixWord ++ tailWord_6720346).sum := by decide
  have hdescent : baseEnd_6720346 < baseStart_6720346 := by decide
  rcases family_descends (prefixWord ++ tailWord_6720346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6720363 : List Nat := [1, 1, 1, 1, 2, 2, 5, 5, 5]
def baseStart_6720363 : Nat := 118140960795 + 6720363 * 2 ^ 59
def prefixEnd_6720363 : Nat := 4983230072969 + 3 ^ 40 * 6720363 * 2
def baseEnd_6720363 : Nat := 383419599076821698061791

theorem tailTrace_6720363 : CollatzResearch.WordTrace tailWord_6720363 prefixEnd_6720363 383419599076821698061791 := by
  unfold tailWord_6720363
  simp only [CollatzResearch.WordTrace]
  refine ⟨245111775352280072468733743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163407850234853381645822495 245111775352280072468733743)
  ·
    refine ⟨367667663028420108703100615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245111775352280072468733743 367667663028420108703100615)
    ·
      refine ⟨551501494542630163054650923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 367667663028420108703100615 551501494542630163054650923)
      ·
        refine ⟨827252241813945244581976385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 551501494542630163054650923 827252241813945244581976385)
        ·
          refine ⟨620439181360458933436482289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 827252241813945244581976385 620439181360458933436482289)
          ·
            refine ⟨465329386020344200077361717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 620439181360458933436482289 465329386020344200077361717)
            ·
              refine ⟨43624629939407268757252661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 465329386020344200077361717 43624629939407268757252661)
              ·
                refine ⟨4089809056819431445992437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43624629939407268757252661 4089809056819431445992437)
                ·
                  refine ⟨383419599076821698061791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4089809056819431445992437 383419599076821698061791)
                  ·
                    rfl

theorem cell23_6720363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 5, 5].length) (baseStart_6720363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6720363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6720363 prefixEnd_6720363 := by exact prefixLift 6720363
  have htrace : WordTrace (prefixWord ++ tailWord_6720363) baseStart_6720363 baseEnd_6720363 := by
    simpa [prefixWord, tailWord_6720363, baseEnd_6720363] using wordTrace_append hprefix tailTrace_6720363
  have hstable : (prefixWord ++ tailWord_6720363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6720363).length < 2 ^ (prefixWord ++ tailWord_6720363).sum := by decide
  have hdescent : baseEnd_6720363 < baseStart_6720363 := by decide
  rcases family_descends (prefixWord ++ tailWord_6720363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6720374 : List Nat := [5, 1, 1, 3, 1, 2, 1, 1, 4, 2, 2]
def baseStart_6720374 : Nat := 118140960795 + 6720374 * 2 ^ 59
def prefixEnd_6720374 : Nat := 4983230072969 + 3 ^ 40 * 6720374 * 2
def baseEnd_6720374 : Nat := 3450782039978594739518569

theorem tailTrace_6720374 : CollatzResearch.WordTrace tailWord_6720374 prefixEnd_6720374 3450782039978594739518569 := by
  unfold tailWord_6720374
  simp only [CollatzResearch.WordTrace]
  refine ⟨15319511034702513834211511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 163408117703493480898256117 15319511034702513834211511)
  ·
    refine ⟨22979266552053770751317267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15319511034702513834211511 22979266552053770751317267)
    ·
      refine ⟨34468899828080656126975901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22979266552053770751317267 34468899828080656126975901)
      ·
        refine ⟨12925837435530246047615963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34468899828080656126975901 12925837435530246047615963)
        ·
          refine ⟨19388756153295369071423945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12925837435530246047615963 19388756153295369071423945)
          ·
            refine ⟨14541567114971526803567959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19388756153295369071423945 14541567114971526803567959)
            ·
              refine ⟨21812350672457290205351939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14541567114971526803567959 21812350672457290205351939)
              ·
                refine ⟨32718526008685935308027909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21812350672457290205351939 32718526008685935308027909)
                ·
                  refine ⟨6134723626628612870255233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32718526008685935308027909 6134723626628612870255233)
                  ·
                    refine ⟨4601042719971459652691425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6134723626628612870255233 4601042719971459652691425)
                    ·
                      refine ⟨3450782039978594739518569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4601042719971459652691425 3450782039978594739518569)
                      ·
                        rfl

theorem cell23_6720374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 1, 4, 2, 2].length) (baseStart_6720374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6720374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6720374 prefixEnd_6720374 := by exact prefixLift 6720374
  have htrace : WordTrace (prefixWord ++ tailWord_6720374) baseStart_6720374 baseEnd_6720374 := by
    simpa [prefixWord, tailWord_6720374, baseEnd_6720374] using wordTrace_append hprefix tailTrace_6720374
  have hstable : (prefixWord ++ tailWord_6720374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6720374).length < 2 ^ (prefixWord ++ tailWord_6720374).sum := by decide
  have hdescent : baseEnd_6720374 < baseStart_6720374 := by decide
  rcases family_descends (prefixWord ++ tailWord_6720374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6720383 : List Nat := [1, 1, 2, 2, 1, 1, 4, 1, 1, 7, 2]
def baseStart_6720383 : Nat := 118140960795 + 6720383 * 2 ^ 59
def prefixEnd_6720383 : Nat := 4983230072969 + 3 ^ 40 * 6720383 * 2
def baseEnd_6720383 : Nat := 3450786661304485204306027

theorem tailTrace_6720383 : CollatzResearch.WordTrace tailWord_6720383 prefixEnd_6720383 3450786661304485204306027 := by
  unfold tailWord_6720383
  simp only [CollatzResearch.WordTrace]
  refine ⟨245112504812207615884461803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163408336541471743922974535 245112504812207615884461803)
  ·
    refine ⟨367668757218311423826692705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245112504812207615884461803 367668757218311423826692705)
    ·
      refine ⟨275751567913733567870019529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 367668757218311423826692705 275751567913733567870019529)
      ·
        refine ⟨206813675935300175902514647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 275751567913733567870019529 206813675935300175902514647)
        ·
          refine ⟨310220513902950263853771971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206813675935300175902514647 310220513902950263853771971)
          ·
            refine ⟨465330770854425395780657957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 310220513902950263853771971 465330770854425395780657957)
            ·
              refine ⟨87249519535204761708873367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 465330770854425395780657957 87249519535204761708873367)
              ·
                refine ⟨130874279302807142563310051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87249519535204761708873367 130874279302807142563310051)
                ·
                  refine ⟨196311418954210713844965077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 130874279302807142563310051 196311418954210713844965077)
                  ·
                    refine ⟨4601048881739313605741369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 196311418954210713844965077 4601048881739313605741369)
                    ·
                      refine ⟨3450786661304485204306027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4601048881739313605741369 3450786661304485204306027)
                      ·
                        rfl

theorem cell23_6720383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 1, 1, 7, 2].length) (baseStart_6720383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6720383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6720383 prefixEnd_6720383 := by exact prefixLift 6720383
  have htrace : WordTrace (prefixWord ++ tailWord_6720383) baseStart_6720383 baseEnd_6720383 := by
    simpa [prefixWord, tailWord_6720383, baseEnd_6720383] using wordTrace_append hprefix tailTrace_6720383
  have hstable : (prefixWord ++ tailWord_6720383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6720383).length < 2 ^ (prefixWord ++ tailWord_6720383).sum := by decide
  have hdescent : baseEnd_6720383 < baseStart_6720383 := by decide
  rcases family_descends (prefixWord ++ tailWord_6720383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6720413 : List Nat := [1, 4, 2, 1, 2, 1, 1, 3, 1, 3, 4]
def baseStart_6720413 : Nat := 118140960795 + 6720413 * 2 ^ 59
def prefixEnd_6720413 : Nat := 4983230072969 + 3 ^ 40 * 6720413 * 2
def baseEnd_6720413 : Nat := 3450802065724120086930889

theorem tailTrace_6720413 : CollatzResearch.WordTrace tailWord_6720413 prefixEnd_6720413 3450802065724120086930889 := by
  unfold tailWord_6720413
  simp only [CollatzResearch.WordTrace]
  refine ⟨245113599002098931008053893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163409066001399287338702595 245113599002098931008053893)
  ·
    refine ⟨45958799812893549564010105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 245113599002098931008053893 45958799812893549564010105)
    ·
      refine ⟨34469099859670162173007579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45958799812893549564010105 34469099859670162173007579)
      ·
        refine ⟨51703649789505243259511369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34469099859670162173007579 51703649789505243259511369)
        ·
          refine ⟨38777737342128932444633527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51703649789505243259511369 38777737342128932444633527)
          ·
            refine ⟨58166606013193398666950291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38777737342128932444633527 58166606013193398666950291)
            ·
              refine ⟨87249909019790098000425437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58166606013193398666950291 87249909019790098000425437)
              ·
                refine ⟨32718715882421286750159539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 87249909019790098000425437 32718715882421286750159539)
                ·
                  refine ⟨49078073823631930125239309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32718715882421286750159539 49078073823631930125239309)
                  ·
                    refine ⟨18404277683861973796964741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49078073823631930125239309 18404277683861973796964741)
                    ·
                      refine ⟨3450802065724120086930889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18404277683861973796964741 3450802065724120086930889)
                      ·
                        rfl

theorem cell23_6720413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 3, 1, 3, 4].length) (baseStart_6720413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6720413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6720413 prefixEnd_6720413 := by exact prefixLift 6720413
  have htrace : WordTrace (prefixWord ++ tailWord_6720413) baseStart_6720413 baseEnd_6720413 := by
    simpa [prefixWord, tailWord_6720413, baseEnd_6720413] using wordTrace_append hprefix tailTrace_6720413
  have hstable : (prefixWord ++ tailWord_6720413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6720413).length < 2 ^ (prefixWord ++ tailWord_6720413).sum := by decide
  have hdescent : baseEnd_6720413 < baseStart_6720413 := by decide
  rcases family_descends (prefixWord ++ tailWord_6720413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6720440 : List Nat := [2, 1, 2, 1, 2, 4, 3, 1, 3, 4]
def baseStart_6720440 : Nat := 118140960795 + 6720440 * 2 ^ 59
def prefixEnd_6720440 : Nat := 4983230072969 + 3 ^ 40 * 6720440 * 2
def baseEnd_6720440 : Nat := 1150271976567263827097755

theorem tailTrace_6720440 : CollatzResearch.WordTrace tailWord_6720440 prefixEnd_6720440 1150271976567263827097755 := by
  unfold tailWord_6720440
  simp only [CollatzResearch.WordTrace]
  refine ⟨122557291886500557309643387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163409722515334076412857849 122557291886500557309643387)
  ·
    refine ⟨183835937829750835964465081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122557291886500557309643387 183835937829750835964465081)
    ·
      refine ⟨137876953372313126973348811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183835937829750835964465081 137876953372313126973348811)
      ·
        refine ⟨206815430058469690460023217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137876953372313126973348811 206815430058469690460023217)
        ·
          refine ⟨155111572543852267845017413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 206815430058469690460023217 155111572543852267845017413)
          ·
            refine ⟨29083419851972300220940765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 155111572543852267845017413 29083419851972300220940765)
            ·
              refine ⟨10906282444489612582852787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29083419851972300220940765 10906282444489612582852787)
              ·
                refine ⟨16359423666734418874279181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10906282444489612582852787 16359423666734418874279181)
                ·
                  refine ⟨6134783875025407077854693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16359423666734418874279181 6134783875025407077854693)
                  ·
                    refine ⟨1150271976567263827097755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6134783875025407077854693 1150271976567263827097755)
                    ·
                      rfl

theorem cell23_6720440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 3, 1, 3, 4].length) (baseStart_6720440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6720440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6720440 prefixEnd_6720440 := by exact prefixLift 6720440
  have htrace : WordTrace (prefixWord ++ tailWord_6720440) baseStart_6720440 baseEnd_6720440 := by
    simpa [prefixWord, tailWord_6720440, baseEnd_6720440] using wordTrace_append hprefix tailTrace_6720440
  have hstable : (prefixWord ++ tailWord_6720440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6720440).length < 2 ^ (prefixWord ++ tailWord_6720440).sum := by decide
  have hdescent : baseEnd_6720440 < baseStart_6720440 := by decide
  rcases family_descends (prefixWord ++ tailWord_6720440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6720461 : List Nat := [1, 6, 3, 1, 1, 1, 2, 1, 2, 5]
def baseStart_6720461 : Nat := 118140960795 + 6720461 * 2 ^ 59
def prefixEnd_6720461 : Nat := 4983230072969 + 3 ^ 40 * 6720461 * 2
def baseEnd_6720461 : Nat := 1150275570931845299710223

theorem tailTrace_6720461 : CollatzResearch.WordTrace tailWord_6720461 prefixEnd_6720461 1150275570931845299710223 := by
  unfold tailWord_6720461
  simp only [CollatzResearch.WordTrace]
  refine ⟨245115349705925035205801237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163410233137283356803867491 245115349705925035205801237)
  ·
    refine ⟨11489782017465236025271933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 245115349705925035205801237 11489782017465236025271933)
    ·
      refine ⟨4308668256549463509476975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11489782017465236025271933 4308668256549463509476975)
      ·
        refine ⟨6463002384824195264215463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4308668256549463509476975 6463002384824195264215463)
        ·
          refine ⟨9694503577236292896323195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6463002384824195264215463 9694503577236292896323195)
          ·
            refine ⟨14541755365854439344484793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9694503577236292896323195 14541755365854439344484793)
            ·
              refine ⟨10906316524390829508363595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14541755365854439344484793 10906316524390829508363595)
              ·
                refine ⟨16359474786586244262545393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10906316524390829508363595 16359474786586244262545393)
                ·
                  refine ⟨12269606089939683196909045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16359474786586244262545393 12269606089939683196909045)
                  ·
                    refine ⟨1150275570931845299710223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12269606089939683196909045 1150275570931845299710223)
                    ·
                      rfl

theorem cell23_6720461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_6720461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6720461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6720461 prefixEnd_6720461 := by exact prefixLift 6720461
  have htrace : WordTrace (prefixWord ++ tailWord_6720461) baseStart_6720461 baseEnd_6720461 := by
    simpa [prefixWord, tailWord_6720461, baseEnd_6720461] using wordTrace_append hprefix tailTrace_6720461
  have hstable : (prefixWord ++ tailWord_6720461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6720461).length < 2 ^ (prefixWord ++ tailWord_6720461).sum := by decide
  have hdescent : baseEnd_6720461 < baseStart_6720461 := by decide
  rcases family_descends (prefixWord ++ tailWord_6720461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6720520 : List Nat := [2, 1, 3, 2, 1, 3, 2, 1, 3, 1, 4]
def baseStart_6720520 : Nat := 118140960795 + 6720520 * 2 ^ 59
def prefixEnd_6720520 : Nat := 4983230072969 + 3 ^ 40 * 6720520 * 2
def baseEnd_6720520 : Nat := 3450857008154151168292897

theorem tailTrace_6720520 : CollatzResearch.WordTrace tailWord_6720520 prefixEnd_6720520 3450857008154151168292897 := by
  unfold tailWord_6720520
  simp only [CollatzResearch.WordTrace]
  refine ⟨122558750806355644141099507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163411667741807525521466009 122558750806355644141099507)
  ·
    refine ⟨183838126209533466211649261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122558750806355644141099507 183838126209533466211649261)
    ·
      refine ⟨68939297328575049829368473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 183838126209533466211649261 68939297328575049829368473)
      ·
        refine ⟨51704472996431287372026355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68939297328575049829368473 51704472996431287372026355)
        ·
          refine ⟨77556709494646931058039533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51704472996431287372026355 77556709494646931058039533)
          ·
            refine ⟨29083766060492599146764825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77556709494646931058039533 29083766060492599146764825)
            ·
              refine ⟨21812824545369449360073619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29083766060492599146764825 21812824545369449360073619)
              ·
                refine ⟨32719236818054174040110429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21812824545369449360073619 32719236818054174040110429)
                ·
                  refine ⟨12269713806770315265041411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32719236818054174040110429 12269713806770315265041411)
                  ·
                    refine ⟨18404570710155472897562117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12269713806770315265041411 18404570710155472897562117)
                    ·
                      refine ⟨3450857008154151168292897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18404570710155472897562117 3450857008154151168292897)
                      ·
                        rfl

theorem cell23_6720520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 1, 3, 1, 4].length) (baseStart_6720520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6720520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6720520 prefixEnd_6720520 := by exact prefixLift 6720520
  have htrace : WordTrace (prefixWord ++ tailWord_6720520) baseStart_6720520 baseEnd_6720520 := by
    simpa [prefixWord, tailWord_6720520, baseEnd_6720520] using wordTrace_append hprefix tailTrace_6720520
  have hstable : (prefixWord ++ tailWord_6720520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6720520).length < 2 ^ (prefixWord ++ tailWord_6720520).sum := by decide
  have hdescent : baseEnd_6720520 < baseStart_6720520 := by decide
  rcases family_descends (prefixWord ++ tailWord_6720520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6720524 : List Nat := [2, 2, 1, 2, 3, 4, 1, 1, 2, 3, 2]
def baseStart_6720524 : Nat := 118140960795 + 6720524 * 2 ^ 59
def prefixEnd_6720524 : Nat := 4983230072969 + 3 ^ 40 * 6720524 * 2
def baseEnd_6720524 : Nat := 3450859062076769152642879

theorem tailTrace_6720524 : CollatzResearch.WordTrace tailWord_6720524 prefixEnd_6720524 3450859062076769152642879 := by
  unfold tailWord_6720524
  simp only [CollatzResearch.WordTrace]
  refine ⟨122558823752348398482672313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163411765003131197976896417 122558823752348398482672313)
  ·
    refine ⟨91919117814261298862004235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122558823752348398482672313 91919117814261298862004235)
    ·
      refine ⟨137878676721391948293006353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91919117814261298862004235 137878676721391948293006353)
      ·
        refine ⟨103409007541043961219754765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137878676721391948293006353 103409007541043961219754765)
        ·
          refine ⟨38778377827891485457408037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103409007541043961219754765 38778377827891485457408037)
          ·
            refine ⟨7270945842729653523264007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38778377827891485457408037 7270945842729653523264007)
            ·
              refine ⟨10906418764094480284896011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7270945842729653523264007 10906418764094480284896011)
              ·
                refine ⟨16359628146141720427344017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10906418764094480284896011 16359628146141720427344017)
                ·
                  refine ⟨12269721109606290320508013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16359628146141720427344017 12269721109606290320508013)
                  ·
                    refine ⟨4601145416102358870190505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12269721109606290320508013 4601145416102358870190505)
                    ·
                      refine ⟨3450859062076769152642879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4601145416102358870190505 3450859062076769152642879)
                      ·
                        rfl

theorem cell23_6720524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 1, 1, 2, 3, 2].length) (baseStart_6720524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6720524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6720524 prefixEnd_6720524 := by exact prefixLift 6720524
  have htrace : WordTrace (prefixWord ++ tailWord_6720524) baseStart_6720524 baseEnd_6720524 := by
    simpa [prefixWord, tailWord_6720524, baseEnd_6720524] using wordTrace_append hprefix tailTrace_6720524
  have hstable : (prefixWord ++ tailWord_6720524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6720524).length < 2 ^ (prefixWord ++ tailWord_6720524).sum := by decide
  have hdescent : baseEnd_6720524 < baseStart_6720524 := by decide
  rcases family_descends (prefixWord ++ tailWord_6720524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6720537 : List Nat := [1, 2, 1, 2, 1, 1, 8, 1, 1, 1, 4]
def baseStart_6720537 : Nat := 118140960795 + 6720537 * 2 ^ 59
def prefixEnd_6720537 : Nat := 4983230072969 + 3 ^ 40 * 6720537 * 2
def baseEnd_6720537 : Nat := 3450865737325277601780319

theorem tailTrace_6720537 : CollatzResearch.WordTrace tailWord_6720537 prefixEnd_6720537 3450865737325277601780319 := by
  unfold tailWord_6720537
  simp only [CollatzResearch.WordTrace]
  refine ⟨245118121653649700185567865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163412081102433133457045243 245118121653649700185567865)
  ·
    refine ⟨183838591240237275139175899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245118121653649700185567865 183838591240237275139175899)
    ·
      refine ⟨275757886860355912708763849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183838591240237275139175899 275757886860355912708763849)
      ·
        refine ⟨206818415145266934531572887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 275757886860355912708763849 206818415145266934531572887)
        ·
          refine ⟨310227622717900401797359331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206818415145266934531572887 310227622717900401797359331)
          ·
            refine ⟨465341434076850602696038997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 310227622717900401797359331 465341434076850602696038997)
            ·
              refine ⟨5453219930588093000344207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 465341434076850602696038997 5453219930588093000344207)
              ·
                refine ⟨8179829895882139500516311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5453219930588093000344207 8179829895882139500516311)
                ·
                  refine ⟨12269744843823209250774467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8179829895882139500516311 12269744843823209250774467)
                  ·
                    refine ⟨18404617265734813876161701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12269744843823209250774467 18404617265734813876161701)
                    ·
                      refine ⟨3450865737325277601780319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18404617265734813876161701 3450865737325277601780319)
                      ·
                        rfl

theorem cell23_6720537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 8, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 8, 1, 1, 1, 4].length) (baseStart_6720537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6720537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6720537 prefixEnd_6720537 := by exact prefixLift 6720537
  have htrace : WordTrace (prefixWord ++ tailWord_6720537) baseStart_6720537 baseEnd_6720537 := by
    simpa [prefixWord, tailWord_6720537, baseEnd_6720537] using wordTrace_append hprefix tailTrace_6720537
  have hstable : (prefixWord ++ tailWord_6720537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6720537).length < 2 ^ (prefixWord ++ tailWord_6720537).sum := by decide
  have hdescent : baseEnd_6720537 < baseStart_6720537 := by decide
  rcases family_descends (prefixWord ++ tailWord_6720537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6720543 : List Nat := [1, 1, 2, 4, 1, 4, 10]
def baseStart_6720543 : Nat := 118140960795 + 6720543 * 2 ^ 59
def prefixEnd_6720543 : Nat := 4983230072969 + 3 ^ 40 * 6720543 * 2
def baseEnd_6720543 : Nat := 42603318743323513312411

theorem tailTrace_6720543 : CollatzResearch.WordTrace tailWord_6720543 prefixEnd_6720543 42603318743323513312411 := by
  unfold tailWord_6720543
  simp only [CollatzResearch.WordTrace]
  refine ⟨245118340491627963210286283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163412226994418642140190855 245118340491627963210286283)
  ·
    refine ⟨367677510737441944815429425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245118340491627963210286283 367677510737441944815429425)
    ·
      refine ⟨275758133053081458611572069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 367677510737441944815429425 275758133053081458611572069)
      ·
        refine ⟨51704649947452773489669763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 275758133053081458611572069 51704649947452773489669763)
        ·
          refine ⟨77556974921179160234504645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51704649947452773489669763 77556974921179160234504645)
          ·
            refine ⟨14541932797721092543969621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 77556974921179160234504645 14541932797721092543969621)
            ·
              refine ⟨42603318743323513312411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 14541932797721092543969621 42603318743323513312411)
              ·
                rfl

theorem cell23_6720543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 10].length) (baseStart_6720543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6720543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6720543 prefixEnd_6720543 := by exact prefixLift 6720543
  have htrace : WordTrace (prefixWord ++ tailWord_6720543) baseStart_6720543 baseEnd_6720543 := by
    simpa [prefixWord, tailWord_6720543, baseEnd_6720543] using wordTrace_append hprefix tailTrace_6720543
  have hstable : (prefixWord ++ tailWord_6720543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6720543).length < 2 ^ (prefixWord ++ tailWord_6720543).sum := by decide
  have hdescent : baseEnd_6720543 < baseStart_6720543 := by decide
  rcases family_descends (prefixWord ++ tailWord_6720543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6720547 : List Nat := [1, 1, 1, 4, 3, 2, 3, 2, 2, 4]
def baseStart_6720547 : Nat := 118140960795 + 6720547 * 2 ^ 59
def prefixEnd_6720547 : Nat := 4983230072969 + 3 ^ 40 * 6720547 * 2
def baseEnd_6720547 : Nat := 1150290290710607520885091

theorem tailTrace_6720547 : CollatzResearch.WordTrace tailWord_6720547 prefixEnd_6720547 1150290290710607520885091 := by
  unfold tailWord_6720547
  simp only [CollatzResearch.WordTrace]
  refine ⟨245118486383613471893431895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163412324255742314595621263 245118486383613471893431895)
  ·
    refine ⟨367677729575420207840147843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245118486383613471893431895 367677729575420207840147843)
    ·
      refine ⟨551516594363130311760221765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 367677729575420207840147843 551516594363130311760221765)
      ·
        refine ⟨103409361443086933455041581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 551516594363130311760221765 103409361443086933455041581)
        ·
          refine ⟨38778510541157600045640593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103409361443086933455041581 38778510541157600045640593)
          ·
            refine ⟨29083882905868200034230445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38778510541157600045640593 29083882905868200034230445)
            ·
              refine ⟨10906456089700575012836417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29083882905868200034230445 10906456089700575012836417)
              ·
                refine ⟨8179842067275431259627313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10906456089700575012836417 8179842067275431259627313)
                ·
                  refine ⟨6134881550456573444720485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8179842067275431259627313 6134881550456573444720485)
                  ·
                    refine ⟨1150290290710607520885091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6134881550456573444720485 1150290290710607520885091)
                    ·
                      rfl

theorem cell23_6720547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 3, 2, 2, 4].length) (baseStart_6720547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6720547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6720547 prefixEnd_6720547 := by exact prefixLift 6720547
  have htrace : WordTrace (prefixWord ++ tailWord_6720547) baseStart_6720547 baseEnd_6720547 := by
    simpa [prefixWord, tailWord_6720547, baseEnd_6720547] using wordTrace_append hprefix tailTrace_6720547
  have hstable : (prefixWord ++ tailWord_6720547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6720547).length < 2 ^ (prefixWord ++ tailWord_6720547).sum := by decide
  have hdescent : baseEnd_6720547 < baseStart_6720547 := by decide
  rcases family_descends (prefixWord ++ tailWord_6720547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6720564 : List Nat := [2, 5, 1, 2, 1, 3, 1, 1, 1, 6]
def baseStart_6720564 : Nat := 118140960795 + 6720564 * 2 ^ 59
def prefixEnd_6720564 : Nat := 4983230072969 + 3 ^ 40 * 6720564 * 2
def baseEnd_6720564 : Nat := 1150293200434316332047565

theorem tailTrace_6720564 : CollatzResearch.WordTrace tailWord_6720564 prefixEnd_6720564 1150293200434316332047565 := by
  unfold tailWord_6720564
  simp only [CollatzResearch.WordTrace]
  refine ⟨122559553212275941898400373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163412737616367922531200497 122559553212275941898400373)
  ·
    refine ⟨11489958113650869552975035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 122559553212275941898400373 11489958113650869552975035)
    ·
      refine ⟨17234937170476304329462553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11489958113650869552975035 17234937170476304329462553)
      ·
        refine ⟨12926202877857228247096915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17234937170476304329462553 12926202877857228247096915)
        ·
          refine ⟨19389304316785842370645373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12926202877857228247096915 19389304316785842370645373)
          ·
            refine ⟨7270989118794690888992015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19389304316785842370645373 7270989118794690888992015)
            ·
              refine ⟨10906483678192036333488023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7270989118794690888992015 10906483678192036333488023)
              ·
                refine ⟨16359725517288054500232035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10906483678192036333488023 16359725517288054500232035)
                ·
                  refine ⟨24539588275932081750348053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16359725517288054500232035 24539588275932081750348053)
                  ·
                    refine ⟨1150293200434316332047565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24539588275932081750348053 1150293200434316332047565)
                    ·
                      rfl

theorem cell23_6720564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 1, 1, 1, 6].length) (baseStart_6720564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6720564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6720564 prefixEnd_6720564 := by exact prefixLift 6720564
  have htrace : WordTrace (prefixWord ++ tailWord_6720564) baseStart_6720564 baseEnd_6720564 := by
    simpa [prefixWord, tailWord_6720564, baseEnd_6720564] using wordTrace_append hprefix tailTrace_6720564
  have hstable : (prefixWord ++ tailWord_6720564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6720564).length < 2 ^ (prefixWord ++ tailWord_6720564).sum := by decide
  have hdescent : baseEnd_6720564 < baseStart_6720564 := by decide
  rcases family_descends (prefixWord ++ tailWord_6720564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6720574 : List Nat := [4, 2, 1, 3, 1, 1, 1, 4, 1, 2, 3]
def baseStart_6720574 : Nat := 118140960795 + 6720574 * 2 ^ 59
def prefixEnd_6720574 : Nat := 4983230072969 + 3 ^ 40 * 6720574 * 2
def baseEnd_6720574 : Nat := 3450884736109493957017649

theorem tailTrace_6720574 : CollatzResearch.WordTrace tailWord_6720574 prefixEnd_6720574 3450884736109493957017649 := by
  unfold tailWord_6720574
  simp only [CollatzResearch.WordTrace]
  refine ⟨30639933894314456938083097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 163412980769677103669776517 30639933894314456938083097)
  ·
    refine ⟨22979950420735842703562323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30639933894314456938083097 22979950420735842703562323)
    ·
      refine ⟨34469925631103764055343485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22979950420735842703562323 34469925631103764055343485)
      ·
        refine ⟨12926222111663911520753807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34469925631103764055343485 12926222111663911520753807)
        ·
          refine ⟨19389333167495867281130711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12926222111663911520753807 19389333167495867281130711)
          ·
            refine ⟨29083999751243800921696067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19389333167495867281130711 29083999751243800921696067)
            ·
              refine ⟨43625999626865701382544101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29083999751243800921696067 43625999626865701382544101)
              ·
                refine ⟨8179874930037319009227019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43625999626865701382544101 8179874930037319009227019)
                ·
                  refine ⟨12269812395055978513840529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8179874930037319009227019 12269812395055978513840529)
                  ·
                    refine ⟨9202359296291983885380397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12269812395055978513840529 9202359296291983885380397)
                    ·
                      refine ⟨3450884736109493957017649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9202359296291983885380397 3450884736109493957017649)
                      ·
                        rfl

theorem cell23_6720574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 4, 1, 2, 3].length) (baseStart_6720574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6720574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6720574 prefixEnd_6720574 := by exact prefixLift 6720574
  have htrace : WordTrace (prefixWord ++ tailWord_6720574) baseStart_6720574 baseEnd_6720574 := by
    simpa [prefixWord, tailWord_6720574, baseEnd_6720574] using wordTrace_append hprefix tailTrace_6720574
  have hstable : (prefixWord ++ tailWord_6720574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6720574).length < 2 ^ (prefixWord ++ tailWord_6720574).sum := by decide
  have hdescent : baseEnd_6720574 < baseStart_6720574 := by decide
  rcases family_descends (prefixWord ++ tailWord_6720574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6720604 : List Nat := [2, 2, 4, 1, 1, 1, 2, 4, 2, 1, 3]
def baseStart_6720604 : Nat := 118140960795 + 6720604 * 2 ^ 59
def prefixEnd_6720604 : Nat := 4983230072969 + 3 ^ 40 * 6720604 * 2
def baseEnd_6720604 : Nat := 3450900140529128839642511

theorem tailTrace_6720604 : CollatzResearch.WordTrace tailWord_6720604 prefixEnd_6720604 3450900140529128839642511 := by
  unfold tailWord_6720604
  simp only [CollatzResearch.WordTrace]
  refine ⟨122560282672203485314128433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163413710229604647085504577 122560282672203485314128433)
  ·
    refine ⟨91920212004152613985596325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122560282672203485314128433 91920212004152613985596325)
    ·
      refine ⟨17235039750778615122299311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91920212004152613985596325 17235039750778615122299311)
      ·
        refine ⟨25852559626167922683448967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17235039750778615122299311 25852559626167922683448967)
        ·
          refine ⟨38778839439251884025173451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25852559626167922683448967 38778839439251884025173451)
          ·
            refine ⟨58168259158877826037760177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38778839439251884025173451 58168259158877826037760177)
            ·
              refine ⟨43626194369158369528320133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58168259158877826037760177 43626194369158369528320133)
              ·
                refine ⟨8179911444217194286560025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43626194369158369528320133 8179911444217194286560025)
                ·
                  refine ⟨6134933583162895714920019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8179911444217194286560025 6134933583162895714920019)
                  ·
                    refine ⟨9202400374744343572380029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6134933583162895714920019 9202400374744343572380029)
                    ·
                      refine ⟨3450900140529128839642511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9202400374744343572380029 3450900140529128839642511)
                      ·
                        rfl

theorem cell23_6720604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 4, 2, 1, 3].length) (baseStart_6720604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6720604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6720604 prefixEnd_6720604 := by exact prefixLift 6720604
  have htrace : WordTrace (prefixWord ++ tailWord_6720604) baseStart_6720604 baseEnd_6720604 := by
    simpa [prefixWord, tailWord_6720604, baseEnd_6720604] using wordTrace_append hprefix tailTrace_6720604
  have hstable : (prefixWord ++ tailWord_6720604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6720604).length < 2 ^ (prefixWord ++ tailWord_6720604).sum := by decide
  have hdescent : baseEnd_6720604 < baseStart_6720604 := by decide
  rcases family_descends (prefixWord ++ tailWord_6720604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6720605 : List Nat := [1, 4, 4, 1, 3, 1, 1, 1, 3, 2, 2]
def baseStart_6720605 : Nat := 118140960795 + 6720605 * 2 ^ 59
def prefixEnd_6720605 : Nat := 4983230072969 + 3 ^ 40 * 6720605 * 2
def baseEnd_6720605 : Nat := 3450900654009783335730007

theorem tailTrace_6720605 : CollatzResearch.WordTrace tailWord_6720605 prefixEnd_6720605 3450900654009783335730007 := by
  unfold tailWord_6720605
  simp only [CollatzResearch.WordTrace]
  refine ⟨245120601817403347799043269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163413734544935565199362179 245120601817403347799043269)
  ·
    refine ⟨45960112840763127712320613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 245120601817403347799043269 45960112840763127712320613)
    ·
      refine ⟨8617521157643086446060115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45960112840763127712320613 8617521157643086446060115)
      ·
        refine ⟨12926281736464629669090173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8617521157643086446060115 12926281736464629669090173)
        ·
          refine ⟨4847355651174236125908815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12926281736464629669090173 4847355651174236125908815)
          ·
            refine ⟨7271033476761354188863223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4847355651174236125908815 7271033476761354188863223)
            ·
              refine ⟨10906550215142031283294835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7271033476761354188863223 10906550215142031283294835)
              ·
                refine ⟨16359825322713046924942253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10906550215142031283294835 16359825322713046924942253)
                ·
                  refine ⟨6134934496017392596853345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16359825322713046924942253 6134934496017392596853345)
                  ·
                    refine ⟨4601200872013044447640009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6134934496017392596853345 4601200872013044447640009)
                    ·
                      refine ⟨3450900654009783335730007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4601200872013044447640009 3450900654009783335730007)
                      ·
                        rfl

theorem cell23_6720605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 1, 1, 3, 2, 2].length) (baseStart_6720605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6720605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6720605 prefixEnd_6720605 := by exact prefixLift 6720605
  have htrace : WordTrace (prefixWord ++ tailWord_6720605) baseStart_6720605 baseEnd_6720605 := by
    simpa [prefixWord, tailWord_6720605, baseEnd_6720605] using wordTrace_append hprefix tailTrace_6720605
  have hstable : (prefixWord ++ tailWord_6720605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6720605).length < 2 ^ (prefixWord ++ tailWord_6720605).sum := by decide
  have hdescent : baseEnd_6720605 < baseStart_6720605 := by decide
  rcases family_descends (prefixWord ++ tailWord_6720605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6720621 : List Nat := [1, 5, 1, 1, 2, 2, 4, 1, 2, 1, 3]
def baseStart_6720621 : Nat := 118140960795 + 6720621 * 2 ^ 59
def prefixEnd_6720621 : Nat := 4983230072969 + 3 ^ 40 * 6720621 * 2
def baseEnd_6720621 : Nat := 3450908869700255273129933

theorem tailTrace_6720621 : CollatzResearch.WordTrace tailWord_6720621 prefixEnd_6720621 3450908869700255273129933 := by
  unfold tailWord_6720621
  simp only [CollatzResearch.WordTrace]
  refine ⟨245121185385345382531625717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163414123590230255021083811 245121185385345382531625717)
  ·
    refine ⟨22980111129876129612339911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 245121185385345382531625717 22980111129876129612339911)
    ·
      refine ⟨34470166694814194418509867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22980111129876129612339911 34470166694814194418509867)
      ·
        refine ⟨51705250042221291627764801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34470166694814194418509867 51705250042221291627764801)
        ·
          refine ⟨38778937531665968720823601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51705250042221291627764801 38778937531665968720823601)
          ·
            refine ⟨29084203148749476540617701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38778937531665968720823601 29084203148749476540617701)
            ·
              refine ⟨5453288090390526851365819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29084203148749476540617701 5453288090390526851365819)
              ·
                refine ⟨8179932135585790277048729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5453288090390526851365819 8179932135585790277048729)
                ·
                  refine ⟨6134949101689342707786547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8179932135585790277048729 6134949101689342707786547)
                  ·
                    refine ⟨9202423652534014061679821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6134949101689342707786547 9202423652534014061679821)
                    ·
                      refine ⟨3450908869700255273129933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9202423652534014061679821 3450908869700255273129933)
                      ·
                        rfl

theorem cell23_6720621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 4, 1, 2, 1, 3].length) (baseStart_6720621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6720621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6720621 prefixEnd_6720621 := by exact prefixLift 6720621
  have htrace : WordTrace (prefixWord ++ tailWord_6720621) baseStart_6720621 baseEnd_6720621 := by
    simpa [prefixWord, tailWord_6720621, baseEnd_6720621] using wordTrace_append hprefix tailTrace_6720621
  have hstable : (prefixWord ++ tailWord_6720621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6720621).length < 2 ^ (prefixWord ++ tailWord_6720621).sum := by decide
  have hdescent : baseEnd_6720621 < baseStart_6720621 := by decide
  rcases family_descends (prefixWord ++ tailWord_6720621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6720638 : List Nat := [4, 2, 4, 1, 1, 1, 1, 2, 1, 3, 3]
def baseStart_6720638 : Nat := 118140960795 + 6720638 * 2 ^ 59
def prefixEnd_6720638 : Nat := 4983230072969 + 3 ^ 40 * 6720638 * 2
def baseEnd_6720638 : Nat := 3450917598871381706617355

theorem tailTrace_6720638 : CollatzResearch.WordTrace tailWord_6720638 prefixEnd_6720638 3450917598871381706617355 := by
  unfold tailWord_6720638
  simp only [CollatzResearch.WordTrace]
  refine ⟨30640225678285474304374321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 163414536950855862956663045 30640225678285474304374321)
  ·
    refine ⟨22980169258714105728280741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30640225678285474304374321 22980169258714105728280741)
    ·
      refine ⟨4308781736008894824052639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22980169258714105728280741 4308781736008894824052639)
      ·
        refine ⟨6463172604013342236078959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4308781736008894824052639 6463172604013342236078959)
        ·
          refine ⟨9694758906020013354118439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6463172604013342236078959 9694758906020013354118439)
          ·
            refine ⟨14542138359030020031177659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9694758906020013354118439 14542138359030020031177659)
            ·
              refine ⟨21813207538545030046766489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14542138359030020031177659 21813207538545030046766489)
              ·
                refine ⟨16359905653908772535074867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21813207538545030046766489 16359905653908772535074867)
                ·
                  refine ⟨24539858480863158802612301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16359905653908772535074867 24539858480863158802612301)
                  ·
                    refine ⟨9202446930323684550979613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24539858480863158802612301 9202446930323684550979613)
                    ·
                      refine ⟨3450917598871381706617355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9202446930323684550979613 3450917598871381706617355)
                      ·
                        rfl

theorem cell23_6720638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_6720638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6720638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6720638 prefixEnd_6720638 := by exact prefixLift 6720638
  have htrace : WordTrace (prefixWord ++ tailWord_6720638) baseStart_6720638 baseEnd_6720638 := by
    simpa [prefixWord, tailWord_6720638, baseEnd_6720638] using wordTrace_append hprefix tailTrace_6720638
  have hstable : (prefixWord ++ tailWord_6720638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6720638).length < 2 ^ (prefixWord ++ tailWord_6720638).sum := by decide
  have hdescent : baseEnd_6720638 < baseStart_6720638 := by decide
  rcases family_descends (prefixWord ++ tailWord_6720638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6720644 : List Nat := [2, 3, 2, 1, 2, 3, 1, 2, 1, 4, 2]
def baseStart_6720644 : Nat := 118140960795 + 6720644 * 2 ^ 59
def prefixEnd_6720644 : Nat := 4983230072969 + 3 ^ 40 * 6720644 * 2
def baseEnd_6720644 : Nat := 3450920679755308683142327

theorem tailTrace_6720644 : CollatzResearch.WordTrace tailWord_6720644 prefixEnd_6720644 3450920679755308683142327 := by
  unfold tailWord_6720644
  simp only [CollatzResearch.WordTrace]
  refine ⟨122561012132131028729856493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163414682842841371639808657 122561012132131028729856493)
  ·
    refine ⟨45960379549549135773696185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122561012132131028729856493 45960379549549135773696185)
    ·
      refine ⟨34470284662161851830272139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45960379549549135773696185 34470284662161851830272139)
      ·
        refine ⟨51705426993242777745408209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34470284662161851830272139 51705426993242777745408209)
        ·
          refine ⟨38779070244932083309056157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51705426993242777745408209 38779070244932083309056157)
          ·
            refine ⟨14542151341849531240896059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38779070244932083309056157 14542151341849531240896059)
            ·
              refine ⟨21813227012774296861344089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14542151341849531240896059 21813227012774296861344089)
              ·
                refine ⟨16359920259580722646008067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21813227012774296861344089 16359920259580722646008067)
                ·
                  refine ⟨24539880389371083969012101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16359920259580722646008067 24539880389371083969012101)
                  ·
                    refine ⟨4601227573007078244189769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24539880389371083969012101 4601227573007078244189769)
                    ·
                      refine ⟨3450920679755308683142327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4601227573007078244189769 3450920679755308683142327)
                      ·
                        rfl

theorem cell23_6720644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 2, 1, 4, 2].length) (baseStart_6720644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6720644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6720644 prefixEnd_6720644 := by exact prefixLift 6720644
  have htrace : WordTrace (prefixWord ++ tailWord_6720644) baseStart_6720644 baseEnd_6720644 := by
    simpa [prefixWord, tailWord_6720644, baseEnd_6720644] using wordTrace_append hprefix tailTrace_6720644
  have hstable : (prefixWord ++ tailWord_6720644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6720644).length < 2 ^ (prefixWord ++ tailWord_6720644).sum := by decide
  have hdescent : baseEnd_6720644 < baseStart_6720644 := by decide
  rcases family_descends (prefixWord ++ tailWord_6720644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6720648 : List Nat := [2, 1, 3, 4, 2, 1, 3, 1, 1, 3, 2]
def baseStart_6720648 : Nat := 118140960795 + 6720648 * 2 ^ 59
def prefixEnd_6720648 : Nat := 4983230072969 + 3 ^ 40 * 6720648 * 2
def baseEnd_6720648 : Nat := 3450922733677926667492309

theorem tailTrace_6720648 : CollatzResearch.WordTrace tailWord_6720648 prefixEnd_6720648 3450922733677926667492309 := by
  unfold tailWord_6720648
  simp only [CollatzResearch.WordTrace]
  refine ⟨122561085078123783071429299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163414780104165044095239065 122561085078123783071429299)
  ·
    refine ⟨183841627617185674607143949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122561085078123783071429299 183841627617185674607143949)
    ·
      refine ⟨68940610356444627977678981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 183841627617185674607143949 68940610356444627977678981)
      ·
        refine ⟨12926364441833367745814809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68940610356444627977678981 12926364441833367745814809)
        ·
          refine ⟨9694773331375025809361107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12926364441833367745814809 9694773331375025809361107)
          ·
            refine ⟨14542159997062538714041661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9694773331375025809361107 14542159997062538714041661)
            ·
              refine ⟨5453309998898452017765623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14542159997062538714041661 5453309998898452017765623)
              ·
                refine ⟨8179964998347678026648435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5453309998898452017765623 8179964998347678026648435)
                ·
                  refine ⟨12269947497521517039972653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8179964998347678026648435 12269947497521517039972653)
                  ·
                    refine ⟨4601230311570568889989745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12269947497521517039972653 4601230311570568889989745)
                    ·
                      refine ⟨3450922733677926667492309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4601230311570568889989745 3450922733677926667492309)
                      ·
                        rfl

theorem cell23_6720648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 3, 1, 1, 3, 2].length) (baseStart_6720648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6720648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6720648 prefixEnd_6720648 := by exact prefixLift 6720648
  have htrace : WordTrace (prefixWord ++ tailWord_6720648) baseStart_6720648 baseEnd_6720648 := by
    simpa [prefixWord, tailWord_6720648, baseEnd_6720648] using wordTrace_append hprefix tailTrace_6720648
  have hstable : (prefixWord ++ tailWord_6720648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6720648).length < 2 ^ (prefixWord ++ tailWord_6720648).sum := by decide
  have hdescent : baseEnd_6720648 < baseStart_6720648 := by decide
  rcases family_descends (prefixWord ++ tailWord_6720648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6720674 : List Nat := [3, 3, 1, 3, 2, 1, 1, 1, 2, 2, 4]
def baseStart_6720674 : Nat := 118140960795 + 6720674 * 2 ^ 59
def prefixEnd_6720674 : Nat := 4983230072969 + 3 ^ 40 * 6720674 * 2
def baseEnd_6720674 : Nat := 3450936084174943565767189

theorem tailTrace_6720674 : CollatzResearch.WordTrace tailWord_6720674 prefixEnd_6720674 3450936084174943565767189 := by
  unfold tailWord_6720674
  simp only [CollatzResearch.WordTrace]
  refine ⟨61280779613538343145826269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163415412302768915055536717 61280779613538343145826269)
  ·
    refine ⟨22980292355076878679684851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61280779613538343145826269 22980292355076878679684851)
    ·
      refine ⟨34470438532615318019527277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22980292355076878679684851 34470438532615318019527277)
      ·
        refine ⟨12926414449730744257322729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34470438532615318019527277 12926414449730744257322729)
        ·
          refine ⟨9694810837298058192992047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12926414449730744257322729 9694810837298058192992047)
          ·
            refine ⟨14542216255947087289488071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9694810837298058192992047 14542216255947087289488071)
            ·
              refine ⟨21813324383920630934232107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14542216255947087289488071 21813324383920630934232107)
              ·
                refine ⟨32719986575880946401348161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21813324383920630934232107 32719986575880946401348161)
                ·
                  refine ⟨24539989931910709801011121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32719986575880946401348161 24539989931910709801011121)
                  ·
                    refine ⟨18404992448933032350758341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24539989931910709801011121 18404992448933032350758341)
                    ·
                      refine ⟨3450936084174943565767189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18404992448933032350758341 3450936084174943565767189)
                      ·
                        rfl

theorem cell23_6720674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 1, 2, 2, 4].length) (baseStart_6720674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6720674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6720674 prefixEnd_6720674 := by exact prefixLift 6720674
  have htrace : WordTrace (prefixWord ++ tailWord_6720674) baseStart_6720674 baseEnd_6720674 := by
    simpa [prefixWord, tailWord_6720674, baseEnd_6720674] using wordTrace_append hprefix tailTrace_6720674
  have hstable : (prefixWord ++ tailWord_6720674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6720674).length < 2 ^ (prefixWord ++ tailWord_6720674).sum := by decide
  have hdescent : baseEnd_6720674 < baseStart_6720674 := by decide
  rcases family_descends (prefixWord ++ tailWord_6720674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6720677 : List Nat := [1, 3, 1, 2, 1, 5, 1, 1, 2, 3, 3]
def baseStart_6720677 : Nat := 118140960795 + 6720677 * 2 ^ 59
def prefixEnd_6720677 : Nat := 4983230072969 + 3 ^ 40 * 6720677 * 2
def baseEnd_6720677 : Nat := 3450937624616907054029675

theorem tailTrace_6720677 : CollatzResearch.WordTrace tailWord_6720677 prefixEnd_6720677 3450937624616907054029675 := by
  unfold tailWord_6720677
  simp only [CollatzResearch.WordTrace]
  refine ⟨245123227873142504095664285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163415485248761669397109523 245123227873142504095664285)
  ·
    refine ⟨91921210452428439035874107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 245123227873142504095664285 91921210452428439035874107)
    ·
      refine ⟨137881815678642658553811161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91921210452428439035874107 137881815678642658553811161)
      ·
        refine ⟨103411361758981993915358371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137881815678642658553811161 103411361758981993915358371)
        ·
          refine ⟨155117042638472990873037557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103411361758981993915358371 155117042638472990873037557)
          ·
            refine ⟨14542222747356842894347271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 155117042638472990873037557 14542222747356842894347271)
            ·
              refine ⟨21813334121035264341520907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14542222747356842894347271 21813334121035264341520907)
              ·
                refine ⟨32720001181552896512281361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21813334121035264341520907 32720001181552896512281361)
                ·
                  refine ⟨24540000886164672384211021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32720001181552896512281361 24540000886164672384211021)
                  ·
                    refine ⟨9202500332311752144079133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24540000886164672384211021 9202500332311752144079133)
                    ·
                      refine ⟨3450937624616907054029675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9202500332311752144079133 3450937624616907054029675)
                      ·
                        rfl

theorem cell23_6720677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 1, 2, 3, 3].length) (baseStart_6720677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6720677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6720677 prefixEnd_6720677 := by exact prefixLift 6720677
  have htrace : WordTrace (prefixWord ++ tailWord_6720677) baseStart_6720677 baseEnd_6720677 := by
    simpa [prefixWord, tailWord_6720677, baseEnd_6720677] using wordTrace_append hprefix tailTrace_6720677
  have hstable : (prefixWord ++ tailWord_6720677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6720677).length < 2 ^ (prefixWord ++ tailWord_6720677).sum := by decide
  have hdescent : baseEnd_6720677 < baseStart_6720677 := by decide
  rcases family_descends (prefixWord ++ tailWord_6720677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6720697 : List Nat := [1, 2, 1, 4, 1, 3, 3, 1, 2, 5]
def baseStart_6720697 : Nat := 118140960795 + 6720697 * 2 ^ 59
def prefixEnd_6720697 : Nat := 4983230072969 + 3 ^ 40 * 6720697 * 2
def baseEnd_6720697 : Nat := 1150315964743332325259861

theorem tailTrace_6720697 : CollatzResearch.WordTrace tailWord_6720697 prefixEnd_6720697 1150315964743332325259861 := by
  unfold tailWord_6720697
  simp only [CollatzResearch.WordTrace]
  refine ⟨245123957333070047511392345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163415971555380031674261563 245123957333070047511392345)
  ·
    refine ⟨183842967999802535633544259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245123957333070047511392345 183842967999802535633544259)
    ·
      refine ⟨275764451999703803450316389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183842967999802535633544259 275764451999703803450316389)
      ·
        refine ⟨51705834749944463146934323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 275764451999703803450316389 51705834749944463146934323)
        ·
          refine ⟨77558752124916694720401485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51705834749944463146934323 77558752124916694720401485)
          ·
            refine ⟨29084532046843760520150557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77558752124916694720401485 29084532046843760520150557)
            ·
              refine ⟨10906699517566410195056459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29084532046843760520150557 10906699517566410195056459)
              ·
                refine ⟨16360049276349615292584689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10906699517566410195056459 16360049276349615292584689)
                ·
                  refine ⟨12270036957262211469438517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16360049276349615292584689 12270036957262211469438517)
                  ·
                    refine ⟨1150315964743332325259861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12270036957262211469438517 1150315964743332325259861)
                    ·
                      rfl

theorem cell23_6720697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 3, 1, 2, 5].length) (baseStart_6720697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6720697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6720697 prefixEnd_6720697 := by exact prefixLift 6720697
  have htrace : WordTrace (prefixWord ++ tailWord_6720697) baseStart_6720697 baseEnd_6720697 := by
    simpa [prefixWord, tailWord_6720697, baseEnd_6720697] using wordTrace_append hprefix tailTrace_6720697
  have hstable : (prefixWord ++ tailWord_6720697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6720697).length < 2 ^ (prefixWord ++ tailWord_6720697).sum := by decide
  have hdescent : baseEnd_6720697 < baseStart_6720697 := by decide
  rcases family_descends (prefixWord ++ tailWord_6720697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6720727 : List Nat := [1, 1, 3, 2, 1, 2, 3, 3, 3, 4]
def baseStart_6720727 : Nat := 118140960795 + 6720727 * 2 ^ 59
def prefixEnd_6720727 : Nat := 4983230072969 + 3 ^ 40 * 6720727 * 2
def baseEnd_6720727 : Nat := 1150321099549877286134815

theorem tailTrace_6720727 : CollatzResearch.WordTrace tailWord_6720727 prefixEnd_6720727 1150321099549877286134815 := by
  unfold tailWord_6720727
  simp only [CollatzResearch.WordTrace]
  refine ⟨245125051522961362634984435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163416701015307575089989623 245125051522961362634984435)
  ·
    refine ⟨367687577284442043952476653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245125051522961362634984435 367687577284442043952476653)
    ·
      refine ⟨137882841481665766482178745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 367687577284442043952476653 137882841481665766482178745)
      ·
        refine ⟨103412131111249324861634059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137882841481665766482178745 103412131111249324861634059)
        ·
          refine ⟨155118196666873987292451089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103412131111249324861634059 155118196666873987292451089)
          ·
            refine ⟨116338647500155490469338317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 155118196666873987292451089 116338647500155490469338317)
            ·
              refine ⟨43626992812558308926001869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 116338647500155490469338317 43626992812558308926001869)
              ·
                refine ⟨16360122304709365847250701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43626992812558308926001869 16360122304709365847250701)
                ·
                  refine ⟨6135045864266012192719013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16360122304709365847250701 6135045864266012192719013)
                  ·
                    refine ⟨1150321099549877286134815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6135045864266012192719013 1150321099549877286134815)
                    ·
                      rfl

theorem cell23_6720727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 3, 3, 4].length) (baseStart_6720727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6720727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6720727 prefixEnd_6720727 := by exact prefixLift 6720727
  have htrace : WordTrace (prefixWord ++ tailWord_6720727) baseStart_6720727 baseEnd_6720727 := by
    simpa [prefixWord, tailWord_6720727, baseEnd_6720727] using wordTrace_append hprefix tailTrace_6720727
  have hstable : (prefixWord ++ tailWord_6720727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6720727).length < 2 ^ (prefixWord ++ tailWord_6720727).sum := by decide
  have hdescent : baseEnd_6720727 < baseStart_6720727 := by decide
  rcases family_descends (prefixWord ++ tailWord_6720727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6720730 : List Nat := [3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 6]
def baseStart_6720730 : Nat := 118140960795 + 6720730 * 2 ^ 59
def prefixEnd_6720730 : Nat := 4983230072969 + 3 ^ 40 * 6720730 * 2
def baseEnd_6720730 : Nat := 3450964839091595346666931

theorem tailTrace_6720730 : CollatzResearch.WordTrace tailWord_6720730 prefixEnd_6720730 3450964839091595346666931 := by
  unfold tailWord_6720730
  simp only [CollatzResearch.WordTrace]
  refine ⟨61281290235487623536835911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163416773961300329431562429 61281290235487623536835911)
  ·
    refine ⟨91921935353231435305253867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61281290235487623536835911 91921935353231435305253867)
    ·
      refine ⟨137882903029847152957880801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91921935353231435305253867 137882903029847152957880801)
      ·
        refine ⟨103412177272385364718410601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137882903029847152957880801 103412177272385364718410601)
        ·
          refine ⟨77559132954289023538807951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103412177272385364718410601 77559132954289023538807951)
          ·
            refine ⟨116338699431433535308211927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77559132954289023538807951 116338699431433535308211927)
            ·
              refine ⟨174508049147150302962317891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116338699431433535308211927 174508049147150302962317891)
              ·
                refine ⟨261762073720725454443476837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 174508049147150302962317891 261762073720725454443476837)
                ·
                  refine ⟨49080388822636022708151907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 261762073720725454443476837 49080388822636022708151907)
                  ·
                    refine ⟨73620583233954034062227861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49080388822636022708151907 73620583233954034062227861)
                    ·
                      refine ⟨3450964839091595346666931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 73620583233954034062227861 3450964839091595346666931)
                      ·
                        rfl

theorem cell23_6720730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 6].length) (baseStart_6720730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6720730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6720730 prefixEnd_6720730 := by exact prefixLift 6720730
  have htrace : WordTrace (prefixWord ++ tailWord_6720730) baseStart_6720730 baseEnd_6720730 := by
    simpa [prefixWord, tailWord_6720730, baseEnd_6720730] using wordTrace_append hprefix tailTrace_6720730
  have hstable : (prefixWord ++ tailWord_6720730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6720730).length < 2 ^ (prefixWord ++ tailWord_6720730).sum := by decide
  have hdescent : baseEnd_6720730 < baseStart_6720730 := by decide
  rcases family_descends (prefixWord ++ tailWord_6720730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6720737 : List Nat := [1, 2, 3, 1, 3, 2, 1, 2, 1, 4, 3]
def baseStart_6720737 : Nat := 118140960795 + 6720737 * 2 ^ 59
def prefixEnd_6720737 : Nat := 4983230072969 + 3 ^ 40 * 6720737 * 2
def baseEnd_6720737 : Nat := 3450968433456176819279399

theorem tailTrace_6720737 : CollatzResearch.WordTrace tailWord_6720737 prefixEnd_6720737 3450968433456176819279399 := by
  unfold tailWord_6720737
  simp only [CollatzResearch.WordTrace]
  refine ⟨245125416252925134342848465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163416944168616756228565643 245125416252925134342848465)
  ·
    refine ⟨183844062189693850757136349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245125416252925134342848465 183844062189693850757136349)
    ·
      refine ⟨68941523321135194033926131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 183844062189693850757136349 68941523321135194033926131)
      ·
        refine ⟨103412284981702791050889197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68941523321135194033926131 103412284981702791050889197)
        ·
          refine ⟨38779606868138546644083449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103412284981702791050889197 38779606868138546644083449)
          ·
            refine ⟨29084705151103909983062587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38779606868138546644083449 29084705151103909983062587)
            ·
              refine ⟨43627057726655864974593881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29084705151103909983062587 43627057726655864974593881)
              ·
                refine ⟨32720293294991898730945411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43627057726655864974593881 32720293294991898730945411)
                ·
                  refine ⟨49080439942487848096418117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32720293294991898730945411 49080439942487848096418117)
                  ·
                    refine ⟨9202582489216471518078397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 49080439942487848096418117 9202582489216471518078397)
                    ·
                      refine ⟨3450968433456176819279399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9202582489216471518078397 3450968433456176819279399)
                      ·
                        rfl

theorem cell23_6720737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 2, 1, 4, 3].length) (baseStart_6720737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6720737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6720737 prefixEnd_6720737 := by exact prefixLift 6720737
  have htrace : WordTrace (prefixWord ++ tailWord_6720737) baseStart_6720737 baseEnd_6720737 := by
    simpa [prefixWord, tailWord_6720737, baseEnd_6720737] using wordTrace_append hprefix tailTrace_6720737
  have hstable : (prefixWord ++ tailWord_6720737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6720737).length < 2 ^ (prefixWord ++ tailWord_6720737).sum := by decide
  have hdescent : baseEnd_6720737 < baseStart_6720737 := by decide
  rcases family_descends (prefixWord ++ tailWord_6720737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6720817 : List Nat := [1, 2, 2, 3, 3, 1, 1, 1, 3, 6]
def baseStart_6720817 : Nat := 118140960795 + 6720817 * 2 ^ 59
def prefixEnd_6720817 : Nat := 4983230072969 + 3 ^ 40 * 6720817 * 2
def baseEnd_6720817 : Nat := 1150336503969512168759677

theorem tailTrace_6720817 : CollatzResearch.WordTrace tailWord_6720817 prefixEnd_6720817 1150336503969512168759677 := by
  unfold tailWord_6720817
  simp only [CollatzResearch.WordTrace]
  refine ⟨245128334092635308005760705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163418889395090205337173803 245128334092635308005760705)
  ·
    refine ⟨183846250569476481004320529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245128334092635308005760705 183846250569476481004320529)
    ·
      refine ⟨137884687927107360753240397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183846250569476481004320529 137884687927107360753240397)
      ·
        refine ⟨51706757972665260282465149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137884687927107360753240397 51706757972665260282465149)
        ·
          refine ⟨19390034239749472605924431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51706757972665260282465149 19390034239749472605924431)
          ·
            refine ⟨29085051359624208908886647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19390034239749472605924431 29085051359624208908886647)
            ·
              refine ⟨43627577039436313363329971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29085051359624208908886647 43627577039436313363329971)
              ·
                refine ⟨65441365559154470044994957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43627577039436313363329971 65441365559154470044994957)
                ·
                  refine ⟨24540512084682926266873109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65441365559154470044994957 24540512084682926266873109)
                  ·
                    refine ⟨1150336503969512168759677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24540512084682926266873109 1150336503969512168759677)
                    ·
                      rfl

theorem cell23_6720817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 1, 3, 6].length) (baseStart_6720817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6720817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6720817 prefixEnd_6720817 := by exact prefixLift 6720817
  have htrace : WordTrace (prefixWord ++ tailWord_6720817) baseStart_6720817 baseEnd_6720817 := by
    simpa [prefixWord, tailWord_6720817, baseEnd_6720817] using wordTrace_append hprefix tailTrace_6720817
  have hstable : (prefixWord ++ tailWord_6720817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6720817).length < 2 ^ (prefixWord ++ tailWord_6720817).sum := by decide
  have hdescent : baseEnd_6720817 < baseStart_6720817 := by decide
  rcases family_descends (prefixWord ++ tailWord_6720817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6720821 : List Nat := [1, 3, 3, 1, 2, 3, 3, 1, 1, 5]
def baseStart_6720821 : Nat := 118140960795 + 6720821 * 2 ^ 59
def prefixEnd_6720821 : Nat := 4983230072969 + 3 ^ 40 * 6720821 * 2
def baseEnd_6720821 : Nat := 1150337188610384830209671

theorem tailTrace_6720821 : CollatzResearch.WordTrace tailWord_6720821 prefixEnd_6720821 1150337188610384830209671 := by
  unfold tailWord_6720821
  simp only [CollatzResearch.WordTrace]
  refine ⟨245128479984620816688906317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163418986656413877792604211 245128479984620816688906317)
  ·
    refine ⟨91923179994232806258339869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 245128479984620816688906317 91923179994232806258339869)
    ·
      refine ⟨34471192497837302346877451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91923179994232806258339869 34471192497837302346877451)
      ·
        refine ⟨51706788746755953520316177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34471192497837302346877451 51706788746755953520316177)
        ·
          refine ⟨38780091560066965140237133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51706788746755953520316177 38780091560066965140237133)
          ·
            refine ⟨14542534335025111927588925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38780091560066965140237133 14542534335025111927588925)
            ·
              refine ⟨5453450375634416972845847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14542534335025111927588925 5453450375634416972845847)
              ·
                refine ⟨8180175563451625459268771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5453450375634416972845847 8180175563451625459268771)
                ·
                  refine ⟨12270263345177438188903157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8180175563451625459268771 12270263345177438188903157)
                  ·
                    refine ⟨1150337188610384830209671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12270263345177438188903157 1150337188610384830209671)
                    ·
                      rfl

theorem cell23_6720821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 3, 1, 1, 5].length) (baseStart_6720821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6720821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6720821 prefixEnd_6720821 := by exact prefixLift 6720821
  have htrace : WordTrace (prefixWord ++ tailWord_6720821) baseStart_6720821 baseEnd_6720821 := by
    simpa [prefixWord, tailWord_6720821, baseEnd_6720821] using wordTrace_append hprefix tailTrace_6720821
  have hstable : (prefixWord ++ tailWord_6720821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6720821).length < 2 ^ (prefixWord ++ tailWord_6720821).sum := by decide
  have hdescent : baseEnd_6720821 < baseStart_6720821 := by decide
  rcases family_descends (prefixWord ++ tailWord_6720821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6720844 : List Nat := [2, 2, 1, 3, 2, 2, 1, 2, 3, 2, 3]
def baseStart_6720844 : Nat := 118140960795 + 6720844 * 2 ^ 59
def prefixEnd_6720844 : Nat := 4983230072969 + 3 ^ 40 * 6720844 * 2
def baseEnd_6720844 : Nat := 3451023375886207900641407

theorem tailTrace_6720844 : CollatzResearch.WordTrace tailWord_6720844 prefixEnd_6720844 3451023375886207900641407 := by
  unfold tailWord_6720844
  simp only [CollatzResearch.WordTrace]
  refine ⟨122564659431768745808496793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163419545909024994411329057 122564659431768745808496793)
  ·
    refine ⟨91923494573826559356372595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122564659431768745808496793 91923494573826559356372595)
    ·
      refine ⟨137885241860739839034558893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91923494573826559356372595 137885241860739839034558893)
      ·
        refine ⟨51706965697777439637959585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137885241860739839034558893 51706965697777439637959585)
        ·
          refine ⟨38780224273333079728469689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51706965697777439637959585 38780224273333079728469689)
          ·
            refine ⟨29085168204999809796352267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38780224273333079728469689 29085168204999809796352267)
            ·
              refine ⟨43627752307499714694528401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29085168204999809796352267 43627752307499714694528401)
              ·
                refine ⟨32720814230624786020896301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43627752307499714694528401 32720814230624786020896301)
                ·
                  refine ⟨12270305336484294757836113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32720814230624786020896301 12270305336484294757836113)
                  ·
                    refine ⟨9202729002363221068377085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12270305336484294757836113 9202729002363221068377085)
                    ·
                      refine ⟨3451023375886207900641407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9202729002363221068377085 3451023375886207900641407)
                      ·
                        rfl

theorem cell23_6720844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 2, 3, 2, 3].length) (baseStart_6720844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6720844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6720844 prefixEnd_6720844 := by exact prefixLift 6720844
  have htrace : WordTrace (prefixWord ++ tailWord_6720844) baseStart_6720844 baseEnd_6720844 := by
    simpa [prefixWord, tailWord_6720844, baseEnd_6720844] using wordTrace_append hprefix tailTrace_6720844
  have hstable : (prefixWord ++ tailWord_6720844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6720844).length < 2 ^ (prefixWord ++ tailWord_6720844).sum := by decide
  have hdescent : baseEnd_6720844 < baseStart_6720844 := by decide
  rcases family_descends (prefixWord ++ tailWord_6720844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6720864 : List Nat := [2, 1, 1, 3, 4, 2, 3, 7]
def baseStart_6720864 : Nat := 118140960795 + 6720864 * 2 ^ 59
def prefixEnd_6720864 : Nat := 4983230072969 + 3 ^ 40 * 6720864 * 2
def baseEnd_6720864 : Nat := 127816060944418437866345

theorem tailTrace_6720864 : CollatzResearch.WordTrace tailWord_6720864 prefixEnd_6720864 127816060944418437866345 := by
  unfold tailWord_6720864
  simp only [CollatzResearch.WordTrace]
  refine ⟨122565024161732517516360823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163420032215643356688481097 122565024161732517516360823)
  ·
    refine ⟨183847536242598776274541235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122565024161732517516360823 183847536242598776274541235)
    ·
      refine ⟨275771304363898164411811853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183847536242598776274541235 275771304363898164411811853)
      ·
        refine ⟨103414239136461811654429445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 275771304363898164411811853 103414239136461811654429445)
        ·
          refine ⟨19390169838086589685205521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 103414239136461811654429445 19390169838086589685205521)
          ·
            refine ⟨14542627378564942263904141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19390169838086589685205521 14542627378564942263904141)
            ·
              refine ⟨5453485266961853348964053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14542627378564942263904141 5453485266961853348964053)
              ·
                refine ⟨127816060944418437866345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5453485266961853348964053 127816060944418437866345)
                ·
                  rfl

theorem cell23_6720864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 3, 7].length) (baseStart_6720864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6720864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6720864 prefixEnd_6720864 := by exact prefixLift 6720864
  have htrace : WordTrace (prefixWord ++ tailWord_6720864) baseStart_6720864 baseEnd_6720864 := by
    simpa [prefixWord, tailWord_6720864, baseEnd_6720864] using wordTrace_append hprefix tailTrace_6720864
  have hstable : (prefixWord ++ tailWord_6720864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6720864).length < 2 ^ (prefixWord ++ tailWord_6720864).sum := by decide
  have hdescent : baseEnd_6720864 < baseStart_6720864 := by decide
  rcases family_descends (prefixWord ++ tailWord_6720864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6720885 : List Nat := [1, 3, 4, 1, 4, 1, 1, 2, 2, 4]
def baseStart_6720885 : Nat := 118140960795 + 6720885 * 2 ^ 59
def prefixEnd_6720885 : Nat := 4983230072969 + 3 ^ 40 * 6720885 * 2
def baseEnd_6720885 : Nat := 1150348142864347413409573

theorem tailTrace_6720885 : CollatzResearch.WordTrace tailWord_6720885 prefixEnd_6720885 1150348142864347413409573 := by
  unfold tailWord_6720885
  simp only [CollatzResearch.WordTrace]
  refine ⟨245130814256388955619236109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163420542837592637079490739 245130814256388955619236109)
  ·
    refine ⟨91924055346145858357213541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 245130814256388955619236109 91924055346145858357213541)
    ·
      refine ⟨17235760377402348441977539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91924055346145858357213541 17235760377402348441977539)
      ·
        refine ⟨25853640566103522662966309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17235760377402348441977539 25853640566103522662966309)
        ·
          refine ⟨4847557606144410499306183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25853640566103522662966309 4847557606144410499306183)
          ·
            refine ⟨7271336409216615748959275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4847557606144410499306183 7271336409216615748959275)
            ·
              refine ⟨10907004613824923623438913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7271336409216615748959275 10907004613824923623438913)
              ·
                refine ⟨8180253460368692717579185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10907004613824923623438913 8180253460368692717579185)
                ·
                  refine ⟨6135190095276519538184389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8180253460368692717579185 6135190095276519538184389)
                  ·
                    refine ⟨1150348142864347413409573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6135190095276519538184389 1150348142864347413409573)
                    ·
                      rfl

theorem cell23_6720885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 1, 2, 2, 4].length) (baseStart_6720885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6720885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6720885 prefixEnd_6720885 := by exact prefixLift 6720885
  have htrace : WordTrace (prefixWord ++ tailWord_6720885) baseStart_6720885 baseEnd_6720885 := by
    simpa [prefixWord, tailWord_6720885, baseEnd_6720885] using wordTrace_append hprefix tailTrace_6720885
  have hstable : (prefixWord ++ tailWord_6720885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6720885).length < 2 ^ (prefixWord ++ tailWord_6720885).sum := by decide
  have hdescent : baseEnd_6720885 < baseStart_6720885 := by decide
  rcases family_descends (prefixWord ++ tailWord_6720885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6720907 : List Nat := [1, 1, 1, 1, 4, 3, 1, 3, 2, 6]
def baseStart_6720907 : Nat := 118140960795 + 6720907 * 2 ^ 59
def prefixEnd_6720907 : Nat := 4983230072969 + 3 ^ 40 * 6720907 * 2
def baseEnd_6720907 : Nat := 1150351908389147051384539

theorem tailTrace_6720907 : CollatzResearch.WordTrace tailWord_6720907 prefixEnd_6720907 1150351908389147051384539 := by
  unfold tailWord_6720907
  simp only [CollatzResearch.WordTrace]
  refine ⟨245131616662309253376536975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163421077774872835584357983 245131616662309253376536975)
  ·
    refine ⟨367697424993463880064805463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245131616662309253376536975 367697424993463880064805463)
    ·
      refine ⟨551546137490195820097208195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 367697424993463880064805463 551546137490195820097208195)
      ·
        refine ⟨827319206235293730145812293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 551546137490195820097208195 827319206235293730145812293)
        ·
          refine ⟨155122351169117574402339805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 827319206235293730145812293 155122351169117574402339805)
          ·
            refine ⟨58170881688419090400877427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 155122351169117574402339805 58170881688419090400877427)
            ·
              refine ⟨87256322532628635601316141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58170881688419090400877427 87256322532628635601316141)
              ·
                refine ⟨32721120949735738350493553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 87256322532628635601316141 32721120949735738350493553)
                ·
                  refine ⟨24540840712301803762870165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32721120949735738350493553 24540840712301803762870165)
                  ·
                    refine ⟨1150351908389147051384539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24540840712301803762870165 1150351908389147051384539)
                    ·
                      rfl

theorem cell23_6720907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 3, 2, 6].length) (baseStart_6720907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6720907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6720907 prefixEnd_6720907 := by exact prefixLift 6720907
  have htrace : WordTrace (prefixWord ++ tailWord_6720907) baseStart_6720907 baseEnd_6720907 := by
    simpa [prefixWord, tailWord_6720907, baseEnd_6720907] using wordTrace_append hprefix tailTrace_6720907
  have hstable : (prefixWord ++ tailWord_6720907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6720907).length < 2 ^ (prefixWord ++ tailWord_6720907).sum := by decide
  have hdescent : baseEnd_6720907 < baseStart_6720907 := by decide
  rcases family_descends (prefixWord ++ tailWord_6720907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6720908 : List Nat := [2, 2, 1, 2, 1, 3, 5, 1, 2, 1, 3]
def baseStart_6720908 : Nat := 118140960795 + 6720908 * 2 ^ 59
def prefixEnd_6720908 : Nat := 4983230072969 + 3 ^ 40 * 6720908 * 2
def baseEnd_6720908 : Nat := 3451056238648095650241113

theorem tailTrace_6720908 : CollatzResearch.WordTrace tailWord_6720908 prefixEnd_6720908 3451056238648095650241113 := by
  unfold tailWord_6720908
  simp only [CollatzResearch.WordTrace]
  refine ⟨122565826567652815273661689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163421102090203753698215585 122565826567652815273661689)
  ·
    refine ⟨91924369925739611455246267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122565826567652815273661689 91924369925739611455246267)
    ·
      refine ⟨137886554888609417182869401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91924369925739611455246267 137886554888609417182869401)
      ·
        refine ⟨103414916166457062887152051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137886554888609417182869401 103414916166457062887152051)
        ·
          refine ⟨155122374249685594330728077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103414916166457062887152051 155122374249685594330728077)
          ·
            refine ⟨58170890343632097874023029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 155122374249685594330728077 58170890343632097874023029)
            ·
              refine ⟨5453520969715509175689659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 58170890343632097874023029 5453520969715509175689659)
              ·
                refine ⟨8180281454573263763534489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5453520969715509175689659 8180281454573263763534489)
                ·
                  refine ⟨6135211090929947822650867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8180281454573263763534489 6135211090929947822650867)
                  ·
                    refine ⟨9202816636394921733976301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6135211090929947822650867 9202816636394921733976301)
                    ·
                      refine ⟨3451056238648095650241113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9202816636394921733976301 3451056238648095650241113)
                      ·
                        rfl

theorem cell23_6720908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 5, 1, 2, 1, 3].length) (baseStart_6720908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6720908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6720908 prefixEnd_6720908 := by exact prefixLift 6720908
  have htrace : WordTrace (prefixWord ++ tailWord_6720908) baseStart_6720908 baseEnd_6720908 := by
    simpa [prefixWord, tailWord_6720908, baseEnd_6720908] using wordTrace_append hprefix tailTrace_6720908
  have hstable : (prefixWord ++ tailWord_6720908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6720908).length < 2 ^ (prefixWord ++ tailWord_6720908).sum := by decide
  have hdescent : baseEnd_6720908 < baseStart_6720908 := by decide
  rcases family_descends (prefixWord ++ tailWord_6720908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6720926 : List Nat := [4, 3, 1, 2, 3, 1, 1, 3, 1, 2, 2]
def baseStart_6720926 : Nat := 118140960795 + 6720926 * 2 ^ 59
def prefixEnd_6720926 : Nat := 4983230072969 + 3 ^ 40 * 6720926 * 2
def baseEnd_6720926 : Nat := 3451065481299876579816031

theorem tailTrace_6720926 : CollatzResearch.WordTrace tailWord_6720926 prefixEnd_6720926 3451065481299876579816031 := by
  unfold tailWord_6720926
  simp only [CollatzResearch.WordTrace]
  refine ⟨30641538706155052452684829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 163421539766160279747652421 30641538706155052452684829)
  ·
    refine ⟨11490577014808144669756811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30641538706155052452684829 11490577014808144669756811)
    ·
      refine ⟨17235865522212217004635217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11490577014808144669756811 17235865522212217004635217)
      ·
        refine ⟨12926899141659162753476413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17235865522212217004635217 12926899141659162753476413)
        ·
          refine ⟨4847587178122186032553655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12926899141659162753476413 4847587178122186032553655)
          ·
            refine ⟨7271380767183279048830483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4847587178122186032553655 7271380767183279048830483)
            ·
              refine ⟨10907071150774918573245725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7271380767183279048830483 10907071150774918573245725)
              ·
                refine ⟨4090151681540594464967147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10907071150774918573245725 4090151681540594464967147)
                ·
                  refine ⟨6135227522310891697450721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4090151681540594464967147 6135227522310891697450721)
                  ·
                    refine ⟨4601420641733168773088041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6135227522310891697450721 4601420641733168773088041)
                    ·
                      refine ⟨3451065481299876579816031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4601420641733168773088041 3451065481299876579816031)
                      ·
                        rfl

theorem cell23_6720926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 1, 3, 1, 2, 2].length) (baseStart_6720926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6720926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6720926 prefixEnd_6720926 := by exact prefixLift 6720926
  have htrace : WordTrace (prefixWord ++ tailWord_6720926) baseStart_6720926 baseEnd_6720926 := by
    simpa [prefixWord, tailWord_6720926, baseEnd_6720926] using wordTrace_append hprefix tailTrace_6720926
  have hstable : (prefixWord ++ tailWord_6720926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6720926).length < 2 ^ (prefixWord ++ tailWord_6720926).sum := by decide
  have hdescent : baseEnd_6720926 < baseStart_6720926 := by decide
  rcases family_descends (prefixWord ++ tailWord_6720926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6720931 : List Nat := [1, 1, 1, 4, 1, 3, 1, 1, 6, 2, 2]
def baseStart_6720931 : Nat := 118140960795 + 6720931 * 2 ^ 59
def prefixEnd_6720931 : Nat := 4983230072969 + 3 ^ 40 * 6720931 * 2
def baseEnd_6720931 : Nat := 3451068048703149060253507

theorem tailTrace_6720931 : CollatzResearch.WordTrace tailWord_6720931 prefixEnd_6720931 3451068048703149060253507 := by
  unfold tailWord_6720931
  simp only [CollatzResearch.WordTrace]
  refine ⟨245132492014222305475410647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163421661342814870316940431 245132492014222305475410647)
  ·
    refine ⟨367698738021333458213115971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245132492014222305475410647 367698738021333458213115971)
    ·
      refine ⟨551548107032000187319673957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 367698738021333458213115971 551548107032000187319673957)
      ·
        refine ⟨103415270068500035122438867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 551548107032000187319673957 103415270068500035122438867)
        ·
          refine ⟨155122905102750052683658301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103415270068500035122438867 155122905102750052683658301)
          ·
            refine ⟨58171089413531269756371863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 155122905102750052683658301 58171089413531269756371863)
            ·
              refine ⟨87256634120296904634557795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58171089413531269756371863 87256634120296904634557795)
              ·
                refine ⟨130884951180445356951836693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87256634120296904634557795 130884951180445356951836693)
                ·
                  refine ⟨6135232086583376107117345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 130884951180445356951836693 6135232086583376107117345)
                  ·
                    refine ⟨4601424064937532080338009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6135232086583376107117345 4601424064937532080338009)
                    ·
                      refine ⟨3451068048703149060253507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4601424064937532080338009 3451068048703149060253507)
                      ·
                        rfl

theorem cell23_6720931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 1, 6, 2, 2].length) (baseStart_6720931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6720931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6720931 prefixEnd_6720931 := by exact prefixLift 6720931
  have htrace : WordTrace (prefixWord ++ tailWord_6720931) baseStart_6720931 baseEnd_6720931 := by
    simpa [prefixWord, tailWord_6720931, baseEnd_6720931] using wordTrace_append hprefix tailTrace_6720931
  have hstable : (prefixWord ++ tailWord_6720931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6720931).length < 2 ^ (prefixWord ++ tailWord_6720931).sum := by decide
  have hdescent : baseEnd_6720931 < baseStart_6720931 := by decide
  rcases family_descends (prefixWord ++ tailWord_6720931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6720984 : List Nat := [2, 1, 2, 2, 2, 1, 3, 3, 2, 5]
def baseStart_6720984 : Nat := 118140960795 + 6720984 * 2 ^ 59
def prefixEnd_6720984 : Nat := 4983230072969 + 3 ^ 40 * 6720984 * 2
def baseEnd_6720984 : Nat := 1150365087725945784296921

theorem tailTrace_6720984 : CollatzResearch.WordTrace tailWord_6720984 prefixEnd_6720984 1150365087725945784296921 := by
  unfold tailWord_6720984
  simp only [CollatzResearch.WordTrace]
  refine ⟨122567212541515147763545003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163422950055353530351393337 122567212541515147763545003)
  ·
    refine ⟨183850818812272721645317505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122567212541515147763545003 183850818812272721645317505)
    ·
      refine ⟨137888114109204541233988129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183850818812272721645317505 137888114109204541233988129)
      ·
        refine ⟨103416085581903405925491097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137888114109204541233988129 103416085581903405925491097)
        ·
          refine ⟨77562064186427554444118323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103416085581903405925491097 77562064186427554444118323)
          ·
            refine ⟨116343096279641331666177485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77562064186427554444118323 116343096279641331666177485)
            ·
              refine ⟨43628661104865499374816557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 116343096279641331666177485 43628661104865499374816557)
              ·
                refine ⟨16360747914324562265556209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43628661104865499374816557 16360747914324562265556209)
                ·
                  refine ⟨12270560935743421699167157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16360747914324562265556209 12270560935743421699167157)
                  ·
                    refine ⟨1150365087725945784296921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12270560935743421699167157 1150365087725945784296921)
                    ·
                      rfl

theorem cell23_6720984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 3, 2, 5].length) (baseStart_6720984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6720984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6720984 prefixEnd_6720984 := by exact prefixLift 6720984
  have htrace : WordTrace (prefixWord ++ tailWord_6720984) baseStart_6720984 baseEnd_6720984 := by
    simpa [prefixWord, tailWord_6720984, baseEnd_6720984] using wordTrace_append hprefix tailTrace_6720984
  have hstable : (prefixWord ++ tailWord_6720984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6720984).length < 2 ^ (prefixWord ++ tailWord_6720984).sum := by decide
  have hdescent : baseEnd_6720984 < baseStart_6720984 := by decide
  rcases family_descends (prefixWord ++ tailWord_6720984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6721004 : List Nat := [2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 4]
def baseStart_6721004 : Nat := 118140960795 + 6721004 * 2 ^ 59
def prefixEnd_6721004 : Nat := 4983230072969 + 3 ^ 40 * 6721004 * 2
def baseEnd_6721004 : Nat := 3451105532790927274640671

theorem tailTrace_6721004 : CollatzResearch.WordTrace tailWord_6721004 prefixEnd_6721004 3451105532790927274640671 := by
  unfold tailWord_6721004
  simp only [CollatzResearch.WordTrace]
  refine ⟨122567577271478919471409033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163423436361971892628545377 122567577271478919471409033)
  ·
    refine ⟨91925682953609189603556775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122567577271478919471409033 91925682953609189603556775)
    ·
      refine ⟨137888524430413784405335163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91925682953609189603556775 137888524430413784405335163)
      ·
        refine ⟨206832786645620676608002745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137888524430413784405335163 206832786645620676608002745)
        ·
          refine ⟨155124589984215507456002059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 206832786645620676608002745 155124589984215507456002059)
          ·
            refine ⟨232686884976323261184003089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155124589984215507456002059 232686884976323261184003089)
            ·
              refine ⟨174515163732242445888002317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 232686884976323261184003089 174515163732242445888002317)
              ·
                refine ⟨65443186399590917208000869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 174515163732242445888002317 65443186399590917208000869)
                ·
                  refine ⟨12270597449923296976500163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65443186399590917208000869 12270597449923296976500163)
                  ·
                    refine ⟨18405896174884945464750245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12270597449923296976500163 18405896174884945464750245)
                    ·
                      refine ⟨3451105532790927274640671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18405896174884945464750245 3451105532790927274640671)
                      ·
                        rfl

theorem cell23_6721004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 4].length) (baseStart_6721004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6721004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6721004 prefixEnd_6721004 := by exact prefixLift 6721004
  have htrace : WordTrace (prefixWord ++ tailWord_6721004) baseStart_6721004 baseEnd_6721004 := by
    simpa [prefixWord, tailWord_6721004, baseEnd_6721004] using wordTrace_append hprefix tailTrace_6721004
  have hstable : (prefixWord ++ tailWord_6721004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6721004).length < 2 ^ (prefixWord ++ tailWord_6721004).sum := by decide
  have hdescent : baseEnd_6721004 < baseStart_6721004 := by decide
  rcases family_descends (prefixWord ++ tailWord_6721004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6721021 : List Nat := [1, 4, 1, 1, 1, 4, 1, 1, 1, 6, 2]
def baseStart_6721021 : Nat := 118140960795 + 6721021 * 2 ^ 59
def prefixEnd_6721021 : Nat := 4983230072969 + 3 ^ 40 * 6721021 * 2
def baseEnd_6721021 : Nat := 3451114261962053708128093

theorem tailTrace_6721021 : CollatzResearch.WordTrace tailWord_6721021 prefixEnd_6721021 3451114261962053708128093 := by
  unfold tailWord_6721021
  simp only [CollatzResearch.WordTrace]
  refine ⟨245135774583896250846186917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163423849722597500564124611 245135774583896250846186917)
  ·
    refine ⟨45962957734480547033660047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 245135774583896250846186917 45962957734480547033660047)
    ·
      refine ⟨68944436601720820550490071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45962957734480547033660047 68944436601720820550490071)
      ·
        refine ⟨103416654902581230825735107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68944436601720820550490071 103416654902581230825735107)
        ·
          refine ⟨155124982353871846238602661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103416654902581230825735107 155124982353871846238602661)
          ·
            refine ⟨29085934191350971169737999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 155124982353871846238602661 29085934191350971169737999)
            ·
              refine ⟨43628901287026456754606999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29085934191350971169737999 43628901287026456754606999)
              ·
                refine ⟨65443351930539685131910499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43628901287026456754606999 65443351930539685131910499)
                ·
                  refine ⟨98165027895809527697865749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65443351930539685131910499 98165027895809527697865749)
                  ·
                    refine ⟨4601485682616071610837457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 98165027895809527697865749 4601485682616071610837457)
                    ·
                      refine ⟨3451114261962053708128093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4601485682616071610837457 3451114261962053708128093)
                      ·
                        rfl

theorem cell23_6721021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 1, 1, 6, 2].length) (baseStart_6721021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6721021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6721021 prefixEnd_6721021 := by exact prefixLift 6721021
  have htrace : WordTrace (prefixWord ++ tailWord_6721021) baseStart_6721021 baseEnd_6721021 := by
    simpa [prefixWord, tailWord_6721021, baseEnd_6721021] using wordTrace_append hprefix tailTrace_6721021
  have hstable : (prefixWord ++ tailWord_6721021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6721021).length < 2 ^ (prefixWord ++ tailWord_6721021).sum := by decide
  have hdescent : baseEnd_6721021 < baseStart_6721021 := by decide
  rcases family_descends (prefixWord ++ tailWord_6721021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6721031 : List Nat := [1, 1, 4, 3, 2, 1, 1, 1, 5, 4]
def baseStart_6721031 : Nat := 118140960795 + 6721031 * 2 ^ 59
def prefixEnd_6721031 : Nat := 4983230072969 + 3 ^ 40 * 6721031 * 2
def baseEnd_6721031 : Nat := 1150373132256199556334349

theorem tailTrace_6721031 : CollatzResearch.WordTrace tailWord_6721031 prefixEnd_6721031 1150373132256199556334349 := by
  unfold tailWord_6721031
  simp only [CollatzResearch.WordTrace]
  refine ⟨245136139313860022554050947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163424092875906681702700631 245136139313860022554050947)
  ·
    refine ⟨367704208970790033831076421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245136139313860022554050947 367704208970790033831076421)
    ·
      refine ⟨68944539182023131343326829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 367704208970790033831076421 68944539182023131343326829)
      ·
        refine ⟨25854202193258674253747561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68944539182023131343326829 25854202193258674253747561)
        ·
          refine ⟨19390651644944005690310671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25854202193258674253747561 19390651644944005690310671)
          ·
            refine ⟨29085977467416008535466007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19390651644944005690310671 29085977467416008535466007)
            ·
              refine ⟨43628966201124012803199011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29085977467416008535466007 43628966201124012803199011)
              ·
                refine ⟨65443449301686019204798517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43628966201124012803199011 65443449301686019204798517)
                ·
                  refine ⟨6135323372033064300449861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 65443449301686019204798517 6135323372033064300449861)
                  ·
                    refine ⟨1150373132256199556334349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6135323372033064300449861 1150373132256199556334349)
                    ·
                      rfl

theorem cell23_6721031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 1, 5, 4].length) (baseStart_6721031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6721031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6721031 prefixEnd_6721031 := by exact prefixLift 6721031
  have htrace : WordTrace (prefixWord ++ tailWord_6721031) baseStart_6721031 baseEnd_6721031 := by
    simpa [prefixWord, tailWord_6721031, baseEnd_6721031] using wordTrace_append hprefix tailTrace_6721031
  have hstable : (prefixWord ++ tailWord_6721031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6721031).length < 2 ^ (prefixWord ++ tailWord_6721031).sum := by decide
  have hdescent : baseEnd_6721031 < baseStart_6721031 := by decide
  rcases family_descends (prefixWord ++ tailWord_6721031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6721098 : List Nat := [3, 1, 2, 1, 1, 3, 2, 3, 2, 3, 2]
def baseStart_6721098 : Nat := 118140960795 + 6721098 * 2 ^ 59
def prefixEnd_6721098 : Nat := 4983230072969 + 3 ^ 40 * 6721098 * 2
def baseEnd_6721098 : Nat := 3451153799972449906865239

theorem tailTrace_6721098 : CollatzResearch.WordTrace tailWord_6721098 prefixEnd_6721098 3451153799972449906865239 := by
  unfold tailWord_6721098
  simp only [CollatzResearch.WordTrace]
  refine ⟨61284645751154323249184987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163425722003078195331159965 61284645751154323249184987)
  ·
    refine ⟨91926968626731484873777481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61284645751154323249184987 91926968626731484873777481)
    ·
      refine ⟨68945226470048613655333111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91926968626731484873777481 68945226470048613655333111)
      ·
        refine ⟨103417839705072920482999667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68945226470048613655333111 103417839705072920482999667)
        ·
          refine ⟨155126759557609380724499501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103417839705072920482999667 155126759557609380724499501)
          ·
            refine ⟨58172534834103517771687313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 155126759557609380724499501 58172534834103517771687313)
            ·
              refine ⟨43629401125577638328765485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58172534834103517771687313 43629401125577638328765485)
              ·
                refine ⟨16361025422091614373287057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43629401125577638328765485 16361025422091614373287057)
                ·
                  refine ⟨12270769066568710779965293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16361025422091614373287057 12270769066568710779965293)
                  ·
                    refine ⟨4601538399963266542486985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12270769066568710779965293 4601538399963266542486985)
                    ·
                      refine ⟨3451153799972449906865239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4601538399963266542486985 3451153799972449906865239)
                      ·
                        rfl

theorem cell23_6721098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 3, 2, 3, 2].length) (baseStart_6721098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6721098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6721098 prefixEnd_6721098 := by exact prefixLift 6721098
  have htrace : WordTrace (prefixWord ++ tailWord_6721098) baseStart_6721098 baseEnd_6721098 := by
    simpa [prefixWord, tailWord_6721098, baseEnd_6721098] using wordTrace_append hprefix tailTrace_6721098
  have hstable : (prefixWord ++ tailWord_6721098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6721098).length < 2 ^ (prefixWord ++ tailWord_6721098).sum := by decide
  have hdescent : baseEnd_6721098 < baseStart_6721098 := by decide
  rcases family_descends (prefixWord ++ tailWord_6721098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6721104 : List Nat := [2, 1, 1, 1, 1, 3, 4, 1, 3, 6]
def baseStart_6721104 : Nat := 118140960795 + 6721104 * 2 ^ 59
def prefixEnd_6721104 : Nat := 4983230072969 + 3 ^ 40 * 6721104 * 2
def baseEnd_6721104 : Nat := 1150385626952125627796737

theorem tailTrace_6721104 : CollatzResearch.WordTrace tailWord_6721104 prefixEnd_6721104 1150385626952125627796737 := by
  unfold tailWord_6721104
  simp only [CollatzResearch.WordTrace]
  refine ⟨122569400921297778010729183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163425867895063704014305577 122569400921297778010729183)
  ·
    refine ⟨183854101381946667016093775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122569400921297778010729183 183854101381946667016093775)
    ·
      refine ⟨275781152072920000524140663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183854101381946667016093775 275781152072920000524140663)
      ·
        refine ⟨413671728109380000786210995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275781152072920000524140663 413671728109380000786210995)
        ·
          refine ⟨620507592164070001179316493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 413671728109380000786210995 620507592164070001179316493)
          ·
            refine ⟨232690347061526250442243685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 620507592164070001179316493 232690347061526250442243685)
            ·
              refine ⟨43629440074036171957920691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 232690347061526250442243685 43629440074036171957920691)
              ·
                refine ⟨65444160111054257936881037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43629440074036171957920691 65444160111054257936881037)
                ·
                  refine ⟨24541560041645346726330389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65444160111054257936881037 24541560041645346726330389)
                  ·
                    refine ⟨1150385626952125627796737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24541560041645346726330389 1150385626952125627796737)
                    ·
                      rfl

theorem cell23_6721104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 1, 3, 6].length) (baseStart_6721104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6721104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6721104 prefixEnd_6721104 := by exact prefixLift 6721104
  have htrace : WordTrace (prefixWord ++ tailWord_6721104) baseStart_6721104 baseEnd_6721104 := by
    simpa [prefixWord, tailWord_6721104, baseEnd_6721104] using wordTrace_append hprefix tailTrace_6721104
  have hstable : (prefixWord ++ tailWord_6721104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6721104).length < 2 ^ (prefixWord ++ tailWord_6721104).sum := by decide
  have hdescent : baseEnd_6721104 < baseStart_6721104 := by decide
  rcases family_descends (prefixWord ++ tailWord_6721104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6721121 : List Nat := [1, 2, 3, 1, 1, 3, 1, 3, 4, 4]
def baseStart_6721121 : Nat := 118140960795 + 6721121 * 2 ^ 59
def prefixEnd_6721121 : Nat := 4983230072969 + 3 ^ 40 * 6721121 * 2
def baseEnd_6721121 : Nat := 1150388536675834438959211

theorem tailTrace_6721121 : CollatzResearch.WordTrace tailWord_6721121 prefixEnd_6721121 1150388536675834438959211 := by
  unfold tailWord_6721121
  simp only [CollatzResearch.WordTrace]
  refine ⟨245139421883533967924827217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163426281255689311949884811 245139421883533967924827217)
  ·
    refine ⟨183854566412650475943620413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245139421883533967924827217 183854566412650475943620413)
    ·
      refine ⟨68945462404743928478857655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 183854566412650475943620413 68945462404743928478857655)
      ·
        refine ⟨103418193607115892718286483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68945462404743928478857655 103418193607115892718286483)
        ·
          refine ⟨155127290410673839077429725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103418193607115892718286483 155127290410673839077429725)
          ·
            refine ⟨58172733904002689654036147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 155127290410673839077429725 58172733904002689654036147)
            ·
              refine ⟨87259100856004034481054221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58172733904002689654036147 87259100856004034481054221)
              ·
                refine ⟨32722162821001512930395333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 87259100856004034481054221 32722162821001512930395333)
                ·
                  refine ⟨6135405528937783674449125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32722162821001512930395333 6135405528937783674449125)
                  ·
                    refine ⟨1150388536675834438959211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6135405528937783674449125 1150388536675834438959211)
                    ·
                      rfl

theorem cell23_6721121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 3, 4, 4].length) (baseStart_6721121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6721121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6721121 prefixEnd_6721121 := by exact prefixLift 6721121
  have htrace : WordTrace (prefixWord ++ tailWord_6721121) baseStart_6721121 baseEnd_6721121 := by
    simpa [prefixWord, tailWord_6721121, baseEnd_6721121] using wordTrace_append hprefix tailTrace_6721121
  have hstable : (prefixWord ++ tailWord_6721121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6721121).length < 2 ^ (prefixWord ++ tailWord_6721121).sum := by decide
  have hdescent : baseEnd_6721121 < baseStart_6721121 := by decide
  rcases family_descends (prefixWord ++ tailWord_6721121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6721161 : List Nat := [1, 2, 1, 1, 4, 1, 3, 1, 3, 3, 3]
def baseStart_6721161 : Nat := 118140960795 + 6721161 * 2 ^ 59
def prefixEnd_6721161 : Nat := 4983230072969 + 3 ^ 40 * 6721161 * 2
def baseEnd_6721161 : Nat := 3451186149253683160377449

theorem tailTrace_6721161 : CollatzResearch.WordTrace tailWord_6721161 prefixEnd_6721161 3451186149253683160377449 := by
  unfold tailWord_6721161
  simp only [CollatzResearch.WordTrace]
  refine ⟨245140880803389054756283337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163427253868926036504188891 245140880803389054756283337)
  ·
    refine ⟨183855660602541791067212503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245140880803389054756283337 183855660602541791067212503)
    ·
      refine ⟨275783490903812686600818755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183855660602541791067212503 275783490903812686600818755)
      ·
        refine ⟨413675236355719029901228133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275783490903812686600818755 413675236355719029901228133)
        ·
          refine ⟨77564106816697318106480275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 413675236355719029901228133 77564106816697318106480275)
          ·
            refine ⟨116346160225045977159720413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77564106816697318106480275 116346160225045977159720413)
            ·
              refine ⟨43629810084392241434895155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 116346160225045977159720413 43629810084392241434895155)
              ·
                refine ⟨65444715126588362152342733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43629810084392241434895155 65444715126588362152342733)
                ·
                  refine ⟨24541768172470635807128525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65444715126588362152342733 24541768172470635807128525)
                  ·
                    refine ⟨9203163064676488427673197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24541768172470635807128525 9203163064676488427673197)
                    ·
                      refine ⟨3451186149253683160377449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9203163064676488427673197 3451186149253683160377449)
                      ·
                        rfl

theorem cell23_6721161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 1, 3, 3, 3].length) (baseStart_6721161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6721161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6721161 prefixEnd_6721161 := by exact prefixLift 6721161
  have htrace : WordTrace (prefixWord ++ tailWord_6721161) baseStart_6721161 baseEnd_6721161 := by
    simpa [prefixWord, tailWord_6721161, baseEnd_6721161] using wordTrace_append hprefix tailTrace_6721161
  have hstable : (prefixWord ++ tailWord_6721161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6721161).length < 2 ^ (prefixWord ++ tailWord_6721161).sum := by decide
  have hdescent : baseEnd_6721161 < baseStart_6721161 := by decide
  rcases family_descends (prefixWord ++ tailWord_6721161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6721172 : List Nat := [2, 4, 2, 2, 2, 1, 2, 2, 2, 4]
def baseStart_6721172 : Nat := 118140960795 + 6721172 * 2 ^ 59
def prefixEnd_6721172 : Nat := 4983230072969 + 3 ^ 40 * 6721172 * 2
def baseEnd_6721172 : Nat := 1150397265846960872446633

theorem tailTrace_6721172 : CollatzResearch.WordTrace tailWord_6721172 prefixEnd_6721172 1150397265846960872446633 := by
  unfold tailWord_6721172
  simp only [CollatzResearch.WordTrace]
  refine ⟨122570641003174601817466885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163427521337566135756622513 122570641003174601817466885)
  ·
    refine ⟨22981995188095237840775041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 122570641003174601817466885 22981995188095237840775041)
    ·
      refine ⟨17236496391071428380581281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22981995188095237840775041 17236496391071428380581281)
      ·
        refine ⟨12927372293303571285435961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17236496391071428380581281 12927372293303571285435961)
        ·
          refine ⟨9695529219977678464076971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12927372293303571285435961 9695529219977678464076971)
          ·
            refine ⟨14543293829966517696115457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9695529219977678464076971 14543293829966517696115457)
            ·
              refine ⟨10907470372474888272086593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14543293829966517696115457 10907470372474888272086593)
              ·
                refine ⟨8180602779356166204064945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10907470372474888272086593 8180602779356166204064945)
                ·
                  refine ⟨6135452084517124653048709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8180602779356166204064945 6135452084517124653048709)
                  ·
                    refine ⟨1150397265846960872446633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6135452084517124653048709 1150397265846960872446633)
                    ·
                      rfl

theorem cell23_6721172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 2, 2, 2, 4].length) (baseStart_6721172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6721172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6721172 prefixEnd_6721172 := by exact prefixLift 6721172
  have htrace : WordTrace (prefixWord ++ tailWord_6721172) baseStart_6721172 baseEnd_6721172 := by
    simpa [prefixWord, tailWord_6721172, baseEnd_6721172] using wordTrace_append hprefix tailTrace_6721172
  have hstable : (prefixWord ++ tailWord_6721172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6721172).length < 2 ^ (prefixWord ++ tailWord_6721172).sum := by decide
  have hdescent : baseEnd_6721172 < baseStart_6721172 := by decide
  rcases family_descends (prefixWord ++ tailWord_6721172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6721221 : List Nat := [1, 3, 1, 1, 1, 1, 2, 2, 4, 4, 3]
def baseStart_6721221 : Nat := 118140960795 + 6721221 * 2 ^ 59
def prefixEnd_6721221 : Nat := 4983230072969 + 3 ^ 40 * 6721221 * 2
def baseEnd_6721221 : Nat := 3451216958092952925627173

theorem tailTrace_6721221 : CollatzResearch.WordTrace tailWord_6721221 prefixEnd_6721221 3451216958092952925627173 := by
  unfold tailWord_6721221
  simp only [CollatzResearch.WordTrace]
  refine ⟨245143069183171685003467517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163428712788781123335645011 245143069183171685003467517)
  ·
    refine ⟨91928650943689381876300319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 245143069183171685003467517 91928650943689381876300319)
    ·
      refine ⟨137892976415534072814450479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91928650943689381876300319 137892976415534072814450479)
      ·
        refine ⟨206839464623301109221675719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137892976415534072814450479 206839464623301109221675719)
        ·
          refine ⟨310259196934951663832513579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206839464623301109221675719 310259196934951663832513579)
          ·
            refine ⟨465388795402427495748770369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 310259196934951663832513579 465388795402427495748770369)
            ·
              refine ⟨349041596551820621811577777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 465388795402427495748770369 349041596551820621811577777)
              ·
                refine ⟨261781197413865466358683333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 349041596551820621811577777 261781197413865466358683333)
                ·
                  refine ⟨49083974515099774942253125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 261781197413865466358683333 49083974515099774942253125)
                  ·
                    refine ⟨9203245221581207801672461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 49083974515099774942253125 9203245221581207801672461)
                    ·
                      refine ⟨3451216958092952925627173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9203245221581207801672461 3451216958092952925627173)
                      ·
                        rfl

theorem cell23_6721221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 2, 4, 4, 3].length) (baseStart_6721221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6721221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6721221 prefixEnd_6721221 := by exact prefixLift 6721221
  have htrace : WordTrace (prefixWord ++ tailWord_6721221) baseStart_6721221 baseEnd_6721221 := by
    simpa [prefixWord, tailWord_6721221, baseEnd_6721221] using wordTrace_append hprefix tailTrace_6721221
  have hstable : (prefixWord ++ tailWord_6721221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6721221).length < 2 ^ (prefixWord ++ tailWord_6721221).sum := by decide
  have hdescent : baseEnd_6721221 < baseStart_6721221 := by decide
  rcases family_descends (prefixWord ++ tailWord_6721221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6721229 : List Nat := [1, 6, 2, 1, 1, 1, 3, 2, 2, 1, 3]
def baseStart_6721229 : Nat := 118140960795 + 6721229 * 2 ^ 59
def prefixEnd_6721229 : Nat := 4983230072969 + 3 ^ 40 * 6721229 * 2
def baseEnd_6721229 : Nat := 3451221065938188894327137

theorem tailTrace_6721229 : CollatzResearch.WordTrace tailWord_6721229 prefixEnd_6721229 3451221065938188894327137 := by
  unfold tailWord_6721229
  simp only [CollatzResearch.WordTrace]
  refine ⟨245143360967142702369758741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163428907311428468246505827 245143360967142702369758741)
  ·
    refine ⟨11491095045334814173582441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 245143360967142702369758741 11491095045334814173582441)
    ·
      refine ⟨8618321284001110630186831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11491095045334814173582441 8618321284001110630186831)
      ·
        refine ⟨12927481926001665945280247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8618321284001110630186831 12927481926001665945280247)
        ·
          refine ⟨19391222889002498917920371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12927481926001665945280247 19391222889002498917920371)
          ·
            refine ⟨29086834333503748376880557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19391222889002498917920371 29086834333503748376880557)
            ·
              refine ⟨10907562875063905641330209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29086834333503748376880557 10907562875063905641330209)
              ·
                refine ⟨8180672156297929230997657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10907562875063905641330209 8180672156297929230997657)
                ·
                  refine ⟨6135504117223446923248243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8180672156297929230997657 6135504117223446923248243)
                  ·
                    refine ⟨9203256175835170384872365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6135504117223446923248243 9203256175835170384872365)
                    ·
                      refine ⟨3451221065938188894327137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9203256175835170384872365 3451221065938188894327137)
                      ·
                        rfl

theorem cell23_6721229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 3, 2, 2, 1, 3].length) (baseStart_6721229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6721229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6721229 prefixEnd_6721229 := by exact prefixLift 6721229
  have htrace : WordTrace (prefixWord ++ tailWord_6721229) baseStart_6721229 baseEnd_6721229 := by
    simpa [prefixWord, tailWord_6721229, baseEnd_6721229] using wordTrace_append hprefix tailTrace_6721229
  have hstable : (prefixWord ++ tailWord_6721229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6721229).length < 2 ^ (prefixWord ++ tailWord_6721229).sum := by decide
  have hdescent : baseEnd_6721229 < baseStart_6721229 := by decide
  rcases family_descends (prefixWord ++ tailWord_6721229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6721241 : List Nat := [1, 2, 1, 2, 3, 3, 1, 3, 7]
def baseStart_6721241 : Nat := 118140960795 + 6721241 * 2 ^ 59
def prefixEnd_6721241 : Nat := 4983230072969 + 3 ^ 40 * 6721241 * 2
def baseEnd_6721241 : Nat := 383469691967338094153009

theorem tailTrace_6721241 : CollatzResearch.WordTrace tailWord_6721241 prefixEnd_6721241 383469691967338094153009 := by
  unfold tailWord_6721241
  simp only [CollatzResearch.WordTrace]
  refine ⟨245143798643099228419195577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163429199095399485612797051 245143798643099228419195577)
  ·
    refine ⟨183857848982324421314396683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245143798643099228419195577 183857848982324421314396683)
    ·
      refine ⟨275786773473486631971595025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183857848982324421314396683 275786773473486631971595025)
      ·
        refine ⟨206840080105114973978696269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 275786773473486631971595025 206840080105114973978696269)
        ·
          refine ⟨77565030039418115242011101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 206840080105114973978696269 77565030039418115242011101)
          ·
            refine ⟨29086886264781793215754163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77565030039418115242011101 29086886264781793215754163)
            ·
              refine ⟨43630329397172689823631245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29086886264781793215754163 43630329397172689823631245)
              ·
                refine ⟨16361373523939758683861717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43630329397172689823631245 16361373523939758683861717)
                ·
                  refine ⟨383469691967338094153009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16361373523939758683861717 383469691967338094153009)
                  ·
                    rfl

theorem cell23_6721241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 3, 7].length) (baseStart_6721241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6721241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6721241 prefixEnd_6721241 := by exact prefixLift 6721241
  have htrace : WordTrace (prefixWord ++ tailWord_6721241) baseStart_6721241 baseEnd_6721241 := by
    simpa [prefixWord, tailWord_6721241, baseEnd_6721241] using wordTrace_append hprefix tailTrace_6721241
  have hstable : (prefixWord ++ tailWord_6721241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6721241).length < 2 ^ (prefixWord ++ tailWord_6721241).sum := by decide
  have hdescent : baseEnd_6721241 < baseStart_6721241 := by decide
  rcases family_descends (prefixWord ++ tailWord_6721241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6721271 : List Nat := [1, 1, 3, 1, 1, 1, 6, 1, 1, 7]
def baseStart_6721271 : Nat := 118140960795 + 6721271 * 2 ^ 59
def prefixEnd_6721271 : Nat := 4983230072969 + 3 ^ 40 * 6721271 * 2
def baseEnd_6721271 : Nat := 1150414210708559243333981

theorem tailTrace_6721271 : CollatzResearch.WordTrace tailWord_6721271 prefixEnd_6721271 1150414210708559243333981 := by
  unfold tailWord_6721271
  simp only [CollatzResearch.WordTrace]
  refine ⟨245144892832990543542787667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163429928555327029028525111 245144892832990543542787667)
  ·
    refine ⟨367717339249485815314181501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245144892832990543542787667 367717339249485815314181501)
    ·
      refine ⟨137894002218557180742818063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 367717339249485815314181501 137894002218557180742818063)
      ·
        refine ⟨206841003327835771114227095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137894002218557180742818063 206841003327835771114227095)
        ·
          refine ⟨310261504991753656671340643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206841003327835771114227095 310261504991753656671340643)
          ·
            refine ⟨465392257487630485007010965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 310261504991753656671340643 465392257487630485007010965)
            ·
              refine ⟨21815262069732678984703639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 465392257487630485007010965 21815262069732678984703639)
              ·
                refine ⟨32722893104599018477055459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21815262069732678984703639 32722893104599018477055459)
                ·
                  refine ⟨49084339656898527715583189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32722893104599018477055459 49084339656898527715583189)
                  ·
                    refine ⟨1150414210708559243333981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49084339656898527715583189 1150414210708559243333981)
                    ·
                      rfl

theorem cell23_6721271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 1, 1, 7].length) (baseStart_6721271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6721271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6721271 prefixEnd_6721271 := by exact prefixLift 6721271
  have htrace : WordTrace (prefixWord ++ tailWord_6721271) baseStart_6721271 baseEnd_6721271 := by
    simpa [prefixWord, tailWord_6721271, baseEnd_6721271] using wordTrace_append hprefix tailTrace_6721271
  have hstable : (prefixWord ++ tailWord_6721271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6721271).length < 2 ^ (prefixWord ++ tailWord_6721271).sum := by decide
  have hdescent : baseEnd_6721271 < baseStart_6721271 := by decide
  rcases family_descends (prefixWord ++ tailWord_6721271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6721288 : List Nat := [2, 1, 3, 2, 2, 1, 3, 2, 2, 5]
def baseStart_6721288 : Nat := 118140960795 + 6721288 * 2 ^ 59
def prefixEnd_6721288 : Nat := 4983230072969 + 3 ^ 40 * 6721288 * 2
def baseEnd_6721288 : Nat := 1150417120432268054496455

theorem tailTrace_6721288 : CollatzResearch.WordTrace tailWord_6721288 prefixEnd_6721288 1150417120432268054496455 := by
  unfold tailWord_6721288
  simp only [CollatzResearch.WordTrace]
  refine ⟨122572756436964477723078259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163430341915952636964104345 122572756436964477723078259)
  ·
    refine ⟨183859134655446716584617389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122572756436964477723078259 183859134655446716584617389)
    ·
      refine ⟨68947175495792518719231521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 183859134655446716584617389 68947175495792518719231521)
      ·
        refine ⟨51710381621844389039423641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68947175495792518719231521 51710381621844389039423641)
        ·
          refine ⟨38782786216383291779567731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51710381621844389039423641 38782786216383291779567731)
          ·
            refine ⟨58174179324574937669351597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38782786216383291779567731 58174179324574937669351597)
            ·
              refine ⟨21815317246715601626006849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58174179324574937669351597 21815317246715601626006849)
              ·
                refine ⟨16361487935036701219505137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21815317246715601626006849 16361487935036701219505137)
                ·
                  refine ⟨12271115951277525914628853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16361487935036701219505137 12271115951277525914628853)
                  ·
                    refine ⟨1150417120432268054496455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12271115951277525914628853 1150417120432268054496455)
                    ·
                      rfl

theorem cell23_6721288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 2, 2, 5].length) (baseStart_6721288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6721288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6721288 prefixEnd_6721288 := by exact prefixLift 6721288
  have htrace : WordTrace (prefixWord ++ tailWord_6721288) baseStart_6721288 baseEnd_6721288 := by
    simpa [prefixWord, tailWord_6721288, baseEnd_6721288] using wordTrace_append hprefix tailTrace_6721288
  have hstable : (prefixWord ++ tailWord_6721288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6721288).length < 2 ^ (prefixWord ++ tailWord_6721288).sum := by decide
  have hdescent : baseEnd_6721288 < baseStart_6721288 := by decide
  rcases family_descends (prefixWord ++ tailWord_6721288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6721308 : List Nat := [2, 2, 3, 1, 1, 2, 1, 2, 4, 1, 4]
def baseStart_6721308 : Nat := 118140960795 + 6721308 * 2 ^ 59
def prefixEnd_6721308 : Nat := 4983230072969 + 3 ^ 40 * 6721308 * 2
def baseEnd_6721308 : Nat := 3451261630909894085239273

theorem tailTrace_6721308 : CollatzResearch.WordTrace tailWord_6721308 prefixEnd_6721308 3451261630909894085239273 := by
  unfold tailWord_6721308
  simp only [CollatzResearch.WordTrace]
  refine ⟨122573121166928249430942289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163430828222570999241256385 122573121166928249430942289)
  ·
    refine ⟨91929840875196187073206717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122573121166928249430942289 91929840875196187073206717)
    ·
      refine ⟨34473690328198570152452519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91929840875196187073206717 34473690328198570152452519)
      ·
        refine ⟨51710535492297855228678779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34473690328198570152452519 51710535492297855228678779)
        ·
          refine ⟨77565803238446782843018169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51710535492297855228678779 77565803238446782843018169)
          ·
            refine ⟨58174352428835087132263627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77565803238446782843018169 58174352428835087132263627)
            ·
              refine ⟨87261528643252630698395441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58174352428835087132263627 87261528643252630698395441)
              ·
                refine ⟨65446146482439473023796581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87261528643252630698395441 65446146482439473023796581)
                ·
                  refine ⟨12271152465457401191961859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65446146482439473023796581 12271152465457401191961859)
                  ·
                    refine ⟨18406728698186101787942789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12271152465457401191961859 18406728698186101787942789)
                    ·
                      refine ⟨3451261630909894085239273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18406728698186101787942789 3451261630909894085239273)
                      ·
                        rfl

theorem cell23_6721308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 2, 4, 1, 4].length) (baseStart_6721308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6721308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6721308 prefixEnd_6721308 := by exact prefixLift 6721308
  have htrace : WordTrace (prefixWord ++ tailWord_6721308) baseStart_6721308 baseEnd_6721308 := by
    simpa [prefixWord, tailWord_6721308, baseEnd_6721308] using wordTrace_append hprefix tailTrace_6721308
  have hstable : (prefixWord ++ tailWord_6721308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6721308).length < 2 ^ (prefixWord ++ tailWord_6721308).sum := by decide
  have hdescent : baseEnd_6721308 < baseStart_6721308 := by decide
  rcases family_descends (prefixWord ++ tailWord_6721308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6721352 : List Nat := [2, 1, 3, 1, 1, 5, 1, 4, 1, 4]
def baseStart_6721352 : Nat := 118140960795 + 6721352 * 2 ^ 59
def prefixEnd_6721352 : Nat := 4983230072969 + 3 ^ 40 * 6721352 * 2
def baseEnd_6721352 : Nat := 1150428074686230637696357

theorem tailTrace_6721352 : CollatzResearch.WordTrace tailWord_6721352 prefixEnd_6721352 1150428074686230637696357 := by
  unfold tailWord_6721352
  simp only [CollatzResearch.WordTrace]
  refine ⟨122573923572848547188243155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163431898097131396250990873 122573923572848547188243155)
  ·
    refine ⟨183860885359272820782364733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122573923572848547188243155 183860885359272820782364733)
    ·
      refine ⟨68947832009727307793386775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 183860885359272820782364733 68947832009727307793386775)
      ·
        refine ⟨103421748014590961690080163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68947832009727307793386775 103421748014590961690080163)
        ·
          refine ⟨155132622021886442535120245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103421748014590961690080163 155132622021886442535120245)
          ·
            refine ⟨14543683314551853987667523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 155132622021886442535120245 14543683314551853987667523)
            ·
              refine ⟨21815524971827780981501285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14543683314551853987667523 21815524971827780981501285)
              ·
                refine ⟨4090410932217708934031491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21815524971827780981501285 4090410932217708934031491)
                ·
                  refine ⟨6135616398326563401047237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4090410932217708934031491 6135616398326563401047237)
                  ·
                    refine ⟨1150428074686230637696357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6135616398326563401047237 1150428074686230637696357)
                    ·
                      rfl

theorem cell23_6721352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 4, 1, 4].length) (baseStart_6721352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6721352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6721352 prefixEnd_6721352 := by exact prefixLift 6721352
  have htrace : WordTrace (prefixWord ++ tailWord_6721352) baseStart_6721352 baseEnd_6721352 := by
    simpa [prefixWord, tailWord_6721352, baseEnd_6721352] using wordTrace_append hprefix tailTrace_6721352
  have hstable : (prefixWord ++ tailWord_6721352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6721352).length < 2 ^ (prefixWord ++ tailWord_6721352).sum := by decide
  have hdescent : baseEnd_6721352 < baseStart_6721352 := by decide
  rcases family_descends (prefixWord ++ tailWord_6721352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6721358 : List Nat := [4, 1, 1, 1, 1, 1, 1, 1, 4, 5, 3]
def baseStart_6721358 : Nat := 118140960795 + 6721358 * 2 ^ 59
def prefixEnd_6721358 : Nat := 4983230072969 + 3 ^ 40 * 6721358 * 2
def baseEnd_6721358 : Nat := 3451287304942618889614043

theorem tailTrace_6721358 : CollatzResearch.WordTrace tailWord_6721358 prefixEnd_6721358 3451287304942618889614043 := by
  unfold tailWord_6721358
  simp only [CollatzResearch.WordTrace]
  refine ⟨30643508247959419675150591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 163432043989116904934136485 30643508247959419675150591)
  ·
    refine ⟨45965262371939129512725887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30643508247959419675150591 45965262371939129512725887)
    ·
      refine ⟨68947893557908694269088831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45965262371939129512725887 68947893557908694269088831)
      ·
        refine ⟨103421840336863041403633247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68947893557908694269088831 103421840336863041403633247)
        ·
          refine ⟨155132760505294562105449871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103421840336863041403633247 155132760505294562105449871)
          ·
            refine ⟨232699140757941843158174807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155132760505294562105449871 232699140757941843158174807)
            ·
              refine ⟨349048711136912764737262211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 232699140757941843158174807 349048711136912764737262211)
              ·
                refine ⟨523573066705369147105893317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 349048711136912764737262211 523573066705369147105893317)
                ·
                  refine ⟨98169950007256715082354997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 523573066705369147105893317 98169950007256715082354997)
                  ·
                    refine ⟨9203432813180317038970781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 98169950007256715082354997 9203432813180317038970781)
                    ·
                      refine ⟨3451287304942618889614043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9203432813180317038970781 3451287304942618889614043)
                      ·
                        rfl

theorem cell23_6721358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 4, 5, 3].length) (baseStart_6721358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6721358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6721358 prefixEnd_6721358 := by exact prefixLift 6721358
  have htrace : WordTrace (prefixWord ++ tailWord_6721358) baseStart_6721358 baseEnd_6721358 := by
    simpa [prefixWord, tailWord_6721358, baseEnd_6721358] using wordTrace_append hprefix tailTrace_6721358
  have hstable : (prefixWord ++ tailWord_6721358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6721358).length < 2 ^ (prefixWord ++ tailWord_6721358).sum := by decide
  have hdescent : baseEnd_6721358 < baseStart_6721358 := by decide
  rcases family_descends (prefixWord ++ tailWord_6721358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6721375 : List Nat := [1, 1, 2, 3, 1, 4, 1, 1, 5, 1, 3]
def baseStart_6721375 : Nat := 118140960795 + 6721375 * 2 ^ 59
def prefixEnd_6721375 : Nat := 4983230072969 + 3 ^ 40 * 6721375 * 2
def baseEnd_6721375 : Nat := 3451296034113745323101465

theorem tailTrace_6721375 : CollatzResearch.WordTrace tailWord_6721375 prefixEnd_6721375 3451296034113745323101465 := by
  unfold tailWord_6721375
  simp only [CollatzResearch.WordTrace]
  refine ⟨245148686024613769304573579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163432457349742512869715719 245148686024613769304573579)
  ·
    refine ⟨367723029036920653956860369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245148686024613769304573579 367723029036920653956860369)
    ·
      refine ⟨275792271777690490467645277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 367723029036920653956860369 275792271777690490467645277)
      ·
        refine ⟨103422101916633933925366979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 275792271777690490467645277 103422101916633933925366979)
        ·
          refine ⟨155133152874950900888050469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103422101916633933925366979 155133152874950900888050469)
          ·
            refine ⟨29087466164053293916509463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 155133152874950900888050469 29087466164053293916509463)
            ·
              refine ⟨43631199246079940874764195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29087466164053293916509463 43631199246079940874764195)
              ·
                refine ⟨65446798869119911312146293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43631199246079940874764195 65446798869119911312146293)
                ·
                  refine ⟨6135637393979991685513715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 65446798869119911312146293 6135637393979991685513715)
                  ·
                    refine ⟨9203456090969987528270573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6135637393979991685513715 9203456090969987528270573)
                    ·
                      refine ⟨3451296034113745323101465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9203456090969987528270573 3451296034113745323101465)
                      ·
                        rfl

theorem cell23_6721375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 1, 5, 1, 3].length) (baseStart_6721375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6721375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6721375 prefixEnd_6721375 := by exact prefixLift 6721375
  have htrace : WordTrace (prefixWord ++ tailWord_6721375) baseStart_6721375 baseEnd_6721375 := by
    simpa [prefixWord, tailWord_6721375, baseEnd_6721375] using wordTrace_append hprefix tailTrace_6721375
  have hstable : (prefixWord ++ tailWord_6721375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6721375).length < 2 ^ (prefixWord ++ tailWord_6721375).sum := by decide
  have hdescent : baseEnd_6721375 < baseStart_6721375 := by decide
  rcases family_descends (prefixWord ++ tailWord_6721375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6721379 : List Nat := [1, 1, 1, 5, 5, 1, 1, 1, 2, 2, 3]
def baseStart_6721379 : Nat := 118140960795 + 6721379 * 2 ^ 59
def prefixEnd_6721379 : Nat := 4983230072969 + 3 ^ 40 * 6721379 * 2
def baseEnd_6721379 : Nat := 3451298088036363307451447

theorem tailTrace_6721379 : CollatzResearch.WordTrace tailWord_6721379 prefixEnd_6721379 3451298088036363307451447 := by
  unfold tailWord_6721379
  simp only [CollatzResearch.WordTrace]
  refine ⟨245148831916599277987719191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163432554611066185325146127 245148831916599277987719191)
  ·
    refine ⟨367723247874898916981578787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245148831916599277987719191 367723247874898916981578787)
    ·
      refine ⟨551584871812348375472368181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 367723247874898916981578787 551584871812348375472368181)
      ·
        refine ⟨51711081732407660200534517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 551584871812348375472368181 51711081732407660200534517)
        ·
          refine ⟨4847913912413218143800111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 51711081732407660200534517 4847913912413218143800111)
          ·
            refine ⟨7271870868619827215700167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4847913912413218143800111 7271870868619827215700167)
            ·
              refine ⟨10907806302929740823550251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7271870868619827215700167 10907806302929740823550251)
              ·
                refine ⟨16361709454394611235325377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10907806302929740823550251 16361709454394611235325377)
                ·
                  refine ⟨12271282090795958426494033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16361709454394611235325377 12271282090795958426494033)
                  ·
                    refine ⟨9203461568096968819870525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12271282090795958426494033 9203461568096968819870525)
                    ·
                      refine ⟨3451298088036363307451447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9203461568096968819870525 3451298088036363307451447)
                      ·
                        rfl

theorem cell23_6721379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 1, 1, 2, 2, 3].length) (baseStart_6721379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6721379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6721379 prefixEnd_6721379 := by exact prefixLift 6721379
  have htrace : WordTrace (prefixWord ++ tailWord_6721379) baseStart_6721379 baseEnd_6721379 := by
    simpa [prefixWord, tailWord_6721379, baseEnd_6721379] using wordTrace_append hprefix tailTrace_6721379
  have hstable : (prefixWord ++ tailWord_6721379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6721379).length < 2 ^ (prefixWord ++ tailWord_6721379).sum := by decide
  have hdescent : baseEnd_6721379 < baseStart_6721379 := by decide
  rcases family_descends (prefixWord ++ tailWord_6721379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6721386 : List Nat := [3, 1, 3, 4, 1, 1, 2, 3, 1, 4]
def baseStart_6721386 : Nat := 118140960795 + 6721386 * 2 ^ 59
def prefixEnd_6721386 : Nat := 4983230072969 + 3 ^ 40 * 6721386 * 2
def baseEnd_6721386 : Nat := 1150433894133648260021305

theorem tailTrace_6721386 : CollatzResearch.WordTrace tailWord_6721386 prefixEnd_6721386 1150433894133648260021305 := by
  unfold tailWord_6721386
  simp only [CollatzResearch.WordTrace]
  refine ⟨61287271806893479545806003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163432724818382612122149341 61287271806893479545806003)
  ·
    refine ⟨91930907710340219318709005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61287271806893479545806003 91930907710340219318709005)
    ·
      refine ⟨34474090391377582244515877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91930907710340219318709005 34474090391377582244515877)
      ·
        refine ⟨6463891948383296670846727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34474090391377582244515877 6463891948383296670846727)
        ·
          refine ⟨9695837922574945006270091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6463891948383296670846727 9695837922574945006270091)
          ·
            refine ⟨14543756883862417509405137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9695837922574945006270091 14543756883862417509405137)
            ·
              refine ⟨10907817662896813132053853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14543756883862417509405137 10907817662896813132053853)
              ·
                refine ⟨4090431623586304924520195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10907817662896813132053853 4090431623586304924520195)
                ·
                  refine ⟨6135647435379457386780293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4090431623586304924520195 6135647435379457386780293)
                  ·
                    refine ⟨1150433894133648260021305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6135647435379457386780293 1150433894133648260021305)
                    ·
                      rfl

theorem cell23_6721386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 2, 3, 1, 4].length) (baseStart_6721386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6721386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6721386 prefixEnd_6721386 := by exact prefixLift 6721386
  have htrace : WordTrace (prefixWord ++ tailWord_6721386) baseStart_6721386 baseEnd_6721386 := by
    simpa [prefixWord, tailWord_6721386, baseEnd_6721386] using wordTrace_append hprefix tailTrace_6721386
  have hstable : (prefixWord ++ tailWord_6721386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6721386).length < 2 ^ (prefixWord ++ tailWord_6721386).sum := by decide
  have hdescent : baseEnd_6721386 < baseStart_6721386 := by decide
  rcases family_descends (prefixWord ++ tailWord_6721386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6721425 : List Nat := [1, 2, 2, 1, 1, 1, 4, 5, 2, 4]
def baseStart_6721425 : Nat := 118140960795 + 6721425 * 2 ^ 59
def prefixEnd_6721425 : Nat := 4983230072969 + 3 ^ 40 * 6721425 * 2
def baseEnd_6721425 : Nat := 1150440569382156709158745

theorem tailTrace_6721425 : CollatzResearch.WordTrace tailWord_6721425 prefixEnd_6721425 1150440569382156709158745 := by
  unfold tailWord_6721425
  simp only [CollatzResearch.WordTrace]
  refine ⟨245150509674432627843893729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163433673116288418562595819 245150509674432627843893729)
  ·
    refine ⟨183862882255824470882920297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245150509674432627843893729 183862882255824470882920297)
    ·
      refine ⟨137897161691868353162190223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183862882255824470882920297 137897161691868353162190223)
      ·
        refine ⟨206845742537802529743285335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137897161691868353162190223 206845742537802529743285335)
        ·
          refine ⟨310268613806703794614928003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206845742537802529743285335 310268613806703794614928003)
          ·
            refine ⟨465402920710055691922392005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 310268613806703794614928003 465402920710055691922392005)
            ·
              refine ⟨87263047633135442235448501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 465402920710055691922392005 87263047633135442235448501)
              ·
                refine ⟨8180910715606447709573297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 87263047633135442235448501 8180910715606447709573297)
                ·
                  refine ⟨6135683036704835782179973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8180910715606447709573297 6135683036704835782179973)
                  ·
                    refine ⟨1150440569382156709158745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6135683036704835782179973 1150440569382156709158745)
                    ·
                      rfl

theorem cell23_6721425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 5, 2, 4].length) (baseStart_6721425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6721425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6721425 prefixEnd_6721425 := by exact prefixLift 6721425
  have htrace : WordTrace (prefixWord ++ tailWord_6721425) baseStart_6721425 baseEnd_6721425 := by
    simpa [prefixWord, tailWord_6721425, baseEnd_6721425] using wordTrace_append hprefix tailTrace_6721425
  have hstable : (prefixWord ++ tailWord_6721425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6721425).length < 2 ^ (prefixWord ++ tailWord_6721425).sum := by decide
  have hdescent : baseEnd_6721425 < baseStart_6721425 := by decide
  rcases family_descends (prefixWord ++ tailWord_6721425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6721449 : List Nat := [1, 2, 1, 1, 1, 1, 4, 7, 1, 2, 2]
def baseStart_6721449 : Nat := 118140960795 + 6721449 * 2 ^ 59
def prefixEnd_6721449 : Nat := 4983230072969 + 3 ^ 40 * 6721449 * 2
def baseEnd_6721449 : Nat := 3451334031682178033576125

theorem tailTrace_6721449 : CollatzResearch.WordTrace tailWord_6721449 prefixEnd_6721449 3451334031682178033576125 := by
  unfold tailWord_6721449
  simp only [CollatzResearch.WordTrace]
  refine ⟨245151385026345679942767401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163434256684230453295178267 245151385026345679942767401)
  ·
    refine ⟨183863538769759259957075551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245151385026345679942767401 183863538769759259957075551)
    ·
      refine ⟨275795308154638889935613327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183863538769759259957075551 275795308154638889935613327)
      ·
        refine ⟨413692962231958334903419991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275795308154638889935613327 413692962231958334903419991)
        ·
          refine ⟨620539443347937502355129987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 413692962231958334903419991 620539443347937502355129987)
          ·
            refine ⟨930809165021906253532694981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 620539443347937502355129987 930809165021906253532694981)
            ·
              refine ⟨174526718441607422537380309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 930809165021906253532694981 174526718441607422537380309)
              ·
                refine ⟨4090469963475173965719851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 174526718441607422537380309 4090469963475173965719851)
                ·
                  refine ⟨6135704945212760948579777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4090469963475173965719851 6135704945212760948579777)
                  ·
                    refine ⟨4601778708909570711434833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6135704945212760948579777 4601778708909570711434833)
                    ·
                      refine ⟨3451334031682178033576125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4601778708909570711434833 3451334031682178033576125)
                      ·
                        rfl

theorem cell23_6721449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 7, 1, 2, 2].length) (baseStart_6721449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6721449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6721449 prefixEnd_6721449 := by exact prefixLift 6721449
  have htrace : WordTrace (prefixWord ++ tailWord_6721449) baseStart_6721449 baseEnd_6721449 := by
    simpa [prefixWord, tailWord_6721449, baseEnd_6721449] using wordTrace_append hprefix tailTrace_6721449
  have hstable : (prefixWord ++ tailWord_6721449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6721449).length < 2 ^ (prefixWord ++ tailWord_6721449).sum := by decide
  have hdescent : baseEnd_6721449 < baseStart_6721449 := by decide
  rcases family_descends (prefixWord ++ tailWord_6721449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6721460 : List Nat := [2, 5, 2, 1, 2, 1, 3, 2, 1, 1, 3]
def baseStart_6721460 : Nat := 118140960795 + 6721460 * 2 ^ 59
def prefixEnd_6721460 : Nat := 4983230072969 + 3 ^ 40 * 6721460 * 2
def baseEnd_6721460 : Nat := 3451339679969377490538575

theorem tailTrace_6721460 : CollatzResearch.WordTrace tailWord_6721460 prefixEnd_6721460 3451339679969377490538575 := by
  unfold tailWord_6721460
  simp only [CollatzResearch.WordTrace]
  refine ⟨122575893114652914410708917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163434524152870552547611889 122575893114652914410708917)
  ·
    refine ⟨11491489979498710726003961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 122575893114652914410708917 11491489979498710726003961)
    ·
      refine ⟨8618617484624033044502971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11491489979498710726003961 8618617484624033044502971)
      ·
        refine ⟨12927926226936049566754457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8618617484624033044502971 12927926226936049566754457)
        ·
          refine ⟨9695944670202037175065843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12927926226936049566754457 9695944670202037175065843)
          ·
            refine ⟨14543917005303055762598765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9695944670202037175065843 14543917005303055762598765)
            ·
              refine ⟨5453968876988645910974537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14543917005303055762598765 5453968876988645910974537)
              ·
                refine ⟨4090476657741484433230903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5453968876988645910974537 4090476657741484433230903)
                ·
                  refine ⟨6135714986612226649846355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4090476657741484433230903 6135714986612226649846355)
                  ·
                    refine ⟨9203572479918339974769533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6135714986612226649846355 9203572479918339974769533)
                    ·
                      refine ⟨3451339679969377490538575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9203572479918339974769533 3451339679969377490538575)
                      ·
                        rfl

theorem cell23_6721460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 3, 2, 1, 1, 3].length) (baseStart_6721460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6721460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6721460 prefixEnd_6721460 := by exact prefixLift 6721460
  have htrace : WordTrace (prefixWord ++ tailWord_6721460) baseStart_6721460 baseEnd_6721460 := by
    simpa [prefixWord, tailWord_6721460, baseEnd_6721460] using wordTrace_append hprefix tailTrace_6721460
  have hstable : (prefixWord ++ tailWord_6721460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6721460).length < 2 ^ (prefixWord ++ tailWord_6721460).sum := by decide
  have hdescent : baseEnd_6721460 < baseStart_6721460 := by decide
  rcases family_descends (prefixWord ++ tailWord_6721460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6721517 : List Nat := [1, 5, 1, 4, 1, 2, 2, 2, 1, 2, 2]
def baseStart_6721517 : Nat := 118140960795 + 6721517 * 2 ^ 59
def prefixEnd_6721517 : Nat := 4983230072969 + 3 ^ 40 * 6721517 * 2
def baseEnd_6721517 : Nat := 3451368948366683767525813

theorem tailTrace_6721517 : CollatzResearch.WordTrace tailWord_6721517 prefixEnd_6721517 3451368948366683767525813 := by
  unfold tailWord_6721517
  simp only [CollatzResearch.WordTrace]
  refine ⟨245153865190099327556242805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163435910126732885037495203 245153865190099327556242805)
  ·
    refine ⟨22983174861571811958397763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 245153865190099327556242805 22983174861571811958397763)
    ·
      refine ⟨34474762292357717937596645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22983174861571811958397763 34474762292357717937596645)
      ·
        refine ⟨6464017929817072113299371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34474762292357717937596645 6464017929817072113299371)
        ·
          refine ⟨9696026894725608169949057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6464017929817072113299371 9696026894725608169949057)
          ·
            refine ⟨7272020171044206127461793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9696026894725608169949057 7272020171044206127461793)
            ·
              refine ⟨5454015128283154595596345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7272020171044206127461793 5454015128283154595596345)
              ·
                refine ⟨4090511346212365946697259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5454015128283154595596345 4090511346212365946697259)
                ·
                  refine ⟨6135767019318548920045889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4090511346212365946697259 6135767019318548920045889)
                  ·
                    refine ⟨4601825264488911690034417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6135767019318548920045889 4601825264488911690034417)
                    ·
                      refine ⟨3451368948366683767525813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4601825264488911690034417 3451368948366683767525813)
                      ·
                        rfl

theorem cell23_6721517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 2, 2, 1, 2, 2].length) (baseStart_6721517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6721517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6721517 prefixEnd_6721517 := by exact prefixLift 6721517
  have htrace : WordTrace (prefixWord ++ tailWord_6721517) baseStart_6721517 baseEnd_6721517 := by
    simpa [prefixWord, tailWord_6721517, baseEnd_6721517] using wordTrace_append hprefix tailTrace_6721517
  have hstable : (prefixWord ++ tailWord_6721517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6721517).length < 2 ^ (prefixWord ++ tailWord_6721517).sum := by decide
  have hdescent : baseEnd_6721517 < baseStart_6721517 := by decide
  rcases family_descends (prefixWord ++ tailWord_6721517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6721562 : List Nat := [3, 1, 1, 3, 1, 3, 1, 5, 5]
def baseStart_6721562 : Nat := 118140960795 + 6721562 * 2 ^ 59
def prefixEnd_6721562 : Nat := 4983230072969 + 3 ^ 40 * 6721562 * 2
def baseEnd_6721562 : Nat := 383488006110681787940345

theorem tailTrace_6721562 : CollatzResearch.WordTrace tailWord_6721562 prefixEnd_6721562 383488006110681787940345 := by
  unfold tailWord_6721562
  simp only [CollatzResearch.WordTrace]
  refine ⟨61288876618734075060407735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163437004316624200161087293 61288876618734075060407735)
  ·
    refine ⟨91933314928101112590611603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61288876618734075060407735 91933314928101112590611603)
    ·
      refine ⟨137899972392151668885917405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91933314928101112590611603 137899972392151668885917405)
      ·
        refine ⟨51712489647056875832219027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137899972392151668885917405 51712489647056875832219027)
        ·
          refine ⟨77568734470585313748328541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51712489647056875832219027 77568734470585313748328541)
          ·
            refine ⟨29088275426469492655623203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77568734470585313748328541 29088275426469492655623203)
            ·
              refine ⟨43632413139704238983434805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29088275426469492655623203 43632413139704238983434805)
              ·
                refine ⟨4090538731847272404697013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43632413139704238983434805 4090538731847272404697013)
                ·
                  refine ⟨383488006110681787940345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4090538731847272404697013 383488006110681787940345)
                  ·
                    rfl

theorem cell23_6721562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 5, 5].length) (baseStart_6721562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6721562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6721562 prefixEnd_6721562 := by exact prefixLift 6721562
  have htrace : WordTrace (prefixWord ++ tailWord_6721562) baseStart_6721562 baseEnd_6721562 := by
    simpa [prefixWord, tailWord_6721562, baseEnd_6721562] using wordTrace_append hprefix tailTrace_6721562
  have hstable : (prefixWord ++ tailWord_6721562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6721562).length < 2 ^ (prefixWord ++ tailWord_6721562).sum := by decide
  have hdescent : baseEnd_6721562 < baseStart_6721562 := by decide
  rcases family_descends (prefixWord ++ tailWord_6721562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6721595 : List Nat := [1, 1, 1, 1, 1, 2, 1, 6, 4, 1, 4]
def baseStart_6721595 : Nat := 118140960795 + 6721595 * 2 ^ 59
def prefixEnd_6721595 : Nat := 4983230072969 + 3 ^ 40 * 6721595 * 2
def baseEnd_6721595 : Nat := 3451408999857734462350453

theorem tailTrace_6721595 : CollatzResearch.WordTrace tailWord_6721595 prefixEnd_6721595 3451408999857734462350453 := by
  unfold tailWord_6721595
  simp only [CollatzResearch.WordTrace]
  refine ⟨245156710083816746877582239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163437806722544497918388159 245156710083816746877582239)
  ·
    refine ⟨367735065125725120316373359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245156710083816746877582239 367735065125725120316373359)
    ·
      refine ⟨551602597688587680474560039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 367735065125725120316373359 551602597688587680474560039)
      ·
        refine ⟨827403896532881520711840059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 551602597688587680474560039 827403896532881520711840059)
        ·
          refine ⟨1241105844799322281067760089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 827403896532881520711840059 1241105844799322281067760089)
          ·
            refine ⟨930829383599491710800820067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1241105844799322281067760089 930829383599491710800820067)
            ·
              refine ⟨1396244075399237566201230101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 930829383599491710800820067 1396244075399237566201230101)
              ·
                refine ⟨65448941034339260915682661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1396244075399237566201230101 65448941034339260915682661)
                ·
                  refine ⟨12271676443938611421690499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65448941034339260915682661 12271676443938611421690499)
                  ·
                    refine ⟨18407514665907917132535749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12271676443938611421690499 18407514665907917132535749)
                    ·
                      refine ⟨3451408999857734462350453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18407514665907917132535749 3451408999857734462350453)
                      ·
                        rfl

theorem cell23_6721595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 6, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 6, 4, 1, 4].length) (baseStart_6721595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6721595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6721595 prefixEnd_6721595 := by exact prefixLift 6721595
  have htrace : WordTrace (prefixWord ++ tailWord_6721595) baseStart_6721595 baseEnd_6721595 := by
    simpa [prefixWord, tailWord_6721595, baseEnd_6721595] using wordTrace_append hprefix tailTrace_6721595
  have hstable : (prefixWord ++ tailWord_6721595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6721595).length < 2 ^ (prefixWord ++ tailWord_6721595).sum := by decide
  have hdescent : baseEnd_6721595 < baseStart_6721595 := by decide
  rcases family_descends (prefixWord ++ tailWord_6721595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6721612 : List Nat := [2, 2, 1, 3, 1, 1, 2, 2, 1, 6, 2]
def baseStart_6721612 : Nat := 118140960795 + 6721612 * 2 ^ 59
def prefixEnd_6721612 : Nat := 4983230072969 + 3 ^ 40 * 6721612 * 2
def baseEnd_6721612 : Nat := 3451417729028860895837875

theorem tailTrace_6721612 : CollatzResearch.WordTrace tailWord_6721612 prefixEnd_6721612 3451417729028860895837875 := by
  unfold tailWord_6721612
  simp only [CollatzResearch.WordTrace]
  refine ⟨122578665062377579390475545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163438220083170105853967393 122578665062377579390475545)
  ·
    refine ⟨91933998796783184542856659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122578665062377579390475545 91933998796783184542856659)
    ·
      refine ⟨137900998195174776814284989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91933998796783184542856659 137900998195174776814284989)
      ·
        refine ⟨51712874323190541305356871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137900998195174776814284989 51712874323190541305356871)
        ·
          refine ⟨77569311484785811958035307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51712874323190541305356871 77569311484785811958035307)
          ·
            refine ⟨116353967227178717937052961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77569311484785811958035307 116353967227178717937052961)
            ·
              refine ⟨87265475420384038452789721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116353967227178717937052961 87265475420384038452789721)
              ·
                refine ⟨65449106565288028839592291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87265475420384038452789721 65449106565288028839592291)
                ·
                  refine ⟨98173659847932043259388437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65449106565288028839592291 98173659847932043259388437)
                  ·
                    refine ⟨4601890305371814527783833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 98173659847932043259388437 4601890305371814527783833)
                    ·
                      refine ⟨3451417729028860895837875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4601890305371814527783833 3451417729028860895837875)
                      ·
                        rfl

theorem cell23_6721612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 2, 1, 6, 2].length) (baseStart_6721612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6721612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6721612 prefixEnd_6721612 := by exact prefixLift 6721612
  have htrace : WordTrace (prefixWord ++ tailWord_6721612) baseStart_6721612 baseEnd_6721612 := by
    simpa [prefixWord, tailWord_6721612, baseEnd_6721612] using wordTrace_append hprefix tailTrace_6721612
  have hstable : (prefixWord ++ tailWord_6721612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6721612).length < 2 ^ (prefixWord ++ tailWord_6721612).sum := by decide
  have hdescent : baseEnd_6721612 < baseStart_6721612 := by decide
  rcases family_descends (prefixWord ++ tailWord_6721612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6721629 : List Nat := [1, 4, 4, 1, 1, 1, 1, 1, 4, 1, 4]
def baseStart_6721629 : Nat := 118140960795 + 6721629 * 2 ^ 59
def prefixEnd_6721629 : Nat := 4983230072969 + 3 ^ 40 * 6721629 * 2
def baseEnd_6721629 : Nat := 3451426458199987329325297

theorem tailTrace_6721629 : CollatzResearch.WordTrace tailWord_6721629 prefixEnd_6721629 3451426458199987329325297 := by
  unfold tailWord_6721629
  simp only [CollatzResearch.WordTrace]
  refine ⟨245157950165693570684319941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163438633443795713789546627 245157950165693570684319941)
  ·
    refine ⟨45967115656067544503309989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 245157950165693570684319941 45967115656067544503309989)
    ·
      refine ⟨8618834185512664594370623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45967115656067544503309989 8618834185512664594370623)
      ·
        refine ⟨12928251278268996891555935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8618834185512664594370623 12928251278268996891555935)
        ·
          refine ⟨19392376917403495337333903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12928251278268996891555935 19392376917403495337333903)
          ·
            refine ⟨29088565376105243006000855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19392376917403495337333903 29088565376105243006000855)
            ·
              refine ⟨43632848064157864509001283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29088565376105243006000855 43632848064157864509001283)
              ·
                refine ⟨65449272096236796763501925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43632848064157864509001283 65449272096236796763501925)
                ·
                  refine ⟨12271738518044399393156611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65449272096236796763501925 12271738518044399393156611)
                  ·
                    refine ⟨18407607777066599089734917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12271738518044399393156611 18407607777066599089734917)
                    ·
                      refine ⟨3451426458199987329325297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18407607777066599089734917 3451426458199987329325297)
                      ·
                        rfl

theorem cell23_6721629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_6721629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6721629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6721629 prefixEnd_6721629 := by exact prefixLift 6721629
  have htrace : WordTrace (prefixWord ++ tailWord_6721629) baseStart_6721629 baseEnd_6721629 := by
    simpa [prefixWord, tailWord_6721629, baseEnd_6721629] using wordTrace_append hprefix tailTrace_6721629
  have hstable : (prefixWord ++ tailWord_6721629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6721629).length < 2 ^ (prefixWord ++ tailWord_6721629).sum := by decide
  have hdescent : baseEnd_6721629 < baseStart_6721629 := by decide
  rcases family_descends (prefixWord ++ tailWord_6721629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6721630 : List Nat := [4, 4, 1, 1, 2, 1, 3, 2, 5]
def baseStart_6721630 : Nat := 118140960795 + 6721630 * 2 ^ 59
def prefixEnd_6721630 : Nat := 4983230072969 + 3 ^ 40 * 6721630 * 2
def baseEnd_6721630 : Nat := 383491885742293536156977

theorem tailTrace_6721630 : CollatzResearch.WordTrace tailWord_6721630 prefixEnd_6721630 383491885742293536156977 := by
  unfold tailWord_6721630
  simp only [CollatzResearch.WordTrace]
  refine ⟨30644748329836243481888293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 163438657759126631903404229 30644748329836243481888293)
  ·
    refine ⟨5745890311844295652854055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30644748329836243481888293 5745890311844295652854055)
    ·
      refine ⟨8618835467766443479281083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5745890311844295652854055 8618835467766443479281083)
      ·
        refine ⟨12928253201649665218921625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8618835467766443479281083 12928253201649665218921625)
        ·
          refine ⟨9696189901237248914191219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12928253201649665218921625 9696189901237248914191219)
          ·
            refine ⟨14544284851855873371286829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9696189901237248914191219 14544284851855873371286829)
            ·
              refine ⟨5454106819445952514232561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14544284851855873371286829 5454106819445952514232561)
              ·
                refine ⟨4090580114584464385674421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5454106819445952514232561 4090580114584464385674421)
                ·
                  refine ⟨383491885742293536156977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4090580114584464385674421 383491885742293536156977)
                  ·
                    rfl

theorem cell23_6721630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 3, 2, 5].length) (baseStart_6721630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6721630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6721630 prefixEnd_6721630 := by exact prefixLift 6721630
  have htrace : WordTrace (prefixWord ++ tailWord_6721630) baseStart_6721630 baseEnd_6721630 := by
    simpa [prefixWord, tailWord_6721630, baseEnd_6721630] using wordTrace_append hprefix tailTrace_6721630
  have hstable : (prefixWord ++ tailWord_6721630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6721630).length < 2 ^ (prefixWord ++ tailWord_6721630).sum := by decide
  have hdescent : baseEnd_6721630 < baseStart_6721630 := by decide
  rcases family_descends (prefixWord ++ tailWord_6721630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6721632 : List Nat := [2, 1, 1, 3, 2, 3, 1, 1, 4, 2, 3]
def baseStart_6721632 : Nat := 118140960795 + 6721632 * 2 ^ 59
def prefixEnd_6721632 : Nat := 4983230072969 + 3 ^ 40 * 6721632 * 2
def baseEnd_6721632 : Nat := 3451427998641950817587783

theorem tailTrace_6721632 : CollatzResearch.WordTrace tailWord_6721632 prefixEnd_6721632 3451427998641950817587783 := by
  unfold tailWord_6721632
  simp only [CollatzResearch.WordTrace]
  refine ⟨122579029792341351098339575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163438706389788468131119433 122579029792341351098339575)
  ·
    refine ⟨183868544688512026647509363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122579029792341351098339575 183868544688512026647509363)
    ·
      refine ⟨275802817032768039971264045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183868544688512026647509363 275802817032768039971264045)
      ·
        refine ⟨103426056387288014989224017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 275802817032768039971264045 103426056387288014989224017)
        ·
          refine ⟨77569542290466011241918013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103426056387288014989224017 77569542290466011241918013)
          ·
            refine ⟨29088578358924754215719255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77569542290466011241918013 29088578358924754215719255)
            ·
              refine ⟨43632867538387131323578883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29088578358924754215719255 43632867538387131323578883)
              ·
                refine ⟨65449301307580696985368325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43632867538387131323578883 65449301307580696985368325)
                ·
                  refine ⟨12271743995171380684756561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65449301307580696985368325 12271743995171380684756561)
                  ·
                    refine ⟨9203807996378535513567421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12271743995171380684756561 9203807996378535513567421)
                    ·
                      refine ⟨3451427998641950817587783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9203807996378535513567421 3451427998641950817587783)
                      ·
                        rfl

theorem cell23_6721632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 1, 4, 2, 3].length) (baseStart_6721632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6721632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6721632 prefixEnd_6721632 := by exact prefixLift 6721632
  have htrace : WordTrace (prefixWord ++ tailWord_6721632) baseStart_6721632 baseEnd_6721632 := by
    simpa [prefixWord, tailWord_6721632, baseEnd_6721632] using wordTrace_append hprefix tailTrace_6721632
  have hstable : (prefixWord ++ tailWord_6721632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6721632).length < 2 ^ (prefixWord ++ tailWord_6721632).sum := by decide
  have hdescent : baseEnd_6721632 < baseStart_6721632 := by decide
  rcases family_descends (prefixWord ++ tailWord_6721632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6721635 : List Nat := [1, 1, 1, 5, 1, 1, 4, 1, 8]
def baseStart_6721635 : Nat := 118140960795 + 6721635 * 2 ^ 59
def prefixEnd_6721635 : Nat := 4983230072969 + 3 ^ 40 * 6721635 * 2
def baseEnd_6721635 : Nat := 383492171009323811761141

theorem tailTrace_6721635 : CollatzResearch.WordTrace tailWord_6721635 prefixEnd_6721635 383492171009323811761141 := by
  unfold tailWord_6721635
  simp only [CollatzResearch.WordTrace]
  refine ⟨245158169003671833709038359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163438779335781222472692239 245158169003671833709038359)
  ·
    refine ⟨367737253505507750563557539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245158169003671833709038359 367737253505507750563557539)
    ·
      refine ⟨551605880258261625845336309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 367737253505507750563557539 551605880258261625845336309)
      ·
        refine ⟨51713051274212027423000279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 551605880258261625845336309 51713051274212027423000279)
        ·
          refine ⟨77569576911318041134500419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51713051274212027423000279 77569576911318041134500419)
          ·
            refine ⟨116354365366977061701750629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77569576911318041134500419 116354365366977061701750629)
            ·
              refine ⟨21816443506308199069078243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 116354365366977061701750629 21816443506308199069078243)
              ·
                refine ⟨32724665259462298603617365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21816443506308199069078243 32724665259462298603617365)
                ·
                  refine ⟨383492171009323811761141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32724665259462298603617365 383492171009323811761141)
                  ·
                    rfl

theorem cell23_6721635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 1, 8].length) (baseStart_6721635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6721635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6721635 prefixEnd_6721635 := by exact prefixLift 6721635
  have htrace : WordTrace (prefixWord ++ tailWord_6721635) baseStart_6721635 baseEnd_6721635 := by
    simpa [prefixWord, tailWord_6721635, baseEnd_6721635] using wordTrace_append hprefix tailTrace_6721635
  have hstable : (prefixWord ++ tailWord_6721635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6721635).length < 2 ^ (prefixWord ++ tailWord_6721635).sum := by decide
  have hdescent : baseEnd_6721635 < baseStart_6721635 := by decide
  rcases family_descends (prefixWord ++ tailWord_6721635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6721690 : List Nat := [3, 1, 1, 5, 2, 2, 2, 2, 1, 4]
def baseStart_6721690 : Nat := 118140960795 + 6721690 * 2 ^ 59
def prefixEnd_6721690 : Nat := 4983230072969 + 3 ^ 40 * 6721690 * 2
def baseEnd_6721690 : Nat := 1150485926839970530220839

theorem tailTrace_6721690 : CollatzResearch.WordTrace tailWord_6721690 prefixEnd_6721690 1150485926839970530220839 := by
  unfold tailWord_6721690
  simp only [CollatzResearch.WordTrace]
  refine ⟨61290043754618144525572631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163440116678981718734860349 61290043754618144525572631)
  ·
    refine ⟨91935065631927216788358947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61290043754618144525572631 91935065631927216788358947)
    ·
      refine ⟨137902598447890825182538421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91935065631927216788358947 137902598447890825182538421)
      ·
        refine ⟨12928368604489764860862977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 137902598447890825182538421 12928368604489764860862977)
        ·
          refine ⟨9696276453367323645647233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12928368604489764860862977 9696276453367323645647233)
          ·
            refine ⟨7272207340025492734235425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9696276453367323645647233 7272207340025492734235425)
            ·
              refine ⟨5454155505019119550676569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7272207340025492734235425 5454155505019119550676569)
              ·
                refine ⟨4090616628764339663007427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5454155505019119550676569 4090616628764339663007427)
                ·
                  refine ⟨6135924943146509494511141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4090616628764339663007427 6135924943146509494511141)
                  ·
                    refine ⟨1150485926839970530220839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6135924943146509494511141 1150485926839970530220839)
                    ·
                      rfl

theorem cell23_6721690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 2, 2, 1, 4].length) (baseStart_6721690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6721690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6721690 prefixEnd_6721690 := by exact prefixLift 6721690
  have htrace : WordTrace (prefixWord ++ tailWord_6721690) baseStart_6721690 baseEnd_6721690 := by
    simpa [prefixWord, tailWord_6721690, baseEnd_6721690] using wordTrace_append hprefix tailTrace_6721690
  have hstable : (prefixWord ++ tailWord_6721690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6721690).length < 2 ^ (prefixWord ++ tailWord_6721690).sum := by decide
  have hdescent : baseEnd_6721690 < baseStart_6721690 := by decide
  rcases family_descends (prefixWord ++ tailWord_6721690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6721739 : List Nat := [1, 1, 1, 1, 3, 2, 5, 3, 1, 2, 3]
def baseStart_6721739 : Nat := 118140960795 + 6721739 * 2 ^ 59
def prefixEnd_6721739 : Nat := 4983230072969 + 3 ^ 40 * 6721739 * 2
def baseEnd_6721739 : Nat := 3451482941071981898949791

theorem tailTrace_6721739 : CollatzResearch.WordTrace tailWord_6721739 prefixEnd_6721739 3451482941071981898949791 := by
  unfold tailWord_6721739
  simp only [CollatzResearch.WordTrace]
  refine ⟨245161962195295059470824271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163441308130196706313882847 245161962195295059470824271)
  ·
    refine ⟨367742943292942589206236407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245161962195295059470824271 367742943292942589206236407)
    ·
      refine ⟨551614414939413883809354611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 367742943292942589206236407 551614414939413883809354611)
      ·
        refine ⟨827421622409120825714031917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 551614414939413883809354611 827421622409120825714031917)
        ·
          refine ⟨310283108403420309642761969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 827421622409120825714031917 310283108403420309642761969)
          ·
            refine ⟨232712331302565232232071477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 310283108403420309642761969 232712331302565232232071477)
            ·
              refine ⟨21816781059615490521756701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 232712331302565232232071477 21816781059615490521756701)
              ·
                refine ⟨8181292897355808945658763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21816781059615490521756701 8181292897355808945658763)
                ·
                  refine ⟨12271939346033713418488145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8181292897355808945658763 12271939346033713418488145)
                  ·
                    refine ⟨9203954509525285063866109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12271939346033713418488145 9203954509525285063866109)
                    ·
                      refine ⟨3451482941071981898949791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9203954509525285063866109 3451482941071981898949791)
                      ·
                        rfl

theorem cell23_6721739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 3, 1, 2, 3].length) (baseStart_6721739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6721739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6721739 prefixEnd_6721739 := by exact prefixLift 6721739
  have htrace : WordTrace (prefixWord ++ tailWord_6721739) baseStart_6721739 baseEnd_6721739 := by
    simpa [prefixWord, tailWord_6721739, baseEnd_6721739] using wordTrace_append hprefix tailTrace_6721739
  have hstable : (prefixWord ++ tailWord_6721739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6721739).length < 2 ^ (prefixWord ++ tailWord_6721739).sum := by decide
  have hdescent : baseEnd_6721739 < baseStart_6721739 := by decide
  rcases family_descends (prefixWord ++ tailWord_6721739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6721742 : List Nat := [4, 1, 1, 1, 4, 2, 10]
def baseStart_6721742 : Nat := 118140960795 + 6721742 * 2 ^ 59
def prefixEnd_6721742 : Nat := 4983230072969 + 3 ^ 40 * 6721742 * 2
def baseEnd_6721742 : Nat := 42610919524863523298917

theorem tailTrace_6721742 : CollatzResearch.WordTrace tailWord_6721742 prefixEnd_6721742 42610919524863523298917 := by
  unfold tailWord_6721742
  simp only [CollatzResearch.WordTrace]
  refine ⟨30645258951785523872897935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 163441381076189460655455653 30645258951785523872897935)
  ·
    refine ⟨45967888427678285809346903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30645258951785523872897935 45967888427678285809346903)
    ·
      refine ⟨68951832641517428714020355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45967888427678285809346903 68951832641517428714020355)
      ·
        refine ⟨103427748962276143071030533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68951832641517428714020355 103427748962276143071030533)
        ·
          refine ⟨19392702930426776825818225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 103427748962276143071030533 19392702930426776825818225)
          ·
            refine ⟨14544527197820082619363669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19392702930426776825818225 14544527197820082619363669)
            ·
              refine ⟨42610919524863523298917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 14544527197820082619363669 42610919524863523298917)
              ·
                rfl

theorem cell23_6721742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 10].length) (baseStart_6721742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6721742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6721742 prefixEnd_6721742 := by exact prefixLift 6721742
  have htrace : WordTrace (prefixWord ++ tailWord_6721742) baseStart_6721742 baseEnd_6721742 := by
    simpa [prefixWord, tailWord_6721742, baseEnd_6721742] using wordTrace_append hprefix tailTrace_6721742
  have hstable : (prefixWord ++ tailWord_6721742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6721742).length < 2 ^ (prefixWord ++ tailWord_6721742).sum := by decide
  have hdescent : baseEnd_6721742 < baseStart_6721742 := by decide
  rcases family_descends (prefixWord ++ tailWord_6721742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6721746 : List Nat := [3, 2, 2, 2, 1, 2, 3, 2, 2, 4]
def baseStart_6721746 : Nat := 118140960795 + 6721746 * 2 ^ 59
def prefixEnd_6721746 : Nat := 4983230072969 + 3 ^ 40 * 6721746 * 2
def baseEnd_6721746 : Nat := 1150495511812187790520753

theorem tailTrace_6721746 : CollatzResearch.WordTrace tailWord_6721746 prefixEnd_6721746 1150495511812187790520753 := by
  unfold tailWord_6721746
  simp only [CollatzResearch.WordTrace]
  refine ⟨61290554376567424916582273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163441478337513133110886061 61290554376567424916582273)
  ·
    refine ⟨45967915782425568687436705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61290554376567424916582273 45967915782425568687436705)
    ·
      refine ⟨34475936836819176515577529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45967915782425568687436705 34475936836819176515577529)
      ·
        refine ⟨25856952627614382386683147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34475936836819176515577529 25856952627614382386683147)
        ·
          refine ⟨38785428941421573580024721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25856952627614382386683147 38785428941421573580024721)
          ·
            refine ⟨29089071706066180185018541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38785428941421573580024721 29089071706066180185018541)
            ·
              refine ⟨10908401889774817569381953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29089071706066180185018541 10908401889774817569381953)
              ·
                refine ⟨8181301417331113177036465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10908401889774817569381953 8181301417331113177036465)
                ·
                  refine ⟨6135976062998334882777349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8181301417331113177036465 6135976062998334882777349)
                  ·
                    refine ⟨1150495511812187790520753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6135976062998334882777349 1150495511812187790520753)
                    ·
                      rfl

theorem cell23_6721746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 3, 2, 2, 4].length) (baseStart_6721746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6721746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6721746 prefixEnd_6721746 := by exact prefixLift 6721746
  have htrace : WordTrace (prefixWord ++ tailWord_6721746) baseStart_6721746 baseEnd_6721746 := by
    simpa [prefixWord, tailWord_6721746, baseEnd_6721746] using wordTrace_append hprefix tailTrace_6721746
  have hstable : (prefixWord ++ tailWord_6721746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6721746).length < 2 ^ (prefixWord ++ tailWord_6721746).sum := by decide
  have hdescent : baseEnd_6721746 < baseStart_6721746 := by decide
  rcases family_descends (prefixWord ++ tailWord_6721746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6721753 : List Nat := [1, 2, 1, 2, 3, 1, 4, 4, 1, 2, 2]
def baseStart_6721753 : Nat := 118140960795 + 6721753 * 2 ^ 59
def prefixEnd_6721753 : Nat := 4983230072969 + 3 ^ 40 * 6721753 * 2
def baseEnd_6721753 : Nat := 3451490129801144844174727

theorem tailTrace_6721753 : CollatzResearch.WordTrace tailWord_6721753 prefixEnd_6721753 3451490129801144844174727 := by
  unfold tailWord_6721753
  simp only [CollatzResearch.WordTrace]
  refine ⟨245162472817244339861833913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163441648544829559907889275 245162472817244339861833913)
  ·
    refine ⟨183871854612933254896375435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245162472817244339861833913 183871854612933254896375435)
    ·
      refine ⟨275807781919399882344563153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183871854612933254896375435 275807781919399882344563153)
      ·
        refine ⟨206855836439549911758422365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 275807781919399882344563153 206855836439549911758422365)
        ·
          refine ⟨77570938664831216909408387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 206855836439549911758422365 77570938664831216909408387)
          ·
            refine ⟨116356407997246825364112581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77570938664831216909408387 116356407997246825364112581)
            ·
              refine ⟨21816826499483779755771109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 116356407997246825364112581 21816826499483779755771109)
              ·
                refine ⟨4090654968653208704207083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21816826499483779755771109 4090654968653208704207083)
                ·
                  refine ⟨6135982452979813056310625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4090654968653208704207083 6135982452979813056310625)
                  ·
                    refine ⟨4601986839734859792232969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6135982452979813056310625 4601986839734859792232969)
                    ·
                      refine ⟨3451490129801144844174727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4601986839734859792232969 3451490129801144844174727)
                      ·
                        rfl

theorem cell23_6721753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 4, 1, 2, 2].length) (baseStart_6721753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6721753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6721753 prefixEnd_6721753 := by exact prefixLift 6721753
  have htrace : WordTrace (prefixWord ++ tailWord_6721753) baseStart_6721753 baseEnd_6721753 := by
    simpa [prefixWord, tailWord_6721753, baseEnd_6721753] using wordTrace_append hprefix tailTrace_6721753
  have hstable : (prefixWord ++ tailWord_6721753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6721753).length < 2 ^ (prefixWord ++ tailWord_6721753).sum := by decide
  have hdescent : baseEnd_6721753 < baseStart_6721753 := by decide
  rcases family_descends (prefixWord ++ tailWord_6721753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6721763 : List Nat := [1, 1, 1, 8, 2, 1, 1, 1, 1, 6]
def baseStart_6721763 : Nat := 118140960795 + 6721763 * 2 ^ 59
def prefixEnd_6721763 : Nat := 4983230072969 + 3 ^ 40 * 6721763 * 2
def baseEnd_6721763 : Nat := 1150498421535896601683227

theorem tailTrace_6721763 : CollatzResearch.WordTrace tailWord_6721763 prefixEnd_6721763 1150498421535896601683227 := by
  unfold tailWord_6721763
  simp only [CollatzResearch.WordTrace]
  refine ⟨245162837547208111569697943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163441891698138741046465295 245162837547208111569697943)
  ·
    refine ⟨367744256320812167354546915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245162837547208111569697943 367744256320812167354546915)
    ·
      refine ⟨551616384481218251031820373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 367744256320812167354546915 551616384481218251031820373)
      ·
        refine ⟨6464254505639276379279145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 551616384481218251031820373 6464254505639276379279145)
        ·
          refine ⟨4848190879229457284459359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6464254505639276379279145 4848190879229457284459359)
          ·
            refine ⟨7272286318844185926689039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4848190879229457284459359 7272286318844185926689039)
            ·
              refine ⟨10908429478266278890033559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7272286318844185926689039 10908429478266278890033559)
              ·
                refine ⟨16362644217399418335050339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10908429478266278890033559 16362644217399418335050339)
                ·
                  refine ⟨24543966326099127502575509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16362644217399418335050339 24543966326099127502575509)
                  ·
                    refine ⟨1150498421535896601683227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24543966326099127502575509 1150498421535896601683227)
                    ·
                      rfl

theorem cell23_6721763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 1, 1, 1, 6].length) (baseStart_6721763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6721763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6721763 prefixEnd_6721763 := by exact prefixLift 6721763
  have htrace : WordTrace (prefixWord ++ tailWord_6721763) baseStart_6721763 baseEnd_6721763 := by
    simpa [prefixWord, tailWord_6721763, baseEnd_6721763] using wordTrace_append hprefix tailTrace_6721763
  have hstable : (prefixWord ++ tailWord_6721763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6721763).length < 2 ^ (prefixWord ++ tailWord_6721763).sum := by decide
  have hdescent : baseEnd_6721763 < baseStart_6721763 := by decide
  rcases family_descends (prefixWord ++ tailWord_6721763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6721773 : List Nat := [1, 5, 1, 2, 3, 1, 2, 2, 1, 2, 3]
def baseStart_6721773 : Nat := 118140960795 + 6721773 * 2 ^ 59
def prefixEnd_6721773 : Nat := 4983230072969 + 3 ^ 40 * 6721773 * 2
def baseEnd_6721773 : Nat := 3451500399414234765924635

theorem tailTrace_6721773 : CollatzResearch.WordTrace tailWord_6721773 prefixEnd_6721773 3451500399414234765924635 := by
  unfold tailWord_6721773
  simp only [CollatzResearch.WordTrace]
  refine ⟨245163202277171883277561973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163442134851447922185041315 245163202277171883277561973)
  ·
    refine ⟨22984050213484864057271435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 245163202277171883277561973 22984050213484864057271435)
    ·
      refine ⟨34476075320227296085907153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22984050213484864057271435 34476075320227296085907153)
      ·
        refine ⟨25857056490170472064430365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34476075320227296085907153 25857056490170472064430365)
        ·
          refine ⟨9696396183813927024161387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25857056490170472064430365 9696396183813927024161387)
          ·
            refine ⟨14544594275720890536242081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9696396183813927024161387 14544594275720890536242081)
            ·
              refine ⟨10908445706790667902181561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14544594275720890536242081 10908445706790667902181561)
              ·
                refine ⟨8181334280093000926636171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10908445706790667902181561 8181334280093000926636171)
                ·
                  refine ⟨12272001420139501389954257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8181334280093000926636171 12272001420139501389954257)
                  ·
                    refine ⟨9204001065104626042465693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12272001420139501389954257 9204001065104626042465693)
                    ·
                      refine ⟨3451500399414234765924635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9204001065104626042465693 3451500399414234765924635)
                      ·
                        rfl

theorem cell23_6721773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 2, 2, 1, 2, 3].length) (baseStart_6721773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6721773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6721773 prefixEnd_6721773 := by exact prefixLift 6721773
  have htrace : WordTrace (prefixWord ++ tailWord_6721773) baseStart_6721773 baseEnd_6721773 := by
    simpa [prefixWord, tailWord_6721773, baseEnd_6721773] using wordTrace_append hprefix tailTrace_6721773
  have hstable : (prefixWord ++ tailWord_6721773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6721773).length < 2 ^ (prefixWord ++ tailWord_6721773).sum := by decide
  have hdescent : baseEnd_6721773 < baseStart_6721773 := by decide
  rcases family_descends (prefixWord ++ tailWord_6721773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6721802 : List Nat := [3, 1, 2, 2, 1, 1, 2, 1, 4, 6]
def baseStart_6721802 : Nat := 118140960795 + 6721802 * 2 ^ 59
def prefixEnd_6721802 : Nat := 4983230072969 + 3 ^ 40 * 6721802 * 2
def baseEnd_6721802 : Nat := 1150505096784405050820667

theorem tailTrace_6721802 : CollatzResearch.WordTrace tailWord_6721802 prefixEnd_6721802 1150505096784405050820667 := by
  unfold tailWord_6721802
  simp only [CollatzResearch.WordTrace]
  refine ⟨61291064998516705307591915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163442839996044547486911773 61291064998516705307591915)
  ·
    refine ⟨91936597497775057961387873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61291064998516705307591915 91936597497775057961387873)
    ·
      refine ⟨68952448123331293471040905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91936597497775057961387873 68952448123331293471040905)
      ·
        refine ⟨51714336092498470103280679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68952448123331293471040905 51714336092498470103280679)
        ·
          refine ⟨77571504138747705154921019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51714336092498470103280679 77571504138747705154921019)
          ·
            refine ⟨116357256208121557732381529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77571504138747705154921019 116357256208121557732381529)
            ·
              refine ⟨87267942156091168299286147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116357256208121557732381529 87267942156091168299286147)
              ·
                refine ⟨130901913234136752448929221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87267942156091168299286147 130901913234136752448929221)
                ·
                  refine ⟨24544108731400641084174229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 130901913234136752448929221 24544108731400641084174229)
                  ·
                    refine ⟨1150505096784405050820667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24544108731400641084174229 1150505096784405050820667)
                    ·
                      rfl

theorem cell23_6721802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 1, 4, 6].length) (baseStart_6721802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6721802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6721802 prefixEnd_6721802 := by exact prefixLift 6721802
  have htrace : WordTrace (prefixWord ++ tailWord_6721802) baseStart_6721802 baseEnd_6721802 := by
    simpa [prefixWord, tailWord_6721802, baseEnd_6721802] using wordTrace_append hprefix tailTrace_6721802
  have hstable : (prefixWord ++ tailWord_6721802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6721802).length < 2 ^ (prefixWord ++ tailWord_6721802).sum := by decide
  have hdescent : baseEnd_6721802 < baseStart_6721802 := by decide
  rcases family_descends (prefixWord ++ tailWord_6721802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6721876 : List Nat := [2, 4, 1, 1, 2, 3, 1, 1, 2, 3, 3]
def baseStart_6721876 : Nat := 118140960795 + 6721876 * 2 ^ 59
def prefixEnd_6721876 : Nat := 4983230072969 + 3 ^ 40 * 6721876 * 2
def baseEnd_6721876 : Nat := 3451553287921647862936661

theorem tailTrace_6721876 : CollatzResearch.WordTrace tailWord_6721876 prefixEnd_6721876 3451553287921647862936661 := by
  unfold tailWord_6721876
  simp only [CollatzResearch.WordTrace]
  refine ⟨122583479497899365934280741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163444639330532487912374321 122583479497899365934280741)
  ·
    refine ⟨22984402405856131112677639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 122583479497899365934280741 22984402405856131112677639)
    ·
      refine ⟨34476603608784196669016459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22984402405856131112677639 34476603608784196669016459)
      ·
        refine ⟨51714905413176295003524689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34476603608784196669016459 51714905413176295003524689)
        ·
          refine ⟨38786179059882221252643517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51714905413176295003524689 38786179059882221252643517)
          ·
            refine ⟨14544817147455832969741319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38786179059882221252643517 14544817147455832969741319)
            ·
              refine ⟨21817225721183749454611979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14544817147455832969741319 21817225721183749454611979)
              ·
                refine ⟨32725838581775624181917969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21817225721183749454611979 32725838581775624181917969)
                ·
                  refine ⟨24544378936331718136438477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32725838581775624181917969 24544378936331718136438477)
                  ·
                    refine ⟨9204142101124394301164429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24544378936331718136438477 9204142101124394301164429)
                    ·
                      refine ⟨3451553287921647862936661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9204142101124394301164429 3451553287921647862936661)
                      ·
                        rfl

theorem cell23_6721876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 1, 2, 3, 3].length) (baseStart_6721876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6721876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6721876 prefixEnd_6721876 := by exact prefixLift 6721876
  have htrace : WordTrace (prefixWord ++ tailWord_6721876) baseStart_6721876 baseEnd_6721876 := by
    simpa [prefixWord, tailWord_6721876, baseEnd_6721876] using wordTrace_append hprefix tailTrace_6721876
  have hstable : (prefixWord ++ tailWord_6721876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6721876).length < 2 ^ (prefixWord ++ tailWord_6721876).sum := by decide
  have hdescent : baseEnd_6721876 < baseStart_6721876 := by decide
  rcases family_descends (prefixWord ++ tailWord_6721876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6721896 : List Nat := [2, 1, 4, 2, 2, 1, 3, 1, 2, 5]
def baseStart_6721896 : Nat := 118140960795 + 6721896 * 2 ^ 59
def prefixEnd_6721896 : Nat := 4983230072969 + 3 ^ 40 * 6721896 * 2
def baseEnd_6721896 : Nat := 1150521185844912594895523

theorem tailTrace_6721896 : CollatzResearch.WordTrace tailWord_6721896 prefixEnd_6721896 1150521185844912594895523 := by
  unfold tailWord_6721896
  simp only [CollatzResearch.WordTrace]
  refine ⟨122583844227863137642144771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163445125637150850189526361 122583844227863137642144771)
  ·
    refine ⟨183875766341794706463217157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122583844227863137642144771 183875766341794706463217157)
    ·
      refine ⟨34476706189086507461853217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 183875766341794706463217157 34476706189086507461853217)
      ·
        refine ⟨25857529641814880596389913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34476706189086507461853217 25857529641814880596389913)
        ·
          refine ⟨19393147231361160447292435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25857529641814880596389913 19393147231361160447292435)
          ·
            refine ⟨29089720847041740670938653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19393147231361160447292435 29089720847041740670938653)
            ·
              refine ⟨10908645317640652751601995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29089720847041740670938653 10908645317640652751601995)
              ·
                refine ⟨16362967976460979127402993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10908645317640652751601995 16362967976460979127402993)
                ·
                  refine ⟨12272225982345734345552245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16362967976460979127402993 12272225982345734345552245)
                  ·
                    refine ⟨1150521185844912594895523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12272225982345734345552245 1150521185844912594895523)
                    ·
                      rfl

theorem cell23_6721896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 3, 1, 2, 5].length) (baseStart_6721896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6721896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6721896 prefixEnd_6721896 := by exact prefixLift 6721896
  have htrace : WordTrace (prefixWord ++ tailWord_6721896) baseStart_6721896 baseEnd_6721896 := by
    simpa [prefixWord, tailWord_6721896, baseEnd_6721896] using wordTrace_append hprefix tailTrace_6721896
  have hstable : (prefixWord ++ tailWord_6721896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6721896).length < 2 ^ (prefixWord ++ tailWord_6721896).sum := by decide
  have hdescent : baseEnd_6721896 < baseStart_6721896 := by decide
  rcases family_descends (prefixWord ++ tailWord_6721896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6721999 : List Nat := [1, 1, 2, 1, 1, 4, 1, 5, 1, 6]
def baseStart_6721999 : Nat := 118140960795 + 6721999 * 2 ^ 59
def prefixEnd_6721999 : Nat := 4983230072969 + 3 ^ 40 * 6721999 * 2
def baseEnd_6721999 : Nat := 1150538815347383627232865

theorem tailTrace_6721999 : CollatzResearch.WordTrace tailWord_6721999 prefixEnd_6721999 1150538815347383627232865 := by
  unfold tailWord_6721999
  simp only [CollatzResearch.WordTrace]
  refine ⟨245171445174353123875289051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163447630116235415916859367 245171445174353123875289051)
  ·
    refine ⟨367757167761529685812933577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245171445174353123875289051 367757167761529685812933577)
    ·
      refine ⟨275817875821147264359700183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 367757167761529685812933577 275817875821147264359700183)
      ·
        refine ⟨413726813731720896539550275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275817875821147264359700183 413726813731720896539550275)
        ·
          refine ⟨620590220597581344809325413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 413726813731720896539550275 620590220597581344809325413)
          ·
            refine ⟨116360666362046502151748515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 620590220597581344809325413 116360666362046502151748515)
            ·
              refine ⟨174540999543069753227622773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116360666362046502151748515 174540999543069753227622773)
              ·
                refine ⟨16363218707162789365089635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 174540999543069753227622773 16363218707162789365089635)
                ·
                  refine ⟨24544828060744184047634453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16363218707162789365089635 24544828060744184047634453)
                  ·
                    refine ⟨1150538815347383627232865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24544828060744184047634453 1150538815347383627232865)
                    ·
                      rfl

theorem cell23_6721999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 5, 1, 6].length) (baseStart_6721999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6721999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6721999 prefixEnd_6721999 := by exact prefixLift 6721999
  have htrace : WordTrace (prefixWord ++ tailWord_6721999) baseStart_6721999 baseEnd_6721999 := by
    simpa [prefixWord, tailWord_6721999, baseEnd_6721999] using wordTrace_append hprefix tailTrace_6721999
  have hstable : (prefixWord ++ tailWord_6721999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6721999).length < 2 ^ (prefixWord ++ tailWord_6721999).sum := by decide
  have hdescent : baseEnd_6721999 < baseStart_6721999 := by decide
  rcases family_descends (prefixWord ++ tailWord_6721999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6722033 : List Nat := [1, 2, 2, 2, 3, 1, 4, 2, 2, 4]
def baseStart_6722033 : Nat := 118140960795 + 6722033 * 2 ^ 59
def prefixEnd_6722033 : Nat := 4983230072969 + 3 ^ 40 * 6722033 * 2
def baseEnd_6722033 : Nat := 1150544634794801249557813

theorem tailTrace_6722033 : CollatzResearch.WordTrace tailWord_6722033 prefixEnd_6722033 1150544634794801249557813 := by
  unfold tailWord_6722033
  simp only [CollatzResearch.WordTrace]
  refine ⟨245172685256229947682026753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163448456837486631788017835 245172685256229947682026753)
  ·
    refine ⟨183879513942172460761520065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245172685256229947682026753 183879513942172460761520065)
    ·
      refine ⟨137909635456629345571140049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183879513942172460761520065 137909635456629345571140049)
      ·
        refine ⟨103432226592472009178355037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137909635456629345571140049 103432226592472009178355037)
        ·
          refine ⟨38787084972177003441883139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103432226592472009178355037 38787084972177003441883139)
          ·
            refine ⟨58180627458265505162824709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38787084972177003441883139 58180627458265505162824709)
            ·
              refine ⟨10908867648424782218029633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58180627458265505162824709 10908867648424782218029633)
              ·
                refine ⟨8181650736318586663522225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10908867648424782218029633 8181650736318586663522225)
                ·
                  refine ⟨6136238052238939997641669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8181650736318586663522225 6136238052238939997641669)
                  ·
                    refine ⟨1150544634794801249557813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6136238052238939997641669 1150544634794801249557813)
                    ·
                      rfl

theorem cell23_6722033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 4, 2, 2, 4].length) (baseStart_6722033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6722033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6722033 prefixEnd_6722033 := by exact prefixLift 6722033
  have htrace : WordTrace (prefixWord ++ tailWord_6722033) baseStart_6722033 baseEnd_6722033 := by
    simpa [prefixWord, tailWord_6722033, baseEnd_6722033] using wordTrace_append hprefix tailTrace_6722033
  have hstable : (prefixWord ++ tailWord_6722033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6722033).length < 2 ^ (prefixWord ++ tailWord_6722033).sum := by decide
  have hdescent : baseEnd_6722033 < baseStart_6722033 := by decide
  rcases family_descends (prefixWord ++ tailWord_6722033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6722050 : List Nat := [3, 4, 1, 2, 2, 1, 2, 1, 1, 6]
def baseStart_6722050 : Nat := 118140960795 + 6722050 * 2 ^ 59
def prefixEnd_6722050 : Nat := 4983230072969 + 3 ^ 40 * 6722050 * 2
def baseEnd_6722050 : Nat := 1150547544518510060720287

theorem tailTrace_6722050 : CollatzResearch.WordTrace tailWord_6722050 prefixEnd_6722050 1150547544518510060720287 := by
  unfold tailWord_6722050
  simp only [CollatzResearch.WordTrace]
  refine ⟨61293326324292089896348901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163448870198112239723597069 61293326324292089896348901)
  ·
    refine ⟨11492498685804766855565419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61293326324292089896348901 11492498685804766855565419)
    ·
      refine ⟨17238748028707150283348129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11492498685804766855565419 17238748028707150283348129)
      ·
        refine ⟨12929061021530362712511097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17238748028707150283348129 12929061021530362712511097)
        ·
          refine ⟨9696795766147772034383323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12929061021530362712511097 9696795766147772034383323)
          ·
            refine ⟨14545193649221658051574985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9696795766147772034383323 14545193649221658051574985)
            ·
              refine ⟨10908895236916243538681239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14545193649221658051574985 10908895236916243538681239)
              ·
                refine ⟨16363342855374365308021859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10908895236916243538681239 16363342855374365308021859)
                ·
                  refine ⟨24545014283061547962032789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16363342855374365308021859 24545014283061547962032789)
                  ·
                    refine ⟨1150547544518510060720287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24545014283061547962032789 1150547544518510060720287)
                    ·
                      rfl

theorem cell23_6722050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 2, 1, 1, 6].length) (baseStart_6722050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6722050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6722050 prefixEnd_6722050 := by exact prefixLift 6722050
  have htrace : WordTrace (prefixWord ++ tailWord_6722050) baseStart_6722050 baseEnd_6722050 := by
    simpa [prefixWord, tailWord_6722050, baseEnd_6722050] using wordTrace_append hprefix tailTrace_6722050
  have hstable : (prefixWord ++ tailWord_6722050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6722050).length < 2 ^ (prefixWord ++ tailWord_6722050).sum := by decide
  have hdescent : baseEnd_6722050 < baseStart_6722050 := by decide
  rcases family_descends (prefixWord ++ tailWord_6722050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6722077 : List Nat := [1, 4, 2, 2, 1, 4, 2, 1, 1, 2, 3]
def baseStart_6722077 : Nat := 118140960795 + 6722077 * 2 ^ 59
def prefixEnd_6722077 : Nat := 4983230072969 + 3 ^ 40 * 6722077 * 2
def baseEnd_6722077 : Nat := 3451656497533201576523237

theorem tailTrace_6722077 : CollatzResearch.WordTrace tailWord_6722077 prefixEnd_6722077 3451656497533201576523237 := by
  unfold tailWord_6722077
  simp only [CollatzResearch.WordTrace]
  refine ⟨245174290068070543196628485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163449526712047028797752323 245174290068070543196628485)
  ·
    refine ⟨45970179387763226849367841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 245174290068070543196628485 45970179387763226849367841)
    ·
      refine ⟨34477634540822420137025881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45970179387763226849367841 34477634540822420137025881)
      ·
        refine ⟨25858225905616815102769411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34477634540822420137025881 25858225905616815102769411)
        ·
          refine ⟨38787338858425222654154117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25858225905616815102769411 38787338858425222654154117)
          ·
            refine ⟨7272626035954729247653897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38787338858425222654154117 7272626035954729247653897)
            ·
              refine ⟨5454469526966046935740423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7272626035954729247653897 5454469526966046935740423)
              ·
                refine ⟨8181704290449070403610635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5454469526966046935740423 8181704290449070403610635)
                ·
                  refine ⟨12272556435673605605415953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8181704290449070403610635 12272556435673605605415953)
                  ·
                    refine ⟨9204417326755204204061965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12272556435673605605415953 9204417326755204204061965)
                    ·
                      refine ⟨3451656497533201576523237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9204417326755204204061965 3451656497533201576523237)
                      ·
                        rfl

theorem cell23_6722077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 2, 1, 1, 2, 3].length) (baseStart_6722077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6722077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6722077 prefixEnd_6722077 := by exact prefixLift 6722077
  have htrace : WordTrace (prefixWord ++ tailWord_6722077) baseStart_6722077 baseEnd_6722077 := by
    simpa [prefixWord, tailWord_6722077, baseEnd_6722077] using wordTrace_append hprefix tailTrace_6722077
  have hstable : (prefixWord ++ tailWord_6722077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6722077).length < 2 ^ (prefixWord ++ tailWord_6722077).sum := by decide
  have hdescent : baseEnd_6722077 < baseStart_6722077 := by decide
  rcases family_descends (prefixWord ++ tailWord_6722077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6722084 : List Nat := [2, 3, 1, 5, 2, 1, 1, 2, 2, 4]
def baseStart_6722084 : Nat := 118140960795 + 6722084 * 2 ^ 59
def prefixEnd_6722084 : Nat := 4983230072969 + 3 ^ 40 * 6722084 * 2
def baseEnd_6722084 : Nat := 1150553363965927683045235

theorem tailTrace_6722084 : CollatzResearch.WordTrace tailWord_6722084 prefixEnd_6722084 1150553363965927683045235 := by
  unfold tailWord_6722084
  simp only [CollatzResearch.WordTrace]
  refine ⟨122587272689522591696066653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163449696919363455594755537 122587272689522591696066653)
  ·
    refine ⟨45970227258570971886024995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122587272689522591696066653 45970227258570971886024995)
    ·
      refine ⟨68955340887856457829037493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45970227258570971886024995 68955340887856457829037493)
      ·
        refine ⟨6464563208236542921472265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 68955340887856457829037493 6464563208236542921472265)
        ·
          refine ⟨4848422406177407191104199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6464563208236542921472265 4848422406177407191104199)
          ·
            refine ⟨7272633609266110786656299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4848422406177407191104199 7272633609266110786656299)
            ·
              refine ⟨10908950413899166179984449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7272633609266110786656299 10908950413899166179984449)
              ·
                refine ⟨8181712810424374634988337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10908950413899166179984449 8181712810424374634988337)
                ·
                  refine ⟨6136284607818280976241253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8181712810424374634988337 6136284607818280976241253)
                  ·
                    refine ⟨1150553363965927683045235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6136284607818280976241253 1150553363965927683045235)
                    ·
                      rfl

theorem cell23_6722084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 1, 2, 2, 4].length) (baseStart_6722084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6722084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6722084 prefixEnd_6722084 := by exact prefixLift 6722084
  have htrace : WordTrace (prefixWord ++ tailWord_6722084) baseStart_6722084 baseEnd_6722084 := by
    simpa [prefixWord, tailWord_6722084, baseEnd_6722084] using wordTrace_append hprefix tailTrace_6722084
  have hstable : (prefixWord ++ tailWord_6722084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6722084).length < 2 ^ (prefixWord ++ tailWord_6722084).sum := by decide
  have hdescent : baseEnd_6722084 < baseStart_6722084 := by decide
  rcases family_descends (prefixWord ++ tailWord_6722084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6722090 : List Nat := [3, 1, 4, 1, 1, 3, 1, 1, 4, 1, 3]
def baseStart_6722090 : Nat := 118140960795 + 6722090 * 2 ^ 59
def prefixEnd_6722090 : Nat := 4983230072969 + 3 ^ 40 * 6722090 * 2
def baseEnd_6722090 : Nat := 3451663172781710025660677

theorem tailTrace_6722090 : CollatzResearch.WordTrace tailWord_6722090 prefixEnd_6722090 3451663172781710025660677 := by
  unfold tailWord_6722090
  simp only [CollatzResearch.WordTrace]
  refine ⟨61293691054255861604212931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163449842811348964277901149 61293691054255861604212931)
  ·
    refine ⟨91940536581383792406319397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61293691054255861604212931 91940536581383792406319397)
    ·
      refine ⟨17238850609009461076184887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91940536581383792406319397 17238850609009461076184887)
      ·
        refine ⟨25858275913514191614277331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17238850609009461076184887 25858275913514191614277331)
        ·
          refine ⟨38787413870271287421415997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25858275913514191614277331 38787413870271287421415997)
          ·
            refine ⟨14545280201351732783030999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38787413870271287421415997 14545280201351732783030999)
            ·
              refine ⟨21817920302027599174546499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14545280201351732783030999 21817920302027599174546499)
              ·
                refine ⟨32726880453041398761819749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21817920302027599174546499 32726880453041398761819749)
                ·
                  refine ⟨6136290084945262267841203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32726880453041398761819749 6136290084945262267841203)
                  ·
                    refine ⟨9204435127417893401761805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6136290084945262267841203 9204435127417893401761805)
                    ·
                      refine ⟨3451663172781710025660677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9204435127417893401761805 3451663172781710025660677)
                      ·
                        rfl

theorem cell23_6722090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 1, 4, 1, 3].length) (baseStart_6722090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6722090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6722090 prefixEnd_6722090 := by exact prefixLift 6722090
  have htrace : WordTrace (prefixWord ++ tailWord_6722090) baseStart_6722090 baseEnd_6722090 := by
    simpa [prefixWord, tailWord_6722090, baseEnd_6722090] using wordTrace_append hprefix tailTrace_6722090
  have hstable : (prefixWord ++ tailWord_6722090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6722090).length < 2 ^ (prefixWord ++ tailWord_6722090).sum := by decide
  have hdescent : baseEnd_6722090 < baseStart_6722090 := by decide
  rcases family_descends (prefixWord ++ tailWord_6722090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6722106 : List Nat := [3, 1, 1, 1, 3, 3, 2, 1, 2, 6]
def baseStart_6722106 : Nat := 118140960795 + 6722106 * 2 ^ 59
def prefixEnd_6722106 : Nat := 4983230072969 + 3 ^ 40 * 6722106 * 2
def baseEnd_6722106 : Nat := 1150557129490727321020201

theorem tailTrace_6722106 : CollatzResearch.WordTrace tailWord_6722106 prefixEnd_6722106 1150557129490727321020201 := by
  unfold tailWord_6722106
  simp only [CollatzResearch.WordTrace]
  refine ⟨61293836946241370287358543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163450231856643654099622781 61293836946241370287358543)
  ·
    refine ⟨91940755419362055431037815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61293836946241370287358543 91940755419362055431037815)
    ·
      refine ⟨137911133129043083146556723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91940755419362055431037815 137911133129043083146556723)
      ·
        refine ⟨206866699693564624719835085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137911133129043083146556723 206866699693564624719835085)
        ·
          refine ⟨77575012385086734269938157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 206866699693564624719835085 77575012385086734269938157)
          ·
            refine ⟨29090629644407525351226809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77575012385086734269938157 29090629644407525351226809)
            ·
              refine ⟨21817972233305644013420107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29090629644407525351226809 21817972233305644013420107)
              ·
                refine ⟨32726958349958466020130161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21817972233305644013420107 32726958349958466020130161)
                ·
                  refine ⟨24545218762468849515097621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32726958349958466020130161 24545218762468849515097621)
                  ·
                    refine ⟨1150557129490727321020201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24545218762468849515097621 1150557129490727321020201)
                    ·
                      rfl

theorem cell23_6722106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 1, 2, 6].length) (baseStart_6722106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6722106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6722106 prefixEnd_6722106 := by exact prefixLift 6722106
  have htrace : WordTrace (prefixWord ++ tailWord_6722106) baseStart_6722106 baseEnd_6722106 := by
    simpa [prefixWord, tailWord_6722106, baseEnd_6722106] using wordTrace_append hprefix tailTrace_6722106
  have hstable : (prefixWord ++ tailWord_6722106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6722106).length < 2 ^ (prefixWord ++ tailWord_6722106).sum := by decide
  have hdescent : baseEnd_6722106 < baseStart_6722106 := by decide
  rcases family_descends (prefixWord ++ tailWord_6722106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6722126 : List Nat := [4, 1, 1, 1, 1, 2, 2, 2, 1, 4, 4]
def baseStart_6722126 : Nat := 118140960795 + 6722126 * 2 ^ 59
def prefixEnd_6722126 : Nat := 4983230072969 + 3 ^ 40 * 6722126 * 2
def baseEnd_6722126 : Nat := 3451681658085271884810511

theorem tailTrace_6722126 : CollatzResearch.WordTrace tailWord_6722126 prefixEnd_6722126 3451681658085271884810511 := by
  unfold tailWord_6722126
  simp only [CollatzResearch.WordTrace]
  refine ⟨30647009655611628070645279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 163450718163262016376774821 30647009655611628070645279)
  ·
    refine ⟨45970514483417442105967919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30647009655611628070645279 45970514483417442105967919)
    ·
      refine ⟨68955771725126163158951879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45970514483417442105967919 68955771725126163158951879)
      ·
        refine ⟨103433657587689244738427819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68955771725126163158951879 103433657587689244738427819)
        ·
          refine ⟨155150486381533867107641729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103433657587689244738427819 155150486381533867107641729)
          ·
            refine ⟨116362864786150400330731297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 155150486381533867107641729 116362864786150400330731297)
            ·
              refine ⟨87272148589612800248048473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116362864786150400330731297 87272148589612800248048473)
              ·
                refine ⟨65454111442209600186036355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87272148589612800248048473 65454111442209600186036355)
                ·
                  refine ⟨98181167163314400279054533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65454111442209600186036355 98181167163314400279054533)
                  ·
                    refine ⟨18408968843121450052322725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 98181167163314400279054533 18408968843121450052322725)
                    ·
                      refine ⟨3451681658085271884810511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18408968843121450052322725 3451681658085271884810511)
                      ·
                        rfl

theorem cell23_6722126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 2, 1, 4, 4].length) (baseStart_6722126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6722126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6722126 prefixEnd_6722126 := by exact prefixLift 6722126
  have htrace : WordTrace (prefixWord ++ tailWord_6722126) baseStart_6722126 baseEnd_6722126 := by
    simpa [prefixWord, tailWord_6722126, baseEnd_6722126] using wordTrace_append hprefix tailTrace_6722126
  have hstable : (prefixWord ++ tailWord_6722126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6722126).length < 2 ^ (prefixWord ++ tailWord_6722126).sum := by decide
  have hdescent : baseEnd_6722126 < baseStart_6722126 := by decide
  rcases family_descends (prefixWord ++ tailWord_6722126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6722130 : List Nat := [3, 2, 2, 1, 2, 1, 1, 1, 6, 2, 2]
def baseStart_6722130 : Nat := 118140960795 + 6722130 * 2 ^ 59
def prefixEnd_6722130 : Nat := 4983230072969 + 3 ^ 40 * 6722130 * 2
def baseEnd_6722130 : Nat := 3451683712007889869160493

theorem tailTrace_6722130 : CollatzResearch.WordTrace tailWord_6722130 prefixEnd_6722130 3451683712007889869160493 := by
  unfold tailWord_6722130
  simp only [CollatzResearch.WordTrace]
  refine ⟨61294055784219633312076961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163450815424585688832205229 61294055784219633312076961)
  ·
    refine ⟨45970541838164724984057721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61294055784219633312076961 45970541838164724984057721)
    ·
      refine ⟨34477906378623543738043291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45970541838164724984057721 34477906378623543738043291)
      ·
        refine ⟨51716859567935315607064937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34477906378623543738043291 51716859567935315607064937)
        ·
          refine ⟨38787644675951486705298703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51716859567935315607064937 38787644675951486705298703)
          ·
            refine ⟨58181467013927230057948055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38787644675951486705298703 58181467013927230057948055)
            ·
              refine ⟨87272200520890845086922083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58181467013927230057948055 87272200520890845086922083)
              ·
                refine ⟨130908300781336267630383125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87272200520890845086922083 130908300781336267630383125)
                ·
                  refine ⟨6136326599125137545174209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 130908300781336267630383125 6136326599125137545174209)
                  ·
                    refine ⟨4602244949343853158880657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6136326599125137545174209 4602244949343853158880657)
                    ·
                      refine ⟨3451683712007889869160493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4602244949343853158880657 3451683712007889869160493)
                      ·
                        rfl

theorem cell23_6722130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 1, 6, 2, 2].length) (baseStart_6722130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6722130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6722130 prefixEnd_6722130 := by exact prefixLift 6722130
  have htrace : WordTrace (prefixWord ++ tailWord_6722130) baseStart_6722130 baseEnd_6722130 := by
    simpa [prefixWord, tailWord_6722130, baseEnd_6722130] using wordTrace_append hprefix tailTrace_6722130
  have hstable : (prefixWord ++ tailWord_6722130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6722130).length < 2 ^ (prefixWord ++ tailWord_6722130).sum := by decide
  have hdescent : baseEnd_6722130 < baseStart_6722130 := by decide
  rcases family_descends (prefixWord ++ tailWord_6722130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6722183 : List Nat := [1, 1, 4, 2, 1, 2, 4, 1, 2, 5]
def baseStart_6722183 : Nat := 118140960795 + 6722183 * 2 ^ 59
def prefixEnd_6722183 : Nat := 4983230072969 + 3 ^ 40 * 6722183 * 2
def baseEnd_6722183 : Nat := 1150570308827526053932583

theorem tailTrace_6722183 : CollatzResearch.WordTrace tailWord_6722183 prefixEnd_6722183 1150570308827526053932583 := by
  unfold tailWord_6722183
  simp only [CollatzResearch.WordTrace]
  refine ⟨245178156205686523299987203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163452104137124348866658135 245178156205686523299987203)
  ·
    refine ⟨367767234308529784949980805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245178156205686523299987203 367767234308529784949980805)
    ·
      refine ⟨68956356432849334678121401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 367767234308529784949980805 68956356432849334678121401)
      ·
        refine ⟨51717267324637001008591051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68956356432849334678121401 51717267324637001008591051)
        ·
          refine ⟨77575900986955501512886577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51717267324637001008591051 77575900986955501512886577)
          ·
            refine ⟨58181925740216626134664933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77575900986955501512886577 58181925740216626134664933)
            ·
              refine ⟨10909111076290617400249675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58181925740216626134664933 10909111076290617400249675)
              ·
                refine ⟨16363666614435926100374513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10909111076290617400249675 16363666614435926100374513)
                ·
                  refine ⟨12272749960826944575280885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16363666614435926100374513 12272749960826944575280885)
                  ·
                    refine ⟨1150570308827526053932583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12272749960826944575280885 1150570308827526053932583)
                    ·
                      rfl

theorem cell23_6722183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 4, 1, 2, 5].length) (baseStart_6722183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6722183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6722183 prefixEnd_6722183 := by exact prefixLift 6722183
  have htrace : WordTrace (prefixWord ++ tailWord_6722183) baseStart_6722183 baseEnd_6722183 := by
    simpa [prefixWord, tailWord_6722183, baseEnd_6722183] using wordTrace_append hprefix tailTrace_6722183
  have hstable : (prefixWord ++ tailWord_6722183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6722183).length < 2 ^ (prefixWord ++ tailWord_6722183).sum := by decide
  have hdescent : baseEnd_6722183 < baseStart_6722183 := by decide
  rcases family_descends (prefixWord ++ tailWord_6722183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6722213 : List Nat := [1, 3, 1, 2, 1, 2, 1, 5, 3, 4]
def baseStart_6722213 : Nat := 118140960795 + 6722213 * 2 ^ 59
def prefixEnd_6722213 : Nat := 4983230072969 + 3 ^ 40 * 6722213 * 2
def baseEnd_6722213 : Nat := 1150575443634071014807537

theorem tailTrace_6722213 : CollatzResearch.WordTrace tailWord_6722213 prefixEnd_6722213 1150575443634071014807537 := by
  unfold tailWord_6722213
  simp only [CollatzResearch.WordTrace]
  refine ⟨245179250395577838423579293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163452833597051892282386195 245179250395577838423579293)
  ·
    refine ⟨91942218898341689408842235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 245179250395577838423579293 91942218898341689408842235)
    ·
      refine ⟨137913328347512534113263353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91942218898341689408842235 137913328347512534113263353)
      ·
        refine ⟨103434996260634400584947515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137913328347512534113263353 103434996260634400584947515)
        ·
          refine ⟨155152494390951600877421273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103434996260634400584947515 155152494390951600877421273)
          ·
            refine ⟨116364370793213700658065955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 155152494390951600877421273 116364370793213700658065955)
            ·
              refine ⟨174546556189820550987098933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116364370793213700658065955 174546556189820550987098933)
              ·
                refine ⟨16363739642795676655040525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 174546556189820550987098933 16363739642795676655040525)
                ·
                  refine ⟨6136402366048378745640197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16363739642795676655040525 6136402366048378745640197)
                  ·
                    refine ⟨1150575443634071014807537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6136402366048378745640197 1150575443634071014807537)
                    ·
                      rfl

theorem cell23_6722213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 5, 3, 4].length) (baseStart_6722213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6722213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6722213 prefixEnd_6722213 := by exact prefixLift 6722213
  have htrace : WordTrace (prefixWord ++ tailWord_6722213) baseStart_6722213 baseEnd_6722213 := by
    simpa [prefixWord, tailWord_6722213, baseEnd_6722213] using wordTrace_append hprefix tailTrace_6722213
  have hstable : (prefixWord ++ tailWord_6722213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6722213).length < 2 ^ (prefixWord ++ tailWord_6722213).sum := by decide
  have hdescent : baseEnd_6722213 < baseStart_6722213 := by decide
  rcases family_descends (prefixWord ++ tailWord_6722213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6722226 : List Nat := [3, 2, 1, 1, 1, 2, 1, 2, 10]
def baseStart_6722226 : Nat := 118140960795 + 6722226 * 2 ^ 59
def prefixEnd_6722226 : Nat := 4983230072969 + 3 ^ 40 * 6722226 * 2
def baseEnd_6722226 : Nat := 383525889572302388173339

theorem tailTrace_6722226 : CollatzResearch.WordTrace tailWord_6722226 prefixEnd_6722226 383525889572302388173339 := by
  unfold tailWord_6722226
  simp only [CollatzResearch.WordTrace]
  refine ⟨61294931136132685410950633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163453149696353827762535021 61294931136132685410950633)
  ·
    refine ⟨45971198352099514058212975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61294931136132685410950633 45971198352099514058212975)
    ·
      refine ⟨68956797528149271087319463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45971198352099514058212975 68956797528149271087319463)
      ·
        refine ⟨103435196292223906630979195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68956797528149271087319463 103435196292223906630979195)
        ·
          refine ⟨155152794438335859946468793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103435196292223906630979195 155152794438335859946468793)
          ·
            refine ⟨116364595828751894959851595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 155152794438335859946468793 116364595828751894959851595)
            ·
              refine ⟨174546893743127842439777393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116364595828751894959851595 174546893743127842439777393)
              ·
                refine ⟨130910170307345881829833045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 174546893743127842439777393 130910170307345881829833045)
                ·
                  refine ⟨383525889572302388173339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 130910170307345881829833045 383525889572302388173339)
                  ·
                    rfl

theorem cell23_6722226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 2, 10].length) (baseStart_6722226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6722226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6722226 prefixEnd_6722226 := by exact prefixLift 6722226
  have htrace : WordTrace (prefixWord ++ tailWord_6722226) baseStart_6722226 baseEnd_6722226 := by
    simpa [prefixWord, tailWord_6722226, baseEnd_6722226] using wordTrace_append hprefix tailTrace_6722226
  have hstable : (prefixWord ++ tailWord_6722226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6722226).length < 2 ^ (prefixWord ++ tailWord_6722226).sum := by decide
  have hdescent : baseEnd_6722226 < baseStart_6722226 := by decide
  rcases family_descends (prefixWord ++ tailWord_6722226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6722240 : List Nat := [2, 1, 1, 2, 4, 2, 3, 1, 2, 2, 3]
def baseStart_6722240 : Nat := 118140960795 + 6722240 * 2 ^ 59
def prefixEnd_6722240 : Nat := 4983230072969 + 3 ^ 40 * 6722240 * 2
def baseEnd_6722240 : Nat := 3451740194879884438784987

theorem tailTrace_6722240 : CollatzResearch.WordTrace tailWord_6722240 prefixEnd_6722240 3451740194879884438784987 := by
  unfold tailWord_6722240
  simp only [CollatzResearch.WordTrace]
  refine ⟨122590117583240011017406087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163453490110986681356541449 122590117583240011017406087)
  ·
    refine ⟨183885176374860016526109131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122590117583240011017406087 183885176374860016526109131)
    ·
      refine ⟨275827764562290024789163697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183885176374860016526109131 275827764562290024789163697)
      ·
        refine ⟨206870823421717518591872773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 275827764562290024789163697 206870823421717518591872773)
        ·
          refine ⟨38788279391572034735976145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 206870823421717518591872773 38788279391572034735976145)
          ·
            refine ⟨29091209543679026051982109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38788279391572034735976145 29091209543679026051982109)
            ·
              refine ⟨10909203578879634769493291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29091209543679026051982109 10909203578879634769493291)
              ·
                refine ⟨16363805368319452154239937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10909203578879634769493291 16363805368319452154239937)
                ·
                  refine ⟨12272854026239589115679953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16363805368319452154239937 12272854026239589115679953)
                  ·
                    refine ⟨9204640519679691836759965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12272854026239589115679953 9204640519679691836759965)
                    ·
                      refine ⟨3451740194879884438784987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9204640519679691836759965 3451740194879884438784987)
                      ·
                        rfl

theorem cell23_6722240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 3, 1, 2, 2, 3].length) (baseStart_6722240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6722240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6722240 prefixEnd_6722240 := by exact prefixLift 6722240
  have htrace : WordTrace (prefixWord ++ tailWord_6722240) baseStart_6722240 baseEnd_6722240 := by
    simpa [prefixWord, tailWord_6722240, baseEnd_6722240] using wordTrace_append hprefix tailTrace_6722240
  have hstable : (prefixWord ++ tailWord_6722240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6722240).length < 2 ^ (prefixWord ++ tailWord_6722240).sum := by decide
  have hdescent : baseEnd_6722240 < baseStart_6722240 := by decide
  rcases family_descends (prefixWord ++ tailWord_6722240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6722260 : List Nat := [2, 4, 1, 3, 2, 1, 1, 1, 8]
def baseStart_6722260 : Nat := 118140960795 + 6722260 * 2 ^ 59
def prefixEnd_6722260 : Nat := 4983230072969 + 3 ^ 40 * 6722260 * 2
def baseEnd_6722260 : Nat := 383527829388108262281655

theorem tailTrace_6722260 : CollatzResearch.WordTrace tailWord_6722260 prefixEnd_6722260 383527829388108262281655 := by
  unfold tailWord_6722260
  simp only [CollatzResearch.WordTrace]
  refine ⟨122590482313203782725270117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163453976417605043633693489 122590482313203782725270117)
  ·
    refine ⟨22985715433725709260988147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 122590482313203782725270117 22985715433725709260988147)
    ·
      refine ⟨34478573150588563891482221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22985715433725709260988147 34478573150588563891482221)
      ·
        refine ⟨12929464931470711459305833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34478573150588563891482221 12929464931470711459305833)
        ·
          refine ⟨9697098698603033594479375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12929464931470711459305833 9697098698603033594479375)
          ·
            refine ⟨14545648047904550391719063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9697098698603033594479375 14545648047904550391719063)
            ·
              refine ⟨21818472071856825587578595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14545648047904550391719063 21818472071856825587578595)
              ·
                refine ⟨32727708107785238381367893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21818472071856825587578595 32727708107785238381367893)
                ·
                  refine ⟨383527829388108262281655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32727708107785238381367893 383527829388108262281655)
                  ·
                    rfl

theorem cell23_6722260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 1, 8].length) (baseStart_6722260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6722260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6722260 prefixEnd_6722260 := by exact prefixLift 6722260
  have htrace : WordTrace (prefixWord ++ tailWord_6722260) baseStart_6722260 baseEnd_6722260 := by
    simpa [prefixWord, tailWord_6722260, baseEnd_6722260] using wordTrace_append hprefix tailTrace_6722260
  have hstable : (prefixWord ++ tailWord_6722260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6722260).length < 2 ^ (prefixWord ++ tailWord_6722260).sum := by decide
  have hdescent : baseEnd_6722260 < baseStart_6722260 := by decide
  rcases family_descends (prefixWord ++ tailWord_6722260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6722290 : List Nat := [3, 2, 1, 3, 1, 2, 1, 4, 1, 5]
def baseStart_6722290 : Nat := 118140960795 + 6722290 * 2 ^ 59
def prefixEnd_6722290 : Nat := 4983230072969 + 3 ^ 40 * 6722290 * 2
def baseEnd_6722290 : Nat := 1150588622970869747719919

theorem tailTrace_6722290 : CollatzResearch.WordTrace tailWord_6722290 prefixEnd_6722290 1150588622970869747719919 := by
  unfold tailWord_6722290
  simp only [CollatzResearch.WordTrace]
  refine ⟨61295514704074720143533081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163454705877532587049421549 61295514704074720143533081)
  ·
    refine ⟨45971636028056040107649811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61295514704074720143533081 45971636028056040107649811)
    ·
      refine ⟨68957454042084060161474717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45971636028056040107649811 68957454042084060161474717)
      ·
        refine ⟨25859045265781522560553019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68957454042084060161474717 25859045265781522560553019)
        ·
          refine ⟨38788567898672283840829529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25859045265781522560553019 38788567898672283840829529)
          ·
            refine ⟨29091425924004212880622147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38788567898672283840829529 29091425924004212880622147)
            ·
              refine ⟨43637138886006319320933221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29091425924004212880622147 43637138886006319320933221)
              ·
                refine ⟨8181963541126184872674979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43637138886006319320933221 8181963541126184872674979)
                ·
                  refine ⟨12272945311689277309012469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8181963541126184872674979 12272945311689277309012469)
                  ·
                    refine ⟨1150588622970869747719919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12272945311689277309012469 1150588622970869747719919)
                    ·
                      rfl

theorem cell23_6722290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 4, 1, 5].length) (baseStart_6722290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6722290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6722290 prefixEnd_6722290 := by exact prefixLift 6722290
  have htrace : WordTrace (prefixWord ++ tailWord_6722290) baseStart_6722290 baseEnd_6722290 := by
    simpa [prefixWord, tailWord_6722290, baseEnd_6722290] using wordTrace_append hprefix tailTrace_6722290
  have hstable : (prefixWord ++ tailWord_6722290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6722290).length < 2 ^ (prefixWord ++ tailWord_6722290).sum := by decide
  have hdescent : baseEnd_6722290 < baseStart_6722290 := by decide
  rcases family_descends (prefixWord ++ tailWord_6722290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6722313 : List Nat := [1, 2, 1, 1, 3, 2, 3, 3, 1, 1, 5]
def baseStart_6722313 : Nat := 118140960795 + 6722313 * 2 ^ 59
def prefixEnd_6722313 : Nat := 4983230072969 + 3 ^ 40 * 6722313 * 2
def baseEnd_6722313 : Nat := 3451777678967662653172151

theorem tailTrace_6722313 : CollatzResearch.WordTrace tailWord_6722313 prefixEnd_6722313 3451777678967662653172151 := by
  unfold tailWord_6722313
  simp only [CollatzResearch.WordTrace]
  refine ⟨245182897695215555502219593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163455265130143703668146395 245182897695215555502219593)
  ·
    refine ⟨183887173271411666626664695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245182897695215555502219593 183887173271411666626664695)
    ·
      refine ⟨275830759907117499939997043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183887173271411666626664695 275830759907117499939997043)
      ·
        refine ⟨413746139860676249909995565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275830759907117499939997043 413746139860676249909995565)
        ·
          refine ⟨155154802447753593716248337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 413746139860676249909995565 155154802447753593716248337)
          ·
            refine ⟨116366101835815195287186253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 155154802447753593716248337 116366101835815195287186253)
            ·
              refine ⟨43637288188430698232694845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 116366101835815195287186253 43637288188430698232694845)
              ·
                refine ⟨16363983070661511837260567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43637288188430698232694845 16363983070661511837260567)
                ·
                  refine ⟨24545974605992267755890851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16363983070661511837260567 24545974605992267755890851)
                  ·
                    refine ⟨36818961908988401633836277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24545974605992267755890851 36818961908988401633836277)
                    ·
                      refine ⟨3451777678967662653172151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36818961908988401633836277 3451777678967662653172151)
                      ·
                        rfl

theorem cell23_6722313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 3, 1, 1, 5].length) (baseStart_6722313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6722313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6722313 prefixEnd_6722313 := by exact prefixLift 6722313
  have htrace : WordTrace (prefixWord ++ tailWord_6722313) baseStart_6722313 baseEnd_6722313 := by
    simpa [prefixWord, tailWord_6722313, baseEnd_6722313] using wordTrace_append hprefix tailTrace_6722313
  have hstable : (prefixWord ++ tailWord_6722313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6722313).length < 2 ^ (prefixWord ++ tailWord_6722313).sum := by decide
  have hdescent : baseEnd_6722313 < baseStart_6722313 := by decide
  rcases family_descends (prefixWord ++ tailWord_6722313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6722330 : List Nat := [3, 1, 1, 3, 2, 1, 2, 2, 3, 2, 3]
def baseStart_6722330 : Nat := 118140960795 + 6722330 * 2 ^ 59
def prefixEnd_6722330 : Nat := 4983230072969 + 3 ^ 40 * 6722330 * 2
def baseEnd_6722330 : Nat := 3451786408138789086659573

theorem tailTrace_6722330 : CollatzResearch.WordTrace tailWord_6722330 prefixEnd_6722330 3451786408138789086659573 := by
  unfold tailWord_6722330
  simp only [CollatzResearch.WordTrace]
  refine ⟨61295879434038491851397111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163455678490769311603725629 61295879434038491851397111)
  ·
    refine ⟨91943819151057737777095667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61295879434038491851397111 91943819151057737777095667)
    ·
      refine ⟨137915728726586606665643501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91943819151057737777095667 137915728726586606665643501)
      ·
        refine ⟨51718398272469977499616313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137915728726586606665643501 51718398272469977499616313)
        ·
          refine ⟨38788798704352483124712235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51718398272469977499616313 38788798704352483124712235)
          ·
            refine ⟨58183198056528724687068353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38788798704352483124712235 58183198056528724687068353)
            ·
              refine ⟨43637398542396543515301265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58183198056528724687068353 43637398542396543515301265)
              ·
                refine ⟨32728048906797407636475949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43637398542396543515301265 32728048906797407636475949)
                ·
                  refine ⟨12273018340049027863678481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32728048906797407636475949 12273018340049027863678481)
                  ·
                    refine ⟨9204763755036770897758861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12273018340049027863678481 9204763755036770897758861)
                    ·
                      refine ⟨3451786408138789086659573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9204763755036770897758861 3451786408138789086659573)
                      ·
                        rfl

theorem cell23_6722330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 2, 3, 2, 3].length) (baseStart_6722330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6722330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6722330 prefixEnd_6722330 := by exact prefixLift 6722330
  have htrace : WordTrace (prefixWord ++ tailWord_6722330) baseStart_6722330 baseEnd_6722330 := by
    simpa [prefixWord, tailWord_6722330, baseEnd_6722330] using wordTrace_append hprefix tailTrace_6722330
  have hstable : (prefixWord ++ tailWord_6722330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6722330).length < 2 ^ (prefixWord ++ tailWord_6722330).sum := by decide
  have hdescent : baseEnd_6722330 < baseStart_6722330 := by decide
  rcases family_descends (prefixWord ++ tailWord_6722330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6722350 : List Nat := [4, 1, 3, 2, 1, 1, 2, 9]
def baseStart_6722350 : Nat := 118140960795 + 6722350 * 2 ^ 59
def prefixEnd_6722350 : Nat := 4983230072969 + 3 ^ 40 * 6722350 * 2
def baseEnd_6722350 : Nat := 127844321398217741052203

theorem tailTrace_6722350 : CollatzResearch.WordTrace tailWord_6722350 prefixEnd_6722350 127844321398217741052203 := by
  unfold tailWord_6722350
  simp only [CollatzResearch.WordTrace]
  refine ⟨30648030899510188852664563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 163456164797387673880877669 30648030899510188852664563)
  ·
    refine ⟨45972046349265283278996845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30648030899510188852664563 45972046349265283278996845)
    ·
      refine ⟨17239517380974481229623817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45972046349265283278996845 17239517380974481229623817)
      ·
        refine ⟨12929638035730860922217863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17239517380974481229623817 12929638035730860922217863)
        ·
          refine ⟨19394457053596291383326795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12929638035730860922217863 19394457053596291383326795)
          ·
            refine ⟨29091685580394437074990193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19394457053596291383326795 29091685580394437074990193)
            ·
              refine ⟨21818764185295827806242645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29091685580394437074990193 21818764185295827806242645)
              ·
                refine ⟨127844321398217741052203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 21818764185295827806242645 127844321398217741052203)
                ·
                  rfl

theorem cell23_6722350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 9].length) (baseStart_6722350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6722350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6722350 prefixEnd_6722350 := by exact prefixLift 6722350
  have htrace : WordTrace (prefixWord ++ tailWord_6722350) baseStart_6722350 baseEnd_6722350 := by
    simpa [prefixWord, tailWord_6722350, baseEnd_6722350] using wordTrace_append hprefix tailTrace_6722350
  have hstable : (prefixWord ++ tailWord_6722350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6722350).length < 2 ^ (prefixWord ++ tailWord_6722350).sum := by decide
  have hdescent : baseEnd_6722350 < baseStart_6722350 := by decide
  rcases family_descends (prefixWord ++ tailWord_6722350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6722360 : List Nat := [2, 1, 2, 1, 3, 2, 3, 2, 1, 3, 3]
def baseStart_6722360 : Nat := 118140960795 + 6722360 * 2 ^ 59
def prefixEnd_6722360 : Nat := 4983230072969 + 3 ^ 40 * 6722360 * 2
def baseEnd_6722360 : Nat := 3451801812558423969284435

theorem tailTrace_6722360 : CollatzResearch.WordTrace tailWord_6722360 prefixEnd_6722360 3451801812558423969284435 := by
  unfold tailWord_6722360
  simp only [CollatzResearch.WordTrace]
  refine ⟨122592305963022641264590267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163456407950696855019453689 122592305963022641264590267)
  ·
    refine ⟨183888458944533961896885401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122592305963022641264590267 183888458944533961896885401)
    ·
      refine ⟨137916344208400471422664051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183888458944533961896885401 137916344208400471422664051)
      ·
        refine ⟨206874516312600707133996077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137916344208400471422664051 206874516312600707133996077)
        ·
          refine ⟨77577943617225265175248529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 206874516312600707133996077 77577943617225265175248529)
          ·
            refine ⟨58183457712918948881436397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77577943617225265175248529 58183457712918948881436397)
            ·
              refine ⟨21818796642344605830538649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58183457712918948881436397 21818796642344605830538649)
              ·
                refine ⟨16364097481758454372903987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21818796642344605830538649 16364097481758454372903987)
                ·
                  refine ⟨24546146222637681559355981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16364097481758454372903987 24546146222637681559355981)
                  ·
                    refine ⟨9204804833489130584758493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24546146222637681559355981 9204804833489130584758493)
                    ·
                      refine ⟨3451801812558423969284435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9204804833489130584758493 3451801812558423969284435)
                      ·
                        rfl

theorem cell23_6722360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 2, 1, 3, 3].length) (baseStart_6722360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6722360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6722360 prefixEnd_6722360 := by exact prefixLift 6722360
  have htrace : WordTrace (prefixWord ++ tailWord_6722360) baseStart_6722360 baseEnd_6722360 := by
    simpa [prefixWord, tailWord_6722360, baseEnd_6722360] using wordTrace_append hprefix tailTrace_6722360
  have hstable : (prefixWord ++ tailWord_6722360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6722360).length < 2 ^ (prefixWord ++ tailWord_6722360).sum := by decide
  have hdescent : baseEnd_6722360 < baseStart_6722360 := by decide
  rcases family_descends (prefixWord ++ tailWord_6722360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6722372 : List Nat := [2, 3, 4, 2, 2, 1, 2, 2, 1, 1, 3]
def baseStart_6722372 : Nat := 118140960795 + 6722372 * 2 ^ 59
def prefixEnd_6722372 : Nat := 4983230072969 + 3 ^ 40 * 6722372 * 2
def baseEnd_6722372 : Nat := 3451807974326277922334381

theorem tailTrace_6722372 : CollatzResearch.WordTrace tailWord_6722372 prefixEnd_6722372 3451807974326277922334381 := by
  unfold tailWord_6722372
  simp only [CollatzResearch.WordTrace]
  refine ⟨122592524801000904289308685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163456699734667872385744913 122592524801000904289308685)
  ·
    refine ⟨45972196800375339108490757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122592524801000904289308685 45972196800375339108490757)
    ·
      refine ⟨8619786900070376082842017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45972196800375339108490757 8619786900070376082842017)
      ·
        refine ⟨6464840175052782062131513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8619786900070376082842017 6464840175052782062131513)
        ·
          refine ⟨4848630131289586546598635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6464840175052782062131513 4848630131289586546598635)
          ·
            refine ⟨7272945196934379819897953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4848630131289586546598635 7272945196934379819897953)
            ·
              refine ⟨5454708897700784864923465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7272945196934379819897953 5454708897700784864923465)
              ·
                refine ⟨4091031673275588648692599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5454708897700784864923465 4091031673275588648692599)
                ·
                  refine ⟨6136547509913382973038899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4091031673275588648692599 6136547509913382973038899)
                  ·
                    refine ⟨9204821264870074459558349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6136547509913382973038899 9204821264870074459558349)
                    ·
                      refine ⟨3451807974326277922334381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9204821264870074459558349 3451807974326277922334381)
                      ·
                        rfl

theorem cell23_6722372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 2, 2, 1, 1, 3].length) (baseStart_6722372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6722372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6722372 prefixEnd_6722372 := by exact prefixLift 6722372
  have htrace : WordTrace (prefixWord ++ tailWord_6722372) baseStart_6722372 baseEnd_6722372 := by
    simpa [prefixWord, tailWord_6722372, baseEnd_6722372] using wordTrace_append hprefix tailTrace_6722372
  have hstable : (prefixWord ++ tailWord_6722372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6722372).length < 2 ^ (prefixWord ++ tailWord_6722372).sum := by decide
  have hdescent : baseEnd_6722372 < baseStart_6722372 := by decide
  rcases family_descends (prefixWord ++ tailWord_6722372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6722377 : List Nat := [1, 2, 1, 1, 2, 5, 1, 4, 2, 1, 3]
def baseStart_6722377 : Nat := 118140960795 + 6722377 * 2 ^ 59
def prefixEnd_6722377 : Nat := 4983230072969 + 3 ^ 40 * 6722377 * 2
def baseEnd_6722377 : Nat := 3451810541729550402771857

theorem tailTrace_6722377 : CollatzResearch.WordTrace tailWord_6722377 prefixEnd_6722377 3451810541729550402771857 := by
  unfold tailWord_6722377
  simp only [CollatzResearch.WordTrace]
  refine ⟨245185231966983694432549385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163456821311322462955032923 245185231966983694432549385)
  ·
    refine ⟨183888923975237770824412039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245185231966983694432549385 183888923975237770824412039)
    ·
      refine ⟨275833385962856656236618059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183888923975237770824412039 275833385962856656236618059)
      ·
        refine ⟨413750078944284984354927089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275833385962856656236618059 413750078944284984354927089)
        ·
          refine ⟨310312559208213738266195317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 413750078944284984354927089 310312559208213738266195317)
          ·
            refine ⟨29091802425770037962455811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 310312559208213738266195317 29091802425770037962455811)
            ·
              refine ⟨43637703638655056943683717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29091802425770037962455811 43637703638655056943683717)
              ·
                refine ⟨8182069432247823176940697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43637703638655056943683717 8182069432247823176940697)
                ·
                  refine ⟨6136552074185867382705523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8182069432247823176940697 6136552074185867382705523)
                  ·
                    refine ⟨9204828111278801074058285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6136552074185867382705523 9204828111278801074058285)
                    ·
                      refine ⟨3451810541729550402771857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9204828111278801074058285 3451810541729550402771857)
                      ·
                        rfl

theorem cell23_6722377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 4, 2, 1, 3].length) (baseStart_6722377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6722377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6722377 prefixEnd_6722377 := by exact prefixLift 6722377
  have htrace : WordTrace (prefixWord ++ tailWord_6722377) baseStart_6722377 baseEnd_6722377 := by
    simpa [prefixWord, tailWord_6722377, baseEnd_6722377] using wordTrace_append hprefix tailTrace_6722377
  have hstable : (prefixWord ++ tailWord_6722377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6722377).length < 2 ^ (prefixWord ++ tailWord_6722377).sum := by decide
  have hdescent : baseEnd_6722377 < baseStart_6722377 := by decide
  rcases family_descends (prefixWord ++ tailWord_6722377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6722393 : List Nat := [1, 2, 1, 2, 2, 4, 1, 1, 1, 8]
def baseStart_6722393 : Nat := 118140960795 + 6722393 * 2 ^ 59
def prefixEnd_6722393 : Nat := 4983230072969 + 3 ^ 40 * 6722393 * 2
def baseEnd_6722393 : Nat := 1150606252473340780057261

theorem tailTrace_6722393 : CollatzResearch.WordTrace tailWord_6722393 prefixEnd_6722393 1150606252473340780057261 := by
  unfold tailWord_6722393
  simp only [CollatzResearch.WordTrace]
  refine ⟨245185815534925729165131833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163457210356617152776754555 245185815534925729165131833)
  ·
    refine ⟨183889361651194296873848875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245185815534925729165131833 183889361651194296873848875)
    ·
      refine ⟨275834042476791445310773313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183889361651194296873848875 275834042476791445310773313)
      ·
        refine ⟨206875531857593583983079985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 275834042476791445310773313 206875531857593583983079985)
        ·
          refine ⟨155156648893195187987309989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 206875531857593583983079985 155156648893195187987309989)
          ·
            refine ⟨29091871667474097747620623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 155156648893195187987309989 29091871667474097747620623)
            ·
              refine ⟨43637807501211146621430935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29091871667474097747620623 43637807501211146621430935)
              ·
                refine ⟨65456711251816719932146403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43637807501211146621430935 65456711251816719932146403)
                ·
                  refine ⟨98185066877725079898219605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65456711251816719932146403 98185066877725079898219605)
                  ·
                    refine ⟨1150606252473340780057261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 98185066877725079898219605 1150606252473340780057261)
                    ·
                      rfl

theorem cell23_6722393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 1, 1, 8].length) (baseStart_6722393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6722393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6722393 prefixEnd_6722393 := by exact prefixLift 6722393
  have htrace : WordTrace (prefixWord ++ tailWord_6722393) baseStart_6722393 baseEnd_6722393 := by
    simpa [prefixWord, tailWord_6722393, baseEnd_6722393] using wordTrace_append hprefix tailTrace_6722393
  have hstable : (prefixWord ++ tailWord_6722393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6722393).length < 2 ^ (prefixWord ++ tailWord_6722393).sum := by decide
  have hdescent : baseEnd_6722393 < baseStart_6722393 := by decide
  rcases family_descends (prefixWord ++ tailWord_6722393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6722417 : List Nat := [1, 2, 2, 2, 1, 4, 2, 2, 1, 4, 2]
def baseStart_6722417 : Nat := 118140960795 + 6722417 * 2 ^ 59
def prefixEnd_6722417 : Nat := 4983230072969 + 3 ^ 40 * 6722417 * 2
def baseEnd_6722417 : Nat := 3451831080955730246271673

theorem tailTrace_6722417 : CollatzResearch.WordTrace tailWord_6722417 prefixEnd_6722417 3451831080955730246271673 := by
  unfold tailWord_6722417
  simp only [CollatzResearch.WordTrace]
  refine ⟨245186690886838781264005505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163457793924559187509337003 245186690886838781264005505)
  ·
    refine ⟨183890018165129085948004129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245186690886838781264005505 183890018165129085948004129)
    ·
      refine ⟨137917513623846814461003097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183890018165129085948004129 137917513623846814461003097)
      ·
        refine ⟨103438135217885110845752323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137917513623846814461003097 103438135217885110845752323)
        ·
          refine ⟨155157202826827666268628485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103438135217885110845752323 155157202826827666268628485)
          ·
            refine ⟨29091975530030187425367841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 155157202826827666268628485 29091975530030187425367841)
            ·
              refine ⟨21818981647522640569025881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29091975530030187425367841 21818981647522640569025881)
              ·
                refine ⟨16364236235641980426769411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21818981647522640569025881 16364236235641980426769411)
                ·
                  refine ⟨24546354353462970640154117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16364236235641980426769411 24546354353462970640154117)
                  ·
                    refine ⟨4602441441274306995028897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24546354353462970640154117 4602441441274306995028897)
                    ·
                      refine ⟨3451831080955730246271673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4602441441274306995028897 3451831080955730246271673)
                      ·
                        rfl

theorem cell23_6722417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 2, 1, 4, 2].length) (baseStart_6722417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6722417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6722417 prefixEnd_6722417 := by exact prefixLift 6722417
  have htrace : WordTrace (prefixWord ++ tailWord_6722417) baseStart_6722417 baseEnd_6722417 := by
    simpa [prefixWord, tailWord_6722417, baseEnd_6722417] using wordTrace_append hprefix tailTrace_6722417
  have hstable : (prefixWord ++ tailWord_6722417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6722417).length < 2 ^ (prefixWord ++ tailWord_6722417).sum := by decide
  have hdescent : baseEnd_6722417 < baseStart_6722417 := by decide
  rcases family_descends (prefixWord ++ tailWord_6722417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6722421 : List Nat := [1, 3, 4, 1, 1, 2, 4, 1, 1, 3, 2]
def baseStart_6722421 : Nat := 118140960795 + 6722421 * 2 ^ 59
def prefixEnd_6722421 : Nat := 4983230072969 + 3 ^ 40 * 6722421 * 2
def baseEnd_6722421 : Nat := 3451833134878348230621655

theorem tailTrace_6722421 : CollatzResearch.WordTrace tailWord_6722421 prefixEnd_6722421 3451833134878348230621655 := by
  unfold tailWord_6722421
  simp only [CollatzResearch.WordTrace]
  refine ⟨245186836778824289947151117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163457891185882859964767411 245186836778824289947151117)
  ·
    refine ⟨91945063792059108730181669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 245186836778824289947151117 91945063792059108730181669)
    ·
      refine ⟨17239699461011082886909063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91945063792059108730181669 17239699461011082886909063)
      ·
        refine ⟨25859549191516624330363595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17239699461011082886909063 25859549191516624330363595)
        ·
          refine ⟨38789323787274936495545393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25859549191516624330363595 38789323787274936495545393)
          ·
            refine ⟨29091992840456202371659045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38789323787274936495545393 29091992840456202371659045)
            ·
              refine ⟨5454748657585537944686071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29091992840456202371659045 5454748657585537944686071)
              ·
                refine ⟨8182122986378306917029107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5454748657585537944686071 8182122986378306917029107)
                ·
                  refine ⟨12273184479567460375543661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8182122986378306917029107 12273184479567460375543661)
                  ·
                    refine ⟨4602444179837797640828873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12273184479567460375543661 4602444179837797640828873)
                    ·
                      refine ⟨3451833134878348230621655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4602444179837797640828873 3451833134878348230621655)
                      ·
                        rfl

theorem cell23_6722421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 4, 1, 1, 3, 2].length) (baseStart_6722421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6722421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6722421 prefixEnd_6722421 := by exact prefixLift 6722421
  have htrace : WordTrace (prefixWord ++ tailWord_6722421) baseStart_6722421 baseEnd_6722421 := by
    simpa [prefixWord, tailWord_6722421, baseEnd_6722421] using wordTrace_append hprefix tailTrace_6722421
  have hstable : (prefixWord ++ tailWord_6722421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6722421).length < 2 ^ (prefixWord ++ tailWord_6722421).sum := by decide
  have hdescent : baseEnd_6722421 < baseStart_6722421 := by decide
  rcases family_descends (prefixWord ++ tailWord_6722421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6722440 : List Nat := [2, 1, 3, 3, 2, 1, 1, 3, 7]
def baseStart_6722440 : Nat := 118140960795 + 6722440 * 2 ^ 59
def prefixEnd_6722440 : Nat := 4983230072969 + 3 ^ 40 * 6722440 * 2
def baseEnd_6722440 : Nat := 383538099001198184031563

theorem tailTrace_6722440 : CollatzResearch.WordTrace tailWord_6722440 prefixEnd_6722440 383538099001198184031563 := by
  unfold tailWord_6722440
  simp only [CollatzResearch.WordTrace]
  refine ⟨122593764882877728096046387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163458353177170304128061849 122593764882877728096046387)
  ·
    refine ⟨183890647324316592144069581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122593764882877728096046387 183890647324316592144069581)
    ·
      refine ⟨68958992746618722054026093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 183890647324316592144069581 68958992746618722054026093)
      ·
        refine ⟨25859622279982020770259785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68958992746618722054026093 25859622279982020770259785)
        ·
          refine ⟨19394716709986515577694839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25859622279982020770259785 19394716709986515577694839)
          ·
            refine ⟨29092075064979773366542259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19394716709986515577694839 29092075064979773366542259)
            ·
              refine ⟨43638112597469660049813389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29092075064979773366542259 43638112597469660049813389)
              ·
                refine ⟨16364292224051122518680021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43638112597469660049813389 16364292224051122518680021)
                ·
                  refine ⟨383538099001198184031563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16364292224051122518680021 383538099001198184031563)
                  ·
                    rfl

theorem cell23_6722440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 3, 7].length) (baseStart_6722440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6722440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6722440 prefixEnd_6722440 := by exact prefixLift 6722440
  have htrace : WordTrace (prefixWord ++ tailWord_6722440) baseStart_6722440 baseEnd_6722440 := by
    simpa [prefixWord, tailWord_6722440, baseEnd_6722440] using wordTrace_append hprefix tailTrace_6722440
  have hstable : (prefixWord ++ tailWord_6722440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6722440).length < 2 ^ (prefixWord ++ tailWord_6722440).sum := by decide
  have hdescent : baseEnd_6722440 < baseStart_6722440 := by decide
  rcases family_descends (prefixWord ++ tailWord_6722440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6722574 : List Nat := [4, 1, 1, 2, 2, 2, 1, 1, 5, 1, 3]
def baseStart_6722574 : Nat := 118140960795 + 6722574 * 2 ^ 59
def prefixEnd_6722574 : Nat := 4983230072969 + 3 ^ 40 * 6722574 * 2
def baseEnd_6722574 : Nat := 3451911697418486132008451

theorem tailTrace_6722574 : CollatzResearch.WordTrace tailWord_6722574 prefixEnd_6722574 3451911697418486132008451 := by
  unfold tailWord_6722574
  simp only [CollatzResearch.WordTrace]
  refine ⟨30649052143408749634683847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 163461611431513331384980517 30649052143408749634683847)
  ·
    refine ⟨45973578215113124452025771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30649052143408749634683847 45973578215113124452025771)
    ·
      refine ⟨68960367322669686678038657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45973578215113124452025771 68960367322669686678038657)
      ·
        refine ⟨51720275492002265008528993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68960367322669686678038657 51720275492002265008528993)
        ·
          refine ⟨38790206619001698756396745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51720275492002265008528993 38790206619001698756396745)
          ·
            refine ⟨29092654964251274067297559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38790206619001698756396745 29092654964251274067297559)
            ·
              refine ⟨43638982446376911100946339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29092654964251274067297559 43638982446376911100946339)
              ·
                refine ⟨65458473669565366651419509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43638982446376911100946339 65458473669565366651419509)
                ·
                  refine ⟨6136731906521753123570579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 65458473669565366651419509 6136731906521753123570579)
                  ·
                    refine ⟨9205097859782629685355869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6136731906521753123570579 9205097859782629685355869)
                    ·
                      refine ⟨3451911697418486132008451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9205097859782629685355869 3451911697418486132008451)
                      ·
                        rfl

theorem cell23_6722574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 1, 5, 1, 3].length) (baseStart_6722574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6722574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6722574 prefixEnd_6722574 := by exact prefixLift 6722574
  have htrace : WordTrace (prefixWord ++ tailWord_6722574) baseStart_6722574 baseEnd_6722574 := by
    simpa [prefixWord, tailWord_6722574, baseEnd_6722574] using wordTrace_append hprefix tailTrace_6722574
  have hstable : (prefixWord ++ tailWord_6722574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6722574).length < 2 ^ (prefixWord ++ tailWord_6722574).sum := by decide
  have hdescent : baseEnd_6722574 < baseStart_6722574 := by decide
  rcases family_descends (prefixWord ++ tailWord_6722574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6722578 : List Nat := [3, 2, 5, 1, 1, 1, 1, 1, 1, 4, 3]
def baseStart_6722578 : Nat := 118140960795 + 6722578 * 2 ^ 59
def prefixEnd_6722578 : Nat := 4983230072969 + 3 ^ 40 * 6722578 * 2
def baseEnd_6722578 : Nat := 3451913751341104116358433

theorem tailTrace_6722578 : CollatzResearch.WordTrace tailWord_6722578 prefixEnd_6722578 3451913751341104116358433 := by
  unfold tailWord_6722578
  simp only [CollatzResearch.WordTrace]
  refine ⟨61298140759813876440154097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163461708692837003840410925 61298140759813876440154097)
  ·
    refine ⟨45973605569860407330115573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61298140759813876440154097 45973605569860407330115573)
    ·
      refine ⟨4310025522174413187198335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 45973605569860407330115573 4310025522174413187198335)
      ·
        refine ⟨6465038283261619780797503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4310025522174413187198335 6465038283261619780797503)
        ·
          refine ⟨9697557424892429671196255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6465038283261619780797503 9697557424892429671196255)
          ·
            refine ⟨14546336137338644506794383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9697557424892429671196255 14546336137338644506794383)
            ·
              refine ⟨21819504206007966760191575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14546336137338644506794383 21819504206007966760191575)
              ·
                refine ⟨32729256309011950140287363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21819504206007966760191575 32729256309011950140287363)
                ·
                  refine ⟨49093884463517925210431045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32729256309011950140287363 49093884463517925210431045)
                  ·
                    refine ⟨9205103336909610976955821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 49093884463517925210431045 9205103336909610976955821)
                    ·
                      refine ⟨3451913751341104116358433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9205103336909610976955821 3451913751341104116358433)
                      ·
                        rfl

theorem cell23_6722578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_6722578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6722578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6722578 prefixEnd_6722578 := by exact prefixLift 6722578
  have htrace : WordTrace (prefixWord ++ tailWord_6722578) baseStart_6722578 baseEnd_6722578 := by
    simpa [prefixWord, tailWord_6722578, baseEnd_6722578] using wordTrace_append hprefix tailTrace_6722578
  have hstable : (prefixWord ++ tailWord_6722578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6722578).length < 2 ^ (prefixWord ++ tailWord_6722578).sum := by decide
  have hdescent : baseEnd_6722578 < baseStart_6722578 := by decide
  rcases family_descends (prefixWord ++ tailWord_6722578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6722584 : List Nat := [2, 1, 2, 3, 2, 3, 1, 1, 1, 5, 2]
def baseStart_6722584 : Nat := 118140960795 + 6722584 * 2 ^ 59
def prefixEnd_6722584 : Nat := 4983230072969 + 3 ^ 40 * 6722584 * 2
def baseEnd_6722584 : Nat := 3451916832225031092883405

theorem tailTrace_6722584 : CollatzResearch.WordTrace tailWord_6722584 prefixEnd_6722584 3451916832225031092883405 := by
  unfold tailWord_6722584
  simp only [CollatzResearch.WordTrace]
  refine ⟨122596390938616884392667403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163461854584822512523556537 122596390938616884392667403)
  ·
    refine ⟨183894586407925326589001105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122596390938616884392667403 183894586407925326589001105)
    ·
      refine ⟨137920939805943994941750829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183894586407925326589001105 137920939805943994941750829)
      ·
        refine ⟨51720352427228998103156561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137920939805943994941750829 51720352427228998103156561)
        ·
          refine ⟨38790264320421748577367421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51720352427228998103156561 38790264320421748577367421)
          ·
            refine ⟨14546349120158155716512783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38790264320421748577367421 14546349120158155716512783)
            ·
              refine ⟨21819523680237233574769175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14546349120158155716512783 21819523680237233574769175)
              ·
                refine ⟨32729285520355850362153763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21819523680237233574769175 32729285520355850362153763)
                ·
                  refine ⟨49093928280533775543230645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32729285520355850362153763 49093928280533775543230645)
                  ·
                    refine ⟨4602555776300041457177873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49093928280533775543230645 4602555776300041457177873)
                    ·
                      refine ⟨3451916832225031092883405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4602555776300041457177873 3451916832225031092883405)
                      ·
                        rfl

theorem cell23_6722584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 1, 1, 5, 2].length) (baseStart_6722584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6722584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6722584 prefixEnd_6722584 := by exact prefixLift 6722584
  have htrace : WordTrace (prefixWord ++ tailWord_6722584) baseStart_6722584 baseEnd_6722584 := by
    simpa [prefixWord, tailWord_6722584, baseEnd_6722584] using wordTrace_append hprefix tailTrace_6722584
  have hstable : (prefixWord ++ tailWord_6722584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6722584).length < 2 ^ (prefixWord ++ tailWord_6722584).sum := by decide
  have hdescent : baseEnd_6722584 < baseStart_6722584 := by decide
  rcases family_descends (prefixWord ++ tailWord_6722584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6722591 : List Nat := [1, 1, 2, 4, 1, 3, 1, 5, 1, 1, 3]
def baseStart_6722591 : Nat := 118140960795 + 6722591 * 2 ^ 59
def prefixEnd_6722591 : Nat := 4983230072969 + 3 ^ 40 * 6722591 * 2
def baseEnd_6722591 : Nat := 3451920426589612565495873

theorem tailTrace_6722591 : CollatzResearch.WordTrace tailWord_6722591 prefixEnd_6722591 3451920426589612565495873 := by
  unfold tailWord_6722591
  simp only [CollatzResearch.WordTrace]
  refine ⟨245193037188208408980839627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163462024792138939320559751 245193037188208408980839627)
  ·
    refine ⟨367789555782312613471259441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245193037188208408980839627 367789555782312613471259441)
    ·
      refine ⟨275842166836734460103444581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 367789555782312613471259441 275842166836734460103444581)
      ·
        refine ⟨51720406281887711269395859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 275842166836734460103444581 51720406281887711269395859)
        ·
          refine ⟨77580609422831566904093789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51720406281887711269395859 77580609422831566904093789)
          ·
            refine ⟨29092728533561837589035171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77580609422831566904093789 29092728533561837589035171)
            ·
              refine ⟨43639092800342756383552757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29092728533561837589035171 43639092800342756383552757)
              ·
                refine ⟨4091164950032133410958071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43639092800342756383552757 4091164950032133410958071)
                ·
                  refine ⟨6136747425048200116437107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4091164950032133410958071 6136747425048200116437107)
                  ·
                    refine ⟨9205121137572300174655661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6136747425048200116437107 9205121137572300174655661)
                    ·
                      refine ⟨3451920426589612565495873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9205121137572300174655661 3451920426589612565495873)
                      ·
                        rfl

theorem cell23_6722591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 5, 1, 1, 3].length) (baseStart_6722591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6722591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6722591 prefixEnd_6722591 := by exact prefixLift 6722591
  have htrace : WordTrace (prefixWord ++ tailWord_6722591) baseStart_6722591 baseEnd_6722591 := by
    simpa [prefixWord, tailWord_6722591, baseEnd_6722591] using wordTrace_append hprefix tailTrace_6722591
  have hstable : (prefixWord ++ tailWord_6722591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6722591).length < 2 ^ (prefixWord ++ tailWord_6722591).sum := by decide
  have hdescent : baseEnd_6722591 < baseStart_6722591 := by decide
  rcases family_descends (prefixWord ++ tailWord_6722591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6722594 : List Nat := [3, 3, 1, 1, 1, 4, 1, 3, 1, 5]
def baseStart_6722594 : Nat := 118140960795 + 6722594 * 2 ^ 59
def prefixEnd_6722594 : Nat := 4983230072969 + 3 ^ 40 * 6722594 * 2
def baseEnd_6722594 : Nat := 1150640655677192017919453

theorem tailTrace_6722594 : CollatzResearch.WordTrace tailWord_6722594 prefixEnd_6722594 1150640655677192017919453 := by
  unfold tailWord_6722594
  simp only [CollatzResearch.WordTrace]
  refine ⟨61298286651799385123299709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163462097738131693662132557 61298286651799385123299709)
  ·
    refine ⟨22986857494424769421237391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61298286651799385123299709 22986857494424769421237391)
    ·
      refine ⟨34480286241637154131856087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22986857494424769421237391 34480286241637154131856087)
      ·
        refine ⟨51720429362455731197784131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34480286241637154131856087 51720429362455731197784131)
        ·
          refine ⟨77580644043683596796676197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51720429362455731197784131 77580644043683596796676197)
          ·
            refine ⟨14546370758190674399376787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 77580644043683596796676197 14546370758190674399376787)
            ·
              refine ⟨21819556137286011599065181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14546370758190674399376787 21819556137286011599065181)
              ·
                refine ⟨8182333551482254349649443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21819556137286011599065181 8182333551482254349649443)
                ·
                  refine ⟨12273500327223381524474165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8182333551482254349649443 12273500327223381524474165)
                  ·
                    refine ⟨1150640655677192017919453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12273500327223381524474165 1150640655677192017919453)
                    ·
                      rfl

theorem cell23_6722594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 3, 1, 5].length) (baseStart_6722594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6722594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6722594 prefixEnd_6722594 := by exact prefixLift 6722594
  have htrace : WordTrace (prefixWord ++ tailWord_6722594) baseStart_6722594 baseEnd_6722594 := by
    simpa [prefixWord, tailWord_6722594, baseEnd_6722594] using wordTrace_append hprefix tailTrace_6722594
  have hstable : (prefixWord ++ tailWord_6722594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6722594).length < 2 ^ (prefixWord ++ tailWord_6722594).sum := by decide
  have hdescent : baseEnd_6722594 < baseStart_6722594 := by decide
  rcases family_descends (prefixWord ++ tailWord_6722594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6722617 : List Nat := [1, 2, 1, 5, 2, 1, 1, 1, 3, 1, 5]
def baseStart_6722617 : Nat := 118140960795 + 6722617 * 2 ^ 59
def prefixEnd_6722617 : Nat := 4983230072969 + 3 ^ 40 * 6722617 * 2
def baseEnd_6722617 : Nat := 3451933777086629463770753

theorem tailTrace_6722617 : CollatzResearch.WordTrace tailWord_6722617 prefixEnd_6722617 3451933777086629463770753 := by
  unfold tailWord_6722617
  simp only [CollatzResearch.WordTrace]
  refine ⟨245193985486114215421286105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163462656990742810280857403 245193985486114215421286105)
  ·
    refine ⟨183895489114585661565964579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245193985486114215421286105 183895489114585661565964579)
    ·
      refine ⟨275843233671878492348946869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183895489114585661565964579 275843233671878492348946869)
      ·
        refine ⟨25860303156738608657713769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 275843233671878492348946869 25860303156738608657713769)
        ·
          refine ⟨19395227367553956493285327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25860303156738608657713769 19395227367553956493285327)
          ·
            refine ⟨29092841051330934739927991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19395227367553956493285327 29092841051330934739927991)
            ·
              refine ⟨43639261576996402109891987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29092841051330934739927991 43639261576996402109891987)
              ·
                refine ⟨65458892365494603164837981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43639261576996402109891987 65458892365494603164837981)
                ·
                  refine ⟨24547084637060476186814243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65458892365494603164837981 24547084637060476186814243)
                  ·
                    refine ⟨36820626955590714280221365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24547084637060476186814243 36820626955590714280221365)
                    ·
                      refine ⟨3451933777086629463770753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36820626955590714280221365 3451933777086629463770753)
                      ·
                        rfl

theorem cell23_6722617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 1, 3, 1, 5].length) (baseStart_6722617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6722617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6722617 prefixEnd_6722617 := by exact prefixLift 6722617
  have htrace : WordTrace (prefixWord ++ tailWord_6722617) baseStart_6722617 baseEnd_6722617 := by
    simpa [prefixWord, tailWord_6722617, baseEnd_6722617] using wordTrace_append hprefix tailTrace_6722617
  have hstable : (prefixWord ++ tailWord_6722617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6722617).length < 2 ^ (prefixWord ++ tailWord_6722617).sum := by decide
  have hdescent : baseEnd_6722617 < baseStart_6722617 := by decide
  rcases family_descends (prefixWord ++ tailWord_6722617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6722631 : List Nat := [1, 1, 4, 1, 3, 2, 2, 2, 3, 2, 2]
def baseStart_6722631 : Nat := 118140960795 + 6722631 * 2 ^ 59
def prefixEnd_6722631 : Nat := 4983230072969 + 3 ^ 40 * 6722631 * 2
def baseEnd_6722631 : Nat := 3451940965815792408995689

theorem tailTrace_6722631 : CollatzResearch.WordTrace tailWord_6722631 prefixEnd_6722631 3451940965815792408995689 := by
  unfold tailWord_6722631
  simp only [CollatzResearch.WordTrace]
  refine ⟨245194496108063495812295747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163462997405375663874863831 245194496108063495812295747)
  ·
    refine ⟨367791744162095243718443621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245194496108063495812295747 367791744162095243718443621)
    ·
      refine ⟨68960952030392858197208179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 367791744162095243718443621 68960952030392858197208179)
      ·
        refine ⟨103441428045589287295812269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68960952030392858197208179 103441428045589287295812269)
        ·
          refine ⟨38790535517095982735929601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103441428045589287295812269 38790535517095982735929601)
          ·
            refine ⟨29092901637821987051947201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38790535517095982735929601 29092901637821987051947201)
            ·
              refine ⟨21819676228366490288960401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29092901637821987051947201 21819676228366490288960401)
              ·
                refine ⟨16364757171274867716720301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21819676228366490288960401 16364757171274867716720301)
                ·
                  refine ⟨6136783939228075393770113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16364757171274867716720301 6136783939228075393770113)
                  ·
                    refine ⟨4602587954421056545327585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6136783939228075393770113 4602587954421056545327585)
                    ·
                      refine ⟨3451940965815792408995689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4602587954421056545327585 3451940965815792408995689)
                      ·
                        rfl

theorem cell23_6722631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 2, 3, 2, 2].length) (baseStart_6722631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6722631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6722631 prefixEnd_6722631 := by exact prefixLift 6722631
  have htrace : WordTrace (prefixWord ++ tailWord_6722631) baseStart_6722631 baseEnd_6722631 := by
    simpa [prefixWord, tailWord_6722631, baseEnd_6722631] using wordTrace_append hprefix tailTrace_6722631
  have hstable : (prefixWord ++ tailWord_6722631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6722631).length < 2 ^ (prefixWord ++ tailWord_6722631).sum := by decide
  have hdescent : baseEnd_6722631 < baseStart_6722631 := by decide
  rcases family_descends (prefixWord ++ tailWord_6722631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6722634 : List Nat := [3, 1, 2, 1, 1, 2, 3, 4, 1, 2, 3]
def baseStart_6722634 : Nat := 118140960795 + 6722634 * 2 ^ 59
def prefixEnd_6722634 : Nat := 4983230072969 + 3 ^ 40 * 6722634 * 2
def baseEnd_6722634 : Nat := 3451942506257755897258175

theorem tailTrace_6722634 : CollatzResearch.WordTrace tailWord_6722634 prefixEnd_6722634 3451942506257755897258175 := by
  unfold tailWord_6722634
  simp only [CollatzResearch.WordTrace]
  refine ⟨61298651381763156831163739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163463070351368418216436637 61298651381763156831163739)
  ·
    refine ⟨91947977072644735246745609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61298651381763156831163739 91947977072644735246745609)
    ·
      refine ⟨68960982804483551435059207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91947977072644735246745609 68960982804483551435059207)
      ·
        refine ⟨103441474206725327152588811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68960982804483551435059207 103441474206725327152588811)
        ·
          refine ⟨155162211310087990728883217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103441474206725327152588811 155162211310087990728883217)
          ·
            refine ⟨116371658482565993046662413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 155162211310087990728883217 116371658482565993046662413)
            ·
              refine ⟨43639371930962247392498405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 116371658482565993046662413 43639371930962247392498405)
              ·
                refine ⟨8182382237055421386093451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43639371930962247392498405 8182382237055421386093451)
                ·
                  refine ⟨12273573355583132079140177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8182382237055421386093451 12273573355583132079140177)
                  ·
                    refine ⟨9205180016687349059355133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12273573355583132079140177 9205180016687349059355133)
                    ·
                      refine ⟨3451942506257755897258175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9205180016687349059355133 3451942506257755897258175)
                      ·
                        rfl

theorem cell23_6722634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 4, 1, 2, 3].length) (baseStart_6722634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6722634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6722634 prefixEnd_6722634 := by exact prefixLift 6722634
  have htrace : WordTrace (prefixWord ++ tailWord_6722634) baseStart_6722634 baseEnd_6722634 := by
    simpa [prefixWord, tailWord_6722634, baseEnd_6722634] using wordTrace_append hprefix tailTrace_6722634
  have hstable : (prefixWord ++ tailWord_6722634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6722634).length < 2 ^ (prefixWord ++ tailWord_6722634).sum := by decide
  have hdescent : baseEnd_6722634 < baseStart_6722634 := by decide
  rcases family_descends (prefixWord ++ tailWord_6722634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6722640 : List Nat := [2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 6]
def baseStart_6722640 : Nat := 118140960795 + 6722640 * 2 ^ 59
def prefixEnd_6722640 : Nat := 4983230072969 + 3 ^ 40 * 6722640 * 2
def baseEnd_6722640 : Nat := 3451945587141682873783147

theorem tailTrace_6722640 : CollatzResearch.WordTrace tailWord_6722640 prefixEnd_6722640 3451945587141682873783147 := by
  unfold tailWord_6722640
  simp only [CollatzResearch.WordTrace]
  refine ⟨122597412182515445174686687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163463216243353926899582249 122597412182515445174686687)
  ·
    refine ⟨183896118273773167762030031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122597412182515445174686687 183896118273773167762030031)
    ·
      refine ⟨275844177410659751643045047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183896118273773167762030031 275844177410659751643045047)
      ·
        refine ⟨413766266115989627464567571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275844177410659751643045047 413766266115989627464567571)
        ·
          refine ⟨620649399173984441196851357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 413766266115989627464567571 620649399173984441196851357)
          ·
            refine ⟨232743524690244165448819259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 620649399173984441196851357 232743524690244165448819259)
            ·
              refine ⟨349115287035366248173228889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 232743524690244165448819259 349115287035366248173228889)
              ·
                refine ⟨261836465276524686129921667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 349115287035366248173228889 261836465276524686129921667)
                ·
                  refine ⟨392754697914787029194882501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 261836465276524686129921667 392754697914787029194882501)
                  ·
                    refine ⟨73641505859022567974040469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 392754697914787029194882501 73641505859022567974040469)
                    ·
                      refine ⟨3451945587141682873783147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 73641505859022567974040469 3451945587141682873783147)
                      ·
                        rfl

theorem cell23_6722640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 6].length) (baseStart_6722640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6722640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6722640 prefixEnd_6722640 := by exact prefixLift 6722640
  have htrace : WordTrace (prefixWord ++ tailWord_6722640) baseStart_6722640 baseEnd_6722640 := by
    simpa [prefixWord, tailWord_6722640, baseEnd_6722640] using wordTrace_append hprefix tailTrace_6722640
  have hstable : (prefixWord ++ tailWord_6722640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6722640).length < 2 ^ (prefixWord ++ tailWord_6722640).sum := by decide
  have hdescent : baseEnd_6722640 < baseStart_6722640 := by decide
  rcases family_descends (prefixWord ++ tailWord_6722640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6722647 : List Nat := [1, 1, 3, 2, 2, 1, 1, 3, 3, 3, 3]
def baseStart_6722647 : Nat := 118140960795 + 6722647 * 2 ^ 59
def prefixEnd_6722647 : Nat := 4983230072969 + 3 ^ 40 * 6722647 * 2
def baseEnd_6722647 : Nat := 3451949181506264346395615

theorem tailTrace_6722647 : CollatzResearch.WordTrace tailWord_6722647 prefixEnd_6722647 3451949181506264346395615 := by
  unfold tailWord_6722647
  simp only [CollatzResearch.WordTrace]
  refine ⟨245195079676005530544878195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163463386450670353696585463 245195079676005530544878195)
  ·
    refine ⟨367792619514008295817317293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245195079676005530544878195 367792619514008295817317293)
    ·
      refine ⟨137922232317753110931493985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 367792619514008295817317293 137922232317753110931493985)
      ·
        refine ⟨103441674238314833198620489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137922232317753110931493985 103441674238314833198620489)
        ·
          refine ⟨77581255678736124898965367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103441674238314833198620489 77581255678736124898965367)
          ·
            refine ⟨116371883518104187348448051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77581255678736124898965367 116371883518104187348448051)
            ·
              refine ⟨174557825277156281022672077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116371883518104187348448051 174557825277156281022672077)
              ·
                refine ⟨65459184478933605383502029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 174557825277156281022672077 65459184478933605383502029)
                ·
                  refine ⟨24547194179600102018813261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65459184478933605383502029 24547194179600102018813261)
                  ·
                    refine ⟨9205197817350038257054973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24547194179600102018813261 9205197817350038257054973)
                    ·
                      refine ⟨3451949181506264346395615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9205197817350038257054973 3451949181506264346395615)
                      ·
                        rfl

theorem cell23_6722647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 3, 3, 3, 3].length) (baseStart_6722647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6722647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6722647 prefixEnd_6722647 := by exact prefixLift 6722647
  have htrace : WordTrace (prefixWord ++ tailWord_6722647) baseStart_6722647 baseEnd_6722647 := by
    simpa [prefixWord, tailWord_6722647, baseEnd_6722647] using wordTrace_append hprefix tailTrace_6722647
  have hstable : (prefixWord ++ tailWord_6722647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6722647).length < 2 ^ (prefixWord ++ tailWord_6722647).sum := by decide
  have hdescent : baseEnd_6722647 < baseStart_6722647 := by decide
  rcases family_descends (prefixWord ++ tailWord_6722647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6722665 : List Nat := [1, 2, 1, 1, 1, 7, 3, 2, 1, 2, 2]
def baseStart_6722665 : Nat := 118140960795 + 6722665 * 2 ^ 59
def prefixEnd_6722665 : Nat := 4983230072969 + 3 ^ 40 * 6722665 * 2
def baseEnd_6722665 : Nat := 3451958424158045275970533

theorem tailTrace_6722665 : CollatzResearch.WordTrace tailWord_6722665 prefixEnd_6722665 3451958424158045275970533 := by
  unfold tailWord_6722665
  simp only [CollatzResearch.WordTrace]
  refine ⟨245195736189940319619033449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163463824126626879746022299 245195736189940319619033449)
  ·
    refine ⟨183896802142455239714275087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245195736189940319619033449 183896802142455239714275087)
    ·
      refine ⟨275845203213682859571412631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183896802142455239714275087 275845203213682859571412631)
      ·
        refine ⟨413767804820524289357118947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275845203213682859571412631 413767804820524289357118947)
        ·
          refine ⟨620651707230786434035678421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 413767804820524289357118947 620651707230786434035678421)
          ·
            refine ⟨14546524388221557047711213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 620651707230786434035678421 14546524388221557047711213)
            ·
              refine ⟨5454946645583083892891705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14546524388221557047711213 5454946645583083892891705)
              ·
                refine ⟨4091209984187312919668779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5454946645583083892891705 4091209984187312919668779)
                ·
                  refine ⟨6136814976280969379503169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4091209984187312919668779 6136814976280969379503169)
                  ·
                    refine ⟨4602611232210727034627377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6136814976280969379503169 4602611232210727034627377)
                    ·
                      refine ⟨3451958424158045275970533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4602611232210727034627377 3451958424158045275970533)
                      ·
                        rfl

theorem cell23_6722665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 3, 2, 1, 2, 2].length) (baseStart_6722665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6722665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6722665 prefixEnd_6722665 := by exact prefixLift 6722665
  have htrace : WordTrace (prefixWord ++ tailWord_6722665) baseStart_6722665 baseEnd_6722665 := by
    simpa [prefixWord, tailWord_6722665, baseEnd_6722665] using wordTrace_append hprefix tailTrace_6722665
  have hstable : (prefixWord ++ tailWord_6722665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6722665).length < 2 ^ (prefixWord ++ tailWord_6722665).sum := by decide
  have hdescent : baseEnd_6722665 < baseStart_6722665 := by decide
  rcases family_descends (prefixWord ++ tailWord_6722665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6722707 : List Nat := [1, 1, 1, 2, 1, 2, 6, 1, 2, 1, 5]
def baseStart_6722707 : Nat := 118140960795 + 6722707 * 2 ^ 59
def prefixEnd_6722707 : Nat := 4983230072969 + 3 ^ 40 * 6722707 * 2
def baseEnd_6722707 : Nat := 3451979990345534111645339

theorem tailTrace_6722707 : CollatzResearch.WordTrace tailWord_6722707 prefixEnd_6722707 3451979990345534111645339 := by
  unfold tailWord_6722707
  simp only [CollatzResearch.WordTrace]
  refine ⟨245197268055788160792062375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163464845370525440528041583 245197268055788160792062375)
  ·
    refine ⟨367795902083682241188093563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245197268055788160792062375 367795902083682241188093563)
    ·
      refine ⟨551693853125523361782140345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 367795902083682241188093563 551693853125523361782140345)
      ·
        refine ⟨413770389844142521336605259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 551693853125523361782140345 413770389844142521336605259)
        ·
          refine ⟨620655584766213782004907889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 413770389844142521336605259 620655584766213782004907889)
          ·
            refine ⟨465491688574660336503680917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 620655584766213782004907889 465491688574660336503680917)
            ·
              refine ⟨21819922901937203273610043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 465491688574660336503680917 21819922901937203273610043)
              ·
                refine ⟨32729884352905804910415065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21819922901937203273610043 32729884352905804910415065)
                ·
                  refine ⟨24547413264679353682811299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32729884352905804910415065 24547413264679353682811299)
                  ·
                    refine ⟨36821119897019030524216949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24547413264679353682811299 36821119897019030524216949)
                    ·
                      refine ⟨3451979990345534111645339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36821119897019030524216949 3451979990345534111645339)
                      ·
                        rfl

theorem cell23_6722707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 1, 2, 1, 5].length) (baseStart_6722707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6722707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6722707 prefixEnd_6722707 := by exact prefixLift 6722707
  have htrace : WordTrace (prefixWord ++ tailWord_6722707) baseStart_6722707 baseEnd_6722707 := by
    simpa [prefixWord, tailWord_6722707, baseEnd_6722707] using wordTrace_append hprefix tailTrace_6722707
  have hstable : (prefixWord ++ tailWord_6722707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6722707).length < 2 ^ (prefixWord ++ tailWord_6722707).sum := by decide
  have hdescent : baseEnd_6722707 < baseStart_6722707 := by decide
  rcases family_descends (prefixWord ++ tailWord_6722707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6722724 : List Nat := [2, 3, 1, 2, 3, 1, 1, 1, 2, 4, 3]
def baseStart_6722724 : Nat := 118140960795 + 6722724 * 2 ^ 59
def prefixEnd_6722724 : Nat := 4983230072969 + 3 ^ 40 * 6722724 * 2
def baseEnd_6722724 : Nat := 3451988719516660545132761

theorem tailTrace_6722724 : CollatzResearch.WordTrace tailWord_6722724 prefixEnd_6722724 3451988719516660545132761 := by
  unfold tailWord_6722724
  simp only [CollatzResearch.WordTrace]
  refine ⟨122598944048363286347715613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163465258731151048463620817 122598944048363286347715613)
  ·
    refine ⟨45974604018136232380393355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122598944048363286347715613 45974604018136232380393355)
    ·
      refine ⟨68961906027204348570590033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45974604018136232380393355 68961906027204348570590033)
      ·
        refine ⟨51721429520403261427942525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68961906027204348570590033 51721429520403261427942525)
        ·
          refine ⟨19395536070151223035478447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51721429520403261427942525 19395536070151223035478447)
          ·
            refine ⟨29093304105226834553217671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19395536070151223035478447 29093304105226834553217671)
            ·
              refine ⟨43639956157840251829826507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29093304105226834553217671 43639956157840251829826507)
              ·
                refine ⟨65459934236760377744739761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43639956157840251829826507 65459934236760377744739761)
                ·
                  refine ⟨49094950677570283308554821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65459934236760377744739761 49094950677570283308554821)
                  ·
                    refine ⟨9205303252044428120354029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 49094950677570283308554821 9205303252044428120354029)
                    ·
                      refine ⟨3451988719516660545132761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9205303252044428120354029 3451988719516660545132761)
                      ·
                        rfl

theorem cell23_6722724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 1, 2, 4, 3].length) (baseStart_6722724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6722724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6722724 prefixEnd_6722724 := by exact prefixLift 6722724
  have htrace : WordTrace (prefixWord ++ tailWord_6722724) baseStart_6722724 baseEnd_6722724 := by
    simpa [prefixWord, tailWord_6722724, baseEnd_6722724] using wordTrace_append hprefix tailTrace_6722724
  have hstable : (prefixWord ++ tailWord_6722724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6722724).length < 2 ^ (prefixWord ++ tailWord_6722724).sum := by decide
  have hdescent : baseEnd_6722724 < baseStart_6722724 := by decide
  rcases family_descends (prefixWord ++ tailWord_6722724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6722738 : List Nat := [3, 2, 1, 1, 1, 4, 2, 3, 2, 2, 2]
def baseStart_6722738 : Nat := 118140960795 + 6722738 * 2 ^ 59
def prefixEnd_6722738 : Nat := 4983230072969 + 3 ^ 40 * 6722738 * 2
def baseEnd_6722738 : Nat := 3451995908245823490357697

theorem tailTrace_6722738 : CollatzResearch.WordTrace tailWord_6722738 prefixEnd_6722738 3451995908245823490357697 := by
  unfold tailWord_6722738
  simp only [CollatzResearch.WordTrace]
  refine ⟨61299599679668963271610217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163465599145783902057627245 61299599679668963271610217)
  ·
    refine ⟨45974699759751722453707663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61299599679668963271610217 45974699759751722453707663)
    ·
      refine ⟨68962049639627583680561495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45974699759751722453707663 68962049639627583680561495)
      ·
        refine ⟨103443074459441375520842243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68962049639627583680561495 103443074459441375520842243)
        ·
          refine ⟨155164611689162063281263365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103443074459441375520842243 155164611689162063281263365)
          ·
            refine ⟨29093364691717886865236881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 155164611689162063281263365 29093364691717886865236881)
            ·
              refine ⟨21820023518788415148927661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29093364691717886865236881 21820023518788415148927661)
              ·
                refine ⟨8182508819545655680847873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21820023518788415148927661 8182508819545655680847873)
                ·
                  refine ⟨6136881614659241760635905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8182508819545655680847873 6136881614659241760635905)
                  ·
                    refine ⟨4602661210994431320476929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6136881614659241760635905 4602661210994431320476929)
                    ·
                      refine ⟨3451995908245823490357697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4602661210994431320476929 3451995908245823490357697)
                      ·
                        rfl

theorem cell23_6722738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 3, 2, 2, 2].length) (baseStart_6722738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6722738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6722738 prefixEnd_6722738 := by exact prefixLift 6722738
  have htrace : WordTrace (prefixWord ++ tailWord_6722738) baseStart_6722738 baseEnd_6722738 := by
    simpa [prefixWord, tailWord_6722738, baseEnd_6722738] using wordTrace_append hprefix tailTrace_6722738
  have hstable : (prefixWord ++ tailWord_6722738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6722738).length < 2 ^ (prefixWord ++ tailWord_6722738).sum := by decide
  have hdescent : baseEnd_6722738 < baseStart_6722738 := by decide
  rcases family_descends (prefixWord ++ tailWord_6722738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6722767 : List Nat := [1, 1, 2, 1, 1, 3, 2, 4, 1, 2, 5]
def baseStart_6722767 : Nat := 118140960795 + 6722767 * 2 ^ 59
def prefixEnd_6722767 : Nat := 4983230072969 + 3 ^ 40 * 6722767 * 2
def baseEnd_6722767 : Nat := 3452010799184803876895063

theorem tailTrace_6722767 : CollatzResearch.WordTrace tailWord_6722767 prefixEnd_6722767 3452010799184803876895063 := by
  unfold tailWord_6722767
  simp only [CollatzResearch.WordTrace]
  refine ⟨245199456435570791039246555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163466304290380527359497703 245199456435570791039246555)
  ·
    refine ⟨367799184653356186558869833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245199456435570791039246555 367799184653356186558869833)
    ·
      refine ⟨275849388490017139919152375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 367799184653356186558869833 275849388490017139919152375)
      ·
        refine ⟨413774082735025709878728563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275849388490017139919152375 413774082735025709878728563)
        ·
          refine ⟨620661124102538564818092845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 413774082735025709878728563 620661124102538564818092845)
          ·
            refine ⟨232747921538451961806784817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 620661124102538564818092845 232747921538451961806784817)
            ·
              refine ⟨174560941153838971355088613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 232747921538451961806784817 174560941153838971355088613)
              ·
                refine ⟨32730176466344807129079115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 174560941153838971355088613 32730176466344807129079115)
                ·
                  refine ⟨49095264699517210693618673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32730176466344807129079115 49095264699517210693618673)
                  ·
                    refine ⟨36821448524637908020214005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49095264699517210693618673 36821448524637908020214005)
                    ·
                      refine ⟨3452010799184803876895063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36821448524637908020214005 3452010799184803876895063)
                      ·
                        rfl

theorem cell23_6722767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 4, 1, 2, 5].length) (baseStart_6722767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6722767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6722767 prefixEnd_6722767 := by exact prefixLift 6722767
  have htrace : WordTrace (prefixWord ++ tailWord_6722767) baseStart_6722767 baseEnd_6722767 := by
    simpa [prefixWord, tailWord_6722767, baseEnd_6722767] using wordTrace_append hprefix tailTrace_6722767
  have hstable : (prefixWord ++ tailWord_6722767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6722767).length < 2 ^ (prefixWord ++ tailWord_6722767).sum := by decide
  have hdescent : baseEnd_6722767 < baseStart_6722767 := by decide
  rcases family_descends (prefixWord ++ tailWord_6722767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6722794 : List Nat := [3, 1, 3, 1, 1, 3, 1, 2, 1, 3, 4]
def baseStart_6722794 : Nat := 118140960795 + 6722794 * 2 ^ 59
def prefixEnd_6722794 : Nat := 4983230072969 + 3 ^ 40 * 6722794 * 2
def baseEnd_6722794 : Nat := 3452024663162475271257439

theorem tailTrace_6722794 : CollatzResearch.WordTrace tailWord_6722794 prefixEnd_6722794 3452024663162475271257439 := by
  unfold tailWord_6722794
  simp only [CollatzResearch.WordTrace]
  refine ⟨61300110301618243662619859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163466960804315316433652957 61300110301618243662619859)
  ·
    refine ⟨91950165452427365493929789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61300110301618243662619859 91950165452427365493929789)
    ·
      refine ⟨34481312044660262060223671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91950165452427365493929789 34481312044660262060223671)
      ·
        refine ⟨51721968066990393090335507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34481312044660262060223671 51721968066990393090335507)
        ·
          refine ⟨77582952100485589635503261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51721968066990393090335507 77582952100485589635503261)
          ·
            refine ⟨29093607037682096113313723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77582952100485589635503261 29093607037682096113313723)
            ·
              refine ⟨43640410556523144169970585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29093607037682096113313723 43640410556523144169970585)
              ·
                refine ⟨32730307917392358127477939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43640410556523144169970585 32730307917392358127477939)
                ·
                  refine ⟨49095461876088537191216909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32730307917392358127477939 49095461876088537191216909)
                  ·
                    refine ⟨18410798203533201446706341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49095461876088537191216909 18410798203533201446706341)
                    ·
                      refine ⟨3452024663162475271257439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18410798203533201446706341 3452024663162475271257439)
                      ·
                        rfl

theorem cell23_6722794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 2, 1, 3, 4].length) (baseStart_6722794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6722794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6722794 prefixEnd_6722794 := by exact prefixLift 6722794
  have htrace : WordTrace (prefixWord ++ tailWord_6722794) baseStart_6722794 baseEnd_6722794 := by
    simpa [prefixWord, tailWord_6722794, baseEnd_6722794] using wordTrace_append hprefix tailTrace_6722794
  have hstable : (prefixWord ++ tailWord_6722794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6722794).length < 2 ^ (prefixWord ++ tailWord_6722794).sum := by decide
  have hdescent : baseEnd_6722794 < baseStart_6722794 := by decide
  rcases family_descends (prefixWord ++ tailWord_6722794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6722807 : List Nat := [1, 1, 3, 1, 1, 1, 2, 2, 4, 1, 6]
def baseStart_6722807 : Nat := 118140960795 + 6722807 * 2 ^ 59
def prefixEnd_6722807 : Nat := 4983230072969 + 3 ^ 40 * 6722807 * 2
def baseEnd_6722807 : Nat := 3452031338410983720394879

theorem tailTrace_6722807 : CollatzResearch.WordTrace tailWord_6722807 prefixEnd_6722807 3452031338410983720394879 := by
  unfold tailWord_6722807
  simp only [CollatzResearch.WordTrace]
  refine ⟨245200915355425877870702675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163467276903617251913801783 245200915355425877870702675)
  ·
    refine ⟨367801373033138816806054013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245200915355425877870702675 367801373033138816806054013)
    ·
      refine ⟨137925514887427056302270255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 367801373033138816806054013 137925514887427056302270255)
      ·
        refine ⟨206888272331140584453405383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137925514887427056302270255 206888272331140584453405383)
        ·
          refine ⟨310332408496710876680108075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206888272331140584453405383 310332408496710876680108075)
          ·
            refine ⟨465498612745066315020162113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 310332408496710876680108075 465498612745066315020162113)
            ·
              refine ⟨349123959558799736265121585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 465498612745066315020162113 349123959558799736265121585)
              ·
                refine ⟨261842969669099802198841189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 349123959558799736265121585 261842969669099802198841189)
                ·
                  refine ⟨49095556812956212912282723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 261842969669099802198841189 49095556812956212912282723)
                  ·
                    refine ⟨73643335219434319368424085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49095556812956212912282723 73643335219434319368424085)
                    ·
                      refine ⟨3452031338410983720394879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 73643335219434319368424085 3452031338410983720394879)
                      ·
                        rfl

theorem cell23_6722807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 2, 4, 1, 6].length) (baseStart_6722807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6722807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6722807 prefixEnd_6722807 := by exact prefixLift 6722807
  have htrace : WordTrace (prefixWord ++ tailWord_6722807) baseStart_6722807 baseEnd_6722807 := by
    simpa [prefixWord, tailWord_6722807, baseEnd_6722807] using wordTrace_append hprefix tailTrace_6722807
  have hstable : (prefixWord ++ tailWord_6722807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6722807).length < 2 ^ (prefixWord ++ tailWord_6722807).sum := by decide
  have hdescent : baseEnd_6722807 < baseStart_6722807 := by decide
  rcases family_descends (prefixWord ++ tailWord_6722807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6722851 : List Nat := [1, 1, 1, 4, 2, 3, 4, 1, 6]
def baseStart_6722851 : Nat := 118140960795 + 6722851 * 2 ^ 59
def prefixEnd_6722851 : Nat := 4983230072969 + 3 ^ 40 * 6722851 * 2
def baseEnd_6722851 : Nat := 383561547951086838693853

theorem tailTrace_6722851 : CollatzResearch.WordTrace tailWord_6722851 prefixEnd_6722851 383561547951086838693853 := by
  unfold tailWord_6722851
  simp only [CollatzResearch.WordTrace]
  refine ⟨245202520167266473385304407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163468346778177648923536271 245202520167266473385304407)
  ·
    refine ⟨367803780250899710077956611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245202520167266473385304407 367803780250899710077956611)
    ·
      refine ⟨551705670376349565116934917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 367803780250899710077956611 551705670376349565116934917)
      ·
        refine ⟨103444813195565543459425297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 551705670376349565116934917 103444813195565543459425297)
        ·
          refine ⟨77583609896674157594568973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103444813195565543459425297 77583609896674157594568973)
          ·
            refine ⟨29093853711252809097963365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77583609896674157594568973 29093853711252809097963365)
            ·
              refine ⟨5455097570859901705868131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29093853711252809097963365 5455097570859901705868131)
              ·
                refine ⟨8182646356289852558802197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5455097570859901705868131 8182646356289852558802197)
                ·
                  refine ⟨383561547951086838693853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8182646356289852558802197 383561547951086838693853)
                  ·
                    rfl

theorem cell23_6722851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 4, 1, 6].length) (baseStart_6722851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6722851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6722851 prefixEnd_6722851 := by exact prefixLift 6722851
  have htrace : WordTrace (prefixWord ++ tailWord_6722851) baseStart_6722851 baseEnd_6722851 := by
    simpa [prefixWord, tailWord_6722851, baseEnd_6722851] using wordTrace_append hprefix tailTrace_6722851
  have hstable : (prefixWord ++ tailWord_6722851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6722851).length < 2 ^ (prefixWord ++ tailWord_6722851).sum := by decide
  have hdescent : baseEnd_6722851 < baseStart_6722851 := by decide
  rcases family_descends (prefixWord ++ tailWord_6722851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6722864 : List Nat := [2, 1, 1, 1, 2, 2, 5, 1, 3, 5]
def baseStart_6722864 : Nat := 118140960795 + 6722864 * 2 ^ 59
def prefixEnd_6722864 : Nat := 4983230072969 + 3 ^ 40 * 6722864 * 2
def baseEnd_6722864 : Nat := 1150686868936096665794039

theorem tailTrace_6722864 : CollatzResearch.WordTrace tailWord_6722864 prefixEnd_6722864 1150686868936096665794039 := by
  unfold tailWord_6722864
  simp only [CollatzResearch.WordTrace]
  refine ⟨122601497158109688302763823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163468662877479584403685097 122601497158109688302763823)
  ·
    refine ⟨183902245737164532454145735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122601497158109688302763823 183902245737164532454145735)
    ·
      refine ⟨275853368605746798681218603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183902245737164532454145735 275853368605746798681218603)
      ·
        refine ⟨413780052908620198021827905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275853368605746798681218603 413780052908620198021827905)
        ·
          refine ⟨310335039681465148516370929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 413780052908620198021827905 310335039681465148516370929)
          ·
            refine ⟨232751279761098861387278197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 310335039681465148516370929 232751279761098861387278197)
            ·
              refine ⟨21820432477603018255057331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 232751279761098861387278197 21820432477603018255057331)
              ·
                refine ⟨32730648716404527382585997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21820432477603018255057331 32730648716404527382585997)
                ·
                  refine ⟨12273993268651697768469749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32730648716404527382585997 12273993268651697768469749)
                  ·
                    refine ⟨1150686868936096665794039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12273993268651697768469749 1150686868936096665794039)
                    ·
                      rfl

theorem cell23_6722864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 1, 3, 5].length) (baseStart_6722864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6722864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6722864 prefixEnd_6722864 := by exact prefixLift 6722864
  have htrace : WordTrace (prefixWord ++ tailWord_6722864) baseStart_6722864 baseEnd_6722864 := by
    simpa [prefixWord, tailWord_6722864, baseEnd_6722864] using wordTrace_append hprefix tailTrace_6722864
  have hstable : (prefixWord ++ tailWord_6722864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6722864).length < 2 ^ (prefixWord ++ tailWord_6722864).sum := by decide
  have hdescent : baseEnd_6722864 < baseStart_6722864 := by decide
  rcases family_descends (prefixWord ++ tailWord_6722864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6722894 : List Nat := [4, 1, 1, 1, 1, 1, 3, 2, 3, 6]
def baseStart_6722894 : Nat := 118140960795 + 6722894 * 2 ^ 59
def prefixEnd_6722894 : Nat := 4983230072969 + 3 ^ 40 * 6722894 * 2
def baseEnd_6722894 : Nat := 1150692003742641626668993

theorem tailTrace_6722894 : CollatzResearch.WordTrace tailWord_6722894 prefixEnd_6722894 1150692003742641626668993 := by
  unfold tailWord_6722894
  simp only [CollatzResearch.WordTrace]
  refine ⟨30650511063263836466139967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 163469392337407127819413157 30650511063263836466139967)
  ·
    refine ⟨45975766594895754699209951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30650511063263836466139967 45975766594895754699209951)
    ·
      refine ⟨68963649892343632048814927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45975766594895754699209951 68963649892343632048814927)
      ·
        refine ⟨103445474838515448073222391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68963649892343632048814927 103445474838515448073222391)
        ·
          refine ⟨155168212257773172109833587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103445474838515448073222391 155168212257773172109833587)
          ·
            refine ⟨232752318386659758164750381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155168212257773172109833587 232752318386659758164750381)
            ·
              refine ⟨87282119394997409311781393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 232752318386659758164750381 87282119394997409311781393)
              ·
                refine ⟨65461589546248056983836045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87282119394997409311781393 65461589546248056983836045)
                ·
                  refine ⟨24548096079843021368938517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65461589546248056983836045 24548096079843021368938517)
                  ·
                    refine ⟨1150692003742641626668993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24548096079843021368938517 1150692003742641626668993)
                    ·
                      rfl

theorem cell23_6722894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 2, 3, 6].length) (baseStart_6722894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6722894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6722894 prefixEnd_6722894 := by exact prefixLift 6722894
  have htrace : WordTrace (prefixWord ++ tailWord_6722894) baseStart_6722894 baseEnd_6722894 := by
    simpa [prefixWord, tailWord_6722894, baseEnd_6722894] using wordTrace_append hprefix tailTrace_6722894
  have hstable : (prefixWord ++ tailWord_6722894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6722894).length < 2 ^ (prefixWord ++ tailWord_6722894).sum := by decide
  have hdescent : baseEnd_6722894 < baseStart_6722894 := by decide
  rcases family_descends (prefixWord ++ tailWord_6722894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6722901 : List Nat := [1, 3, 2, 2, 3, 1, 1, 2, 3, 1, 4]
def baseStart_6722901 : Nat := 118140960795 + 6722901 * 2 ^ 59
def prefixEnd_6722901 : Nat := 4983230072969 + 3 ^ 40 * 6722901 * 2
def baseEnd_6722901 : Nat := 3452079605592506352619447

theorem tailTrace_6722901 : CollatzResearch.WordTrace tailWord_6722901 prefixEnd_6722901 3452079605592506352619447 := by
  unfold tailWord_6722901
  simp only [CollatzResearch.WordTrace]
  refine ⟨245204343817085331924624557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163469562544723554616416371 245204343817085331924624557)
  ·
    refine ⟨91951628931406999471734209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 245204343817085331924624557 91951628931406999471734209)
    ·
      refine ⟨68963721698555249603800657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91951628931406999471734209 68963721698555249603800657)
      ·
        refine ⟨51722791273916437202850493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68963721698555249603800657 51722791273916437202850493)
        ·
          refine ⟨19396046727718663951068935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51722791273916437202850493 19396046727718663951068935)
          ·
            refine ⟨29094070091577995926603403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19396046727718663951068935 29094070091577995926603403)
            ·
              refine ⟨43641105137366993889905105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29094070091577995926603403 43641105137366993889905105)
              ·
                refine ⟨32730828853025245417428829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43641105137366993889905105 32730828853025245417428829)
                ·
                  refine ⟨12274060819884467031535811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32730828853025245417428829 12274060819884467031535811)
                  ·
                    refine ⟨18411091229826700547303717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12274060819884467031535811 18411091229826700547303717)
                    ·
                      refine ⟨3452079605592506352619447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18411091229826700547303717 3452079605592506352619447)
                      ·
                        rfl

theorem cell23_6722901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 2, 3, 1, 4].length) (baseStart_6722901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6722901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6722901 prefixEnd_6722901 := by exact prefixLift 6722901
  have htrace : WordTrace (prefixWord ++ tailWord_6722901) baseStart_6722901 baseEnd_6722901 := by
    simpa [prefixWord, tailWord_6722901, baseEnd_6722901] using wordTrace_append hprefix tailTrace_6722901
  have hstable : (prefixWord ++ tailWord_6722901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6722901).length < 2 ^ (prefixWord ++ tailWord_6722901).sum := by decide
  have hdescent : baseEnd_6722901 < baseStart_6722901 := by decide
  rcases family_descends (prefixWord ++ tailWord_6722901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6722904 : List Nat := [2, 1, 2, 2, 1, 1, 4, 1, 3, 1, 5]
def baseStart_6722904 : Nat := 118140960795 + 6722904 * 2 ^ 59
def prefixEnd_6722904 : Nat := 4983230072969 + 3 ^ 40 * 6722904 * 2
def baseEnd_6722904 : Nat := 3452081146034469840881933

theorem tailTrace_6722904 : CollatzResearch.WordTrace tailWord_6722904 prefixEnd_6722904 3452081146034469840881933 := by
  unfold tailWord_6722904
  simp only [CollatzResearch.WordTrace]
  refine ⟨122602226618037231718491883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163469635490716308957989177 122602226618037231718491883)
  ·
    refine ⟨183903339927055847577737825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122602226618037231718491883 183903339927055847577737825)
    ·
      refine ⟨137927504945291885683303369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183903339927055847577737825 137927504945291885683303369)
      ·
        refine ⟨103445628708968914262477527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137927504945291885683303369 103445628708968914262477527)
        ·
          refine ⟨155168443063453371393716291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103445628708968914262477527 155168443063453371393716291)
          ·
            refine ⟨232752664595180057090574437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155168443063453371393716291 232752664595180057090574437)
            ·
              refine ⟨43641124611596260704482707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 232752664595180057090574437 43641124611596260704482707)
              ·
                refine ⟨65461686917394391056724061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43641124611596260704482707 65461686917394391056724061)
                ·
                  refine ⟨24548132594022896646271523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65461686917394391056724061 24548132594022896646271523)
                  ·
                    refine ⟨36822198891034344969407285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24548132594022896646271523 36822198891034344969407285)
                    ·
                      refine ⟨3452081146034469840881933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36822198891034344969407285 3452081146034469840881933)
                      ·
                        rfl

theorem cell23_6722904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 1, 3, 1, 5].length) (baseStart_6722904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6722904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6722904 prefixEnd_6722904 := by exact prefixLift 6722904
  have htrace : WordTrace (prefixWord ++ tailWord_6722904) baseStart_6722904 baseEnd_6722904 := by
    simpa [prefixWord, tailWord_6722904, baseEnd_6722904] using wordTrace_append hprefix tailTrace_6722904
  have hstable : (prefixWord ++ tailWord_6722904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6722904).length < 2 ^ (prefixWord ++ tailWord_6722904).sum := by decide
  have hdescent : baseEnd_6722904 < baseStart_6722904 := by decide
  rcases family_descends (prefixWord ++ tailWord_6722904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6722922 : List Nat := [3, 1, 3, 3, 2, 2, 1, 1, 2, 3, 2]
def baseStart_6722922 : Nat := 118140960795 + 6722922 * 2 ^ 59
def prefixEnd_6722922 : Nat := 4983230072969 + 3 ^ 40 * 6722922 * 2
def baseEnd_6722922 : Nat := 3452090388686250770456851

theorem tailTrace_6722922 : CollatzResearch.WordTrace tailWord_6722922 prefixEnd_6722922 3452090388686250770456851 := by
  unfold tailWord_6722922
  simp only [CollatzResearch.WordTrace]
  refine ⟨61301277437502313127784755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163470073166672835007426013 61301277437502313127784755)
  ·
    refine ⟨91951916156253469691677133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61301277437502313127784755 91951916156253469691677133)
    ·
      refine ⟨34481968558595051134378925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91951916156253469691677133 34481968558595051134378925)
      ·
        refine ⟨12930738209473144175392097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34481968558595051134378925 12930738209473144175392097)
        ·
          refine ⟨9698053657104858131544073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12930738209473144175392097 9698053657104858131544073)
          ·
            refine ⟨7273540242828643598658055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9698053657104858131544073 7273540242828643598658055)
            ·
              refine ⟨10910310364242965397987083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7273540242828643598658055 10910310364242965397987083)
              ·
                refine ⟨16365465546364448096980625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10910310364242965397987083 16365465546364448096980625)
                ·
                  refine ⟨12274099159773336072735469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16365465546364448096980625 12274099159773336072735469)
                  ·
                    refine ⟨4602787184915001027275801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12274099159773336072735469 4602787184915001027275801)
                    ·
                      refine ⟨3452090388686250770456851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4602787184915001027275801 3452090388686250770456851)
                      ·
                        rfl

theorem cell23_6722922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 1, 1, 2, 3, 2].length) (baseStart_6722922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6722922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6722922 prefixEnd_6722922 := by exact prefixLift 6722922
  have htrace : WordTrace (prefixWord ++ tailWord_6722922) baseStart_6722922 baseEnd_6722922 := by
    simpa [prefixWord, tailWord_6722922, baseEnd_6722922] using wordTrace_append hprefix tailTrace_6722922
  have hstable : (prefixWord ++ tailWord_6722922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6722922).length < 2 ^ (prefixWord ++ tailWord_6722922).sum := by decide
  have hdescent : baseEnd_6722922 < baseStart_6722922 := by decide
  rcases family_descends (prefixWord ++ tailWord_6722922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6722952 : List Nat := [2, 1, 3, 3, 1, 2, 2, 4, 1, 2, 2]
def baseStart_6722952 : Nat := 118140960795 + 6722952 * 2 ^ 59
def prefixEnd_6722952 : Nat := 4983230072969 + 3 ^ 40 * 6722952 * 2
def baseEnd_6722952 : Nat := 3452105793105885653081713

theorem tailTrace_6722952 : CollatzResearch.WordTrace tailWord_6722952 prefixEnd_6722952 3452105793105885653081713 := by
  unfold tailWord_6722952
  simp only [CollatzResearch.WordTrace]
  refine ⟨122603101969950283817365555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163470802626600378423154073 122603101969950283817365555)
  ·
    refine ⟨183904652954925425726048333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122603101969950283817365555 183904652954925425726048333)
    ·
      refine ⟨68964244858097034647268125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 183904652954925425726048333 68964244858097034647268125)
      ·
        refine ⟨25861591821786387992725547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68964244858097034647268125 25861591821786387992725547)
        ·
          refine ⟨38792387732679581989088321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25861591821786387992725547 38792387732679581989088321)
          ·
            refine ⟨29094290799509686491816241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38792387732679581989088321 29094290799509686491816241)
            ·
              refine ⟨21820718099632264868862181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29094290799509686491816241 21820718099632264868862181)
              ·
                refine ⟨4091384643681049662911659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21820718099632264868862181 4091384643681049662911659)
                ·
                  refine ⟨6137076965521574494367489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4091384643681049662911659 6137076965521574494367489)
                  ·
                    refine ⟨4602807724141180870775617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6137076965521574494367489 4602807724141180870775617)
                    ·
                      refine ⟨3452105793105885653081713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4602807724141180870775617 3452105793105885653081713)
                      ·
                        rfl

theorem cell23_6722952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 4, 1, 2, 2].length) (baseStart_6722952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6722952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6722952 prefixEnd_6722952 := by exact prefixLift 6722952
  have htrace : WordTrace (prefixWord ++ tailWord_6722952) baseStart_6722952 baseEnd_6722952 := by
    simpa [prefixWord, tailWord_6722952, baseEnd_6722952] using wordTrace_append hprefix tailTrace_6722952
  have hstable : (prefixWord ++ tailWord_6722952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6722952).length < 2 ^ (prefixWord ++ tailWord_6722952).sum := by decide
  have hdescent : baseEnd_6722952 < baseStart_6722952 := by decide
  rcases family_descends (prefixWord ++ tailWord_6722952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6722962 : List Nat := [3, 2, 3, 3, 2, 1, 1, 1, 1, 6]
def baseStart_6722962 : Nat := 118140960795 + 6722962 * 2 ^ 59
def prefixEnd_6722962 : Nat := 4983230072969 + 3 ^ 40 * 6722962 * 2
def baseEnd_6722962 : Nat := 1150703642637476871318889

theorem tailTrace_6722962 : CollatzResearch.WordTrace tailWord_6722962 prefixEnd_6722962 1150703642637476871318889 := by
  unfold tailWord_6722962
  simp only [CollatzResearch.WordTrace]
  refine ⟨61301642167466084835648785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163471045779909559561730093 61301642167466084835648785)
  ·
    refine ⟨45976231625599563626736589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61301642167466084835648785 45976231625599563626736589)
    ·
      refine ⟨17241086859599836360026221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45976231625599563626736589 17241086859599836360026221)
      ·
        refine ⟨6465407572349938635009833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17241086859599836360026221 6465407572349938635009833)
        ·
          refine ⟨4849055679262453976257375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6465407572349938635009833 4849055679262453976257375)
          ·
            refine ⟨7273583518893680964386063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4849055679262453976257375 7273583518893680964386063)
            ·
              refine ⟨10910375278340521446579095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7273583518893680964386063 10910375278340521446579095)
              ·
                refine ⟨16365562917510782169868643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10910375278340521446579095 16365562917510782169868643)
                ·
                  refine ⟨24548344376266173254802965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16365562917510782169868643 24548344376266173254802965)
                  ·
                    refine ⟨1150703642637476871318889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24548344376266173254802965 1150703642637476871318889)
                    ·
                      rfl

theorem cell23_6722962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 1, 1, 1, 6].length) (baseStart_6722962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6722962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6722962 prefixEnd_6722962 := by exact prefixLift 6722962
  have htrace : WordTrace (prefixWord ++ tailWord_6722962) baseStart_6722962 baseEnd_6722962 := by
    simpa [prefixWord, tailWord_6722962, baseEnd_6722962] using wordTrace_append hprefix tailTrace_6722962
  have hstable : (prefixWord ++ tailWord_6722962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6722962).length < 2 ^ (prefixWord ++ tailWord_6722962).sum := by decide
  have hdescent : baseEnd_6722962 < baseStart_6722962 := by decide
  rcases family_descends (prefixWord ++ tailWord_6722962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6722972 : List Nat := [2, 2, 3, 4, 1, 1, 2, 2, 1, 2, 3]
def baseStart_6722972 : Nat := 118140960795 + 6722972 * 2 ^ 59
def prefixEnd_6722972 : Nat := 4983230072969 + 3 ^ 40 * 6722972 * 2
def baseEnd_6722972 : Nat := 3452116062718975574831621

theorem tailTrace_6722972 : CollatzResearch.WordTrace tailWord_6722972 prefixEnd_6722972 3452116062718975574831621 := by
  unfold tailWord_6722972
  simp only [CollatzResearch.WordTrace]
  refine ⟨122603466699914055525229585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163471288933218740700306113 122603466699914055525229585)
  ·
    refine ⟨91952600024935541643922189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122603466699914055525229585 91952600024935541643922189)
    ·
      refine ⟨34482225009350828116470821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91952600024935541643922189 34482225009350828116470821)
      ·
        refine ⟨6465417189253280271838279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34482225009350828116470821 6465417189253280271838279)
        ·
          refine ⟨9698125783879920407757419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6465417189253280271838279 9698125783879920407757419)
          ·
            refine ⟨14547188675819880611636129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9698125783879920407757419 14547188675819880611636129)
            ·
              refine ⟨10910391506864910458727097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14547188675819880611636129 10910391506864910458727097)
              ·
                refine ⟨8182793630148682844045323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10910391506864910458727097 8182793630148682844045323)
                ·
                  refine ⟨12274190445223024266067985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8182793630148682844045323 12274190445223024266067985)
                  ·
                    refine ⟨9205642833917268199550989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12274190445223024266067985 9205642833917268199550989)
                    ·
                      refine ⟨3452116062718975574831621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9205642833917268199550989 3452116062718975574831621)
                      ·
                        rfl

theorem cell23_6722972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_6722972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6722972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6722972 prefixEnd_6722972 := by exact prefixLift 6722972
  have htrace : WordTrace (prefixWord ++ tailWord_6722972) baseStart_6722972 baseEnd_6722972 := by
    simpa [prefixWord, tailWord_6722972, baseEnd_6722972] using wordTrace_append hprefix tailTrace_6722972
  have hstable : (prefixWord ++ tailWord_6722972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6722972).length < 2 ^ (prefixWord ++ tailWord_6722972).sum := by decide
  have hdescent : baseEnd_6722972 < baseStart_6722972 := by decide
  rcases family_descends (prefixWord ++ tailWord_6722972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6723024 : List Nat := [2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 9]
def baseStart_6723024 : Nat := 118140960795 + 6723024 * 2 ^ 59
def prefixEnd_6723024 : Nat := 4983230072969 + 3 ^ 40 * 6723024 * 2
def baseEnd_6723024 : Nat := 3452142763713009371381381

theorem tailTrace_6723024 : CollatzResearch.WordTrace tailWord_6723024 prefixEnd_6723024 3452142763713009371381381 := by
  unfold tailWord_6723024
  simp only [CollatzResearch.WordTrace]
  refine ⟨122604414997819861965676063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163472553330426482620901417 122604414997819861965676063)
  ·
    refine ⟨183906622496729792948514095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122604414997819861965676063 183906622496729792948514095)
    ·
      refine ⟨275859933745094689422771143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183906622496729792948514095 275859933745094689422771143)
      ·
        refine ⟨413789900617642034134156715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275859933745094689422771143 413789900617642034134156715)
        ·
          refine ⟨620684850926463051201235073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 413789900617642034134156715 620684850926463051201235073)
          ·
            refine ⟨465513638194847288400926305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 620684850926463051201235073 465513638194847288400926305)
            ·
              refine ⟨349135228646135466300694729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 465513638194847288400926305 349135228646135466300694729)
              ·
                refine ⟨261851421484601599725521047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 349135228646135466300694729 261851421484601599725521047)
                ·
                  refine ⟨392777132226902399588281571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 261851421484601599725521047 392777132226902399588281571)
                  ·
                    refine ⟨589165698340353599382422357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 392777132226902399588281571 589165698340353599382422357)
                    ·
                      refine ⟨3452142763713009371381381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 589165698340353599382422357 3452142763713009371381381)
                      ·
                        rfl

theorem cell23_6723024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 9].length) (baseStart_6723024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6723024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6723024 prefixEnd_6723024 := by exact prefixLift 6723024
  have htrace : WordTrace (prefixWord ++ tailWord_6723024) baseStart_6723024 baseEnd_6723024 := by
    simpa [prefixWord, tailWord_6723024, baseEnd_6723024] using wordTrace_append hprefix tailTrace_6723024
  have hstable : (prefixWord ++ tailWord_6723024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6723024).length < 2 ^ (prefixWord ++ tailWord_6723024).sum := by decide
  have hdescent : baseEnd_6723024 < baseStart_6723024 := by decide
  rcases family_descends (prefixWord ++ tailWord_6723024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6723048 : List Nat := [2, 1, 4, 1, 1, 2, 2, 5, 5]
def baseStart_6723048 : Nat := 118140960795 + 6723048 * 2 ^ 59
def prefixEnd_6723048 : Nat := 4983230072969 + 3 ^ 40 * 6723048 * 2
def baseEnd_6723048 : Nat := 383572787472079697497919

theorem tailTrace_6723048 : CollatzResearch.WordTrace tailWord_6723048 prefixEnd_6723048 383572787472079697497919 := by
  unfold tailWord_6723048
  simp only [CollatzResearch.WordTrace]
  refine ⟨122604852673776388015112899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163473136898368517353483865 122604852673776388015112899)
  ·
    refine ⟨183907279010664582022669349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122604852673776388015112899 183907279010664582022669349)
    ·
      refine ⟨34482614814499609129250503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 183907279010664582022669349 34482614814499609129250503)
      ·
        refine ⟨51723922221749413693875755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34482614814499609129250503 51723922221749413693875755)
        ·
          refine ⟨77585883332624120540813633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51723922221749413693875755 77585883332624120540813633)
          ·
            refine ⟨58189412499468090405610225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77585883332624120540813633 58189412499468090405610225)
            ·
              refine ⟨43642059374601067804207669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58189412499468090405610225 43642059374601067804207669)
              ·
                refine ⟨4091443066368850106644469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43642059374601067804207669 4091443066368850106644469)
                ·
                  refine ⟨383572787472079697497919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4091443066368850106644469 383572787472079697497919)
                  ·
                    rfl

theorem cell23_6723048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 5, 5].length) (baseStart_6723048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6723048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6723048 prefixEnd_6723048 := by exact prefixLift 6723048
  have htrace : WordTrace (prefixWord ++ tailWord_6723048) baseStart_6723048 baseEnd_6723048 := by
    simpa [prefixWord, tailWord_6723048, baseEnd_6723048] using wordTrace_append hprefix tailTrace_6723048
  have hstable : (prefixWord ++ tailWord_6723048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6723048).length < 2 ^ (prefixWord ++ tailWord_6723048).sum := by decide
  have hdescent : baseEnd_6723048 < baseStart_6723048 := by decide
  rcases family_descends (prefixWord ++ tailWord_6723048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6723068 : List Nat := [2, 2, 2, 1, 2, 1, 3, 1, 2, 5, 2]
def baseStart_6723068 : Nat := 118140960795 + 6723068 * 2 ^ 59
def prefixEnd_6723068 : Nat := 4983230072969 + 3 ^ 40 * 6723068 * 2
def baseEnd_6723068 : Nat := 3452165356861807199231179

theorem tailTrace_6723068 : CollatzResearch.WordTrace tailWord_6723068 prefixEnd_6723068 3452165356861807199231179 := by
  unfold tailWord_6723068
  simp only [CollatzResearch.WordTrace]
  refine ⟨122605217403740159722976929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163473623204986879630635905 122605217403740159722976929)
  ·
    refine ⟨91953913052805119792232697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122605217403740159722976929 91953913052805119792232697)
    ·
      refine ⟨68965434789603839844174523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91953913052805119792232697 68965434789603839844174523)
      ·
        refine ⟨103448152184405759766261785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68965434789603839844174523 103448152184405759766261785)
        ·
          refine ⟨77586114138304319824696339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103448152184405759766261785 77586114138304319824696339)
          ·
            refine ⟨116379171207456479737044509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77586114138304319824696339 116379171207456479737044509)
            ·
              refine ⟨43642189202796179901391691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 116379171207456479737044509 43642189202796179901391691)
              ·
                refine ⟨65463283804194269852087537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43642189202796179901391691 65463283804194269852087537)
                ·
                  refine ⟨49097462853145702389065653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65463283804194269852087537 49097462853145702389065653)
                  ·
                    refine ⟨4602887142482409598974905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49097462853145702389065653 4602887142482409598974905)
                    ·
                      refine ⟨3452165356861807199231179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4602887142482409598974905 3452165356861807199231179)
                      ·
                        rfl

theorem cell23_6723068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 1, 2, 5, 2].length) (baseStart_6723068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6723068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6723068 prefixEnd_6723068 := by exact prefixLift 6723068
  have htrace : WordTrace (prefixWord ++ tailWord_6723068) baseStart_6723068 baseEnd_6723068 := by
    simpa [prefixWord, tailWord_6723068, baseEnd_6723068] using wordTrace_append hprefix tailTrace_6723068
  have hstable : (prefixWord ++ tailWord_6723068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6723068).length < 2 ^ (prefixWord ++ tailWord_6723068).sum := by decide
  have hdescent : baseEnd_6723068 < baseStart_6723068 := by decide
  rcases family_descends (prefixWord ++ tailWord_6723068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6723081 : List Nat := [1, 2, 1, 1, 3, 1, 4, 2, 1, 3, 4]
def baseStart_6723081 : Nat := 118140960795 + 6723081 * 2 ^ 59
def prefixEnd_6723081 : Nat := 4983230072969 + 3 ^ 40 * 6723081 * 2
def baseEnd_6723081 : Nat := 3452172032110315648368619

theorem tailTrace_6723081 : CollatzResearch.WordTrace tailWord_6723081 prefixEnd_6723081 3452172032110315648368619 := by
  unfold tailWord_6723081
  simp only [CollatzResearch.WordTrace]
  refine ⟨245210908956433222666177097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163473939304288815110784731 245210908956433222666177097)
  ·
    refine ⟨183908181717324916999632823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245210908956433222666177097 183908181717324916999632823)
    ·
      refine ⟨275862272575987375499449235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183908181717324916999632823 275862272575987375499449235)
      ·
        refine ⟨413793408863981063249173853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275862272575987375499449235 413793408863981063249173853)
        ·
          refine ⟨155172528323992898718440195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 413793408863981063249173853 155172528323992898718440195)
          ·
            refine ⟨232758792485989348077660293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155172528323992898718440195 232758792485989348077660293)
            ·
              refine ⟨43642273591123002764561305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 232758792485989348077660293 43642273591123002764561305)
              ·
                refine ⟨32731705193342252073420979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43642273591123002764561305 32731705193342252073420979)
                ·
                  refine ⟨49097557790013378110131469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32731705193342252073420979 49097557790013378110131469)
                  ·
                    refine ⟨18411584171255016791299301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49097557790013378110131469 18411584171255016791299301)
                    ·
                      refine ⟨3452172032110315648368619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18411584171255016791299301 3452172032110315648368619)
                      ·
                        rfl

theorem cell23_6723081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 2, 1, 3, 4].length) (baseStart_6723081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6723081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6723081 prefixEnd_6723081 := by exact prefixLift 6723081
  have htrace : WordTrace (prefixWord ++ tailWord_6723081) baseStart_6723081 baseEnd_6723081 := by
    simpa [prefixWord, tailWord_6723081, baseEnd_6723081] using wordTrace_append hprefix tailTrace_6723081
  have hstable : (prefixWord ++ tailWord_6723081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6723081).length < 2 ^ (prefixWord ++ tailWord_6723081).sum := by decide
  have hdescent : baseEnd_6723081 < baseStart_6723081 := by decide
  rcases family_descends (prefixWord ++ tailWord_6723081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6723098 : List Nat := [3, 1, 1, 3, 1, 1, 1, 1, 3, 6, 2]
def baseStart_6723098 : Nat := 118140960795 + 6723098 * 2 ^ 59
def prefixEnd_6723098 : Nat := 4983230072969 + 3 ^ 40 * 6723098 * 2
def baseEnd_6723098 : Nat := 3452180761281442081856041

theorem tailTrace_6723098 : CollatzResearch.WordTrace tailWord_6723098 prefixEnd_6723098 3452180761281442081856041 := by
  unfold tailWord_6723098
  simp only [CollatzResearch.WordTrace]
  refine ⟨61302882249342908642386487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163474352664914423046363965 61302882249342908642386487)
  ·
    refine ⟨91954323374014362963579731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61302882249342908642386487 91954323374014362963579731)
    ·
      refine ⟨137931485061021544445369597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91954323374014362963579731 137931485061021544445369597)
      ·
        refine ⟨51724306897883079167013599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137931485061021544445369597 51724306897883079167013599)
        ·
          refine ⟨77586460346824618750520399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51724306897883079167013599 77586460346824618750520399)
          ·
            refine ⟨116379690520236928125780599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77586460346824618750520399 116379690520236928125780599)
            ·
              refine ⟨174569535780355392188670899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116379690520236928125780599 174569535780355392188670899)
              ·
                refine ⟨261854303670533088283006349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 174569535780355392188670899 261854303670533088283006349)
                ·
                  refine ⟨98195363876449908106127381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 261854303670533088283006349 98195363876449908106127381)
                  ·
                    refine ⟨4602907681708589442474721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 98195363876449908106127381 4602907681708589442474721)
                    ·
                      refine ⟨3452180761281442081856041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4602907681708589442474721 3452180761281442081856041)
                      ·
                        rfl

theorem cell23_6723098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 1, 3, 6, 2].length) (baseStart_6723098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6723098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6723098 prefixEnd_6723098 := by exact prefixLift 6723098
  have htrace : WordTrace (prefixWord ++ tailWord_6723098) baseStart_6723098 baseEnd_6723098 := by
    simpa [prefixWord, tailWord_6723098, baseEnd_6723098] using wordTrace_append hprefix tailTrace_6723098
  have hstable : (prefixWord ++ tailWord_6723098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6723098).length < 2 ^ (prefixWord ++ tailWord_6723098).sum := by decide
  have hdescent : baseEnd_6723098 < baseStart_6723098 := by decide
  rcases family_descends (prefixWord ++ tailWord_6723098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6723125 : List Nat := [1, 3, 3, 1, 1, 4, 2, 1, 3, 4]
def baseStart_6723125 : Nat := 118140960795 + 6723125 * 2 ^ 59
def prefixEnd_6723125 : Nat := 4983230072969 + 3 ^ 40 * 6723125 * 2
def baseEnd_6723125 : Nat := 1150731541753037825406139

theorem tailTrace_6723125 : CollatzResearch.WordTrace tailWord_6723125 prefixEnd_6723125 1150731541753037825406139 := by
  unfold tailWord_6723125
  simp only [CollatzResearch.WordTrace]
  refine ⟨245212513768273818180778829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163475009178849212120519219 245212513768273818180778829)
  ·
    refine ⟨91954692663102681817792061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 245212513768273818180778829 91954692663102681817792061)
    ·
      refine ⟨34483009748663505681672023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91954692663102681817792061 34483009748663505681672023)
      ·
        refine ⟨51724514622995258522508035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34483009748663505681672023 51724514622995258522508035)
        ·
          refine ⟨77586771934492887783762053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51724514622995258522508035 77586771934492887783762053)
          ·
            refine ⟨14547519737717416459455385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 77586771934492887783762053 14547519737717416459455385)
            ·
              refine ⟨10910639803288062344591539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14547519737717416459455385 10910639803288062344591539)
              ·
                refine ⟨16365959704932093516887309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10910639803288062344591539 16365959704932093516887309)
                ·
                  refine ⟨6137234889349535068832741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16365959704932093516887309 6137234889349535068832741)
                  ·
                    refine ⟨1150731541753037825406139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6137234889349535068832741 1150731541753037825406139)
                    ·
                      rfl

theorem cell23_6723125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 2, 1, 3, 4].length) (baseStart_6723125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6723125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6723125 prefixEnd_6723125 := by exact prefixLift 6723125
  have htrace : WordTrace (prefixWord ++ tailWord_6723125) baseStart_6723125 baseEnd_6723125 := by
    simpa [prefixWord, tailWord_6723125, baseEnd_6723125] using wordTrace_append hprefix tailTrace_6723125
  have hstable : (prefixWord ++ tailWord_6723125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6723125).length < 2 ^ (prefixWord ++ tailWord_6723125).sum := by decide
  have hdescent : baseEnd_6723125 < baseStart_6723125 := by decide
  rcases family_descends (prefixWord ++ tailWord_6723125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6723141 : List Nat := [1, 3, 1, 1, 1, 4, 1, 2, 1, 2, 6]
def baseStart_6723141 : Nat := 118140960795 + 6723141 * 2 ^ 59
def prefixEnd_6723141 : Nat := 4983230072969 + 3 ^ 40 * 6723141 * 2
def baseEnd_6723141 : Nat := 3452202840949585413618343

theorem tailTrace_6723141 : CollatzResearch.WordTrace tailWord_6723141 prefixEnd_6723141 3452202840949585413618343 := by
  unfold tailWord_6723141
  simp only [CollatzResearch.WordTrace]
  refine ⟨245213097336215852913361277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163475398224143901942240851 245213097336215852913361277)
  ·
    refine ⟨91954911501080944842510479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 245213097336215852913361277 91954911501080944842510479)
    ·
      refine ⟨137932367251621417263765719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91954911501080944842510479 137932367251621417263765719)
      ·
        refine ⟨206898550877432125895648579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137932367251621417263765719 206898550877432125895648579)
        ·
          refine ⟨310347826316148188843472869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206898550877432125895648579 310347826316148188843472869)
          ·
            refine ⟨58190217434277785408151163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 310347826316148188843472869 58190217434277785408151163)
            ·
              refine ⟨87285326151416678112226745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58190217434277785408151163 87285326151416678112226745)
              ·
                refine ⟨65463994613562508584170059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87285326151416678112226745 65463994613562508584170059)
                ·
                  refine ⟨98195991920343762876255089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65463994613562508584170059 98195991920343762876255089)
                  ·
                    refine ⟨73646993940257822157191317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 98195991920343762876255089 73646993940257822157191317)
                    ·
                      refine ⟨3452202840949585413618343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 73646993940257822157191317 3452202840949585413618343)
                      ·
                        rfl

theorem cell23_6723141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 2, 1, 2, 6].length) (baseStart_6723141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6723141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6723141 prefixEnd_6723141 := by exact prefixLift 6723141
  have htrace : WordTrace (prefixWord ++ tailWord_6723141) baseStart_6723141 baseEnd_6723141 := by
    simpa [prefixWord, tailWord_6723141, baseEnd_6723141] using wordTrace_append hprefix tailTrace_6723141
  have hstable : (prefixWord ++ tailWord_6723141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6723141).length < 2 ^ (prefixWord ++ tailWord_6723141).sum := by decide
  have hdescent : baseEnd_6723141 < baseStart_6723141 := by decide
  rcases family_descends (prefixWord ++ tailWord_6723141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6723175 : List Nat := [1, 1, 5, 1, 1, 1, 3, 1, 4, 3, 2]
def baseStart_6723175 : Nat := 118140960795 + 6723175 * 2 ^ 59
def prefixEnd_6723175 : Nat := 4983230072969 + 3 ^ 40 * 6723175 * 2
def baseEnd_6723175 : Nat := 3452220299291838280593187

theorem tailTrace_6723175 : CollatzResearch.WordTrace tailWord_6723175 prefixEnd_6723175 3452220299291838280593187 := by
  unfold tailWord_6723175
  simp only [CollatzResearch.WordTrace]
  refine ⟨245214337418092676720098979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163476224945395117813399319 245214337418092676720098979)
  ·
    refine ⟨367821506127139015080148469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245214337418092676720098979 367821506127139015080148469)
    ·
      refine ⟨34483266199419282663763919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 367821506127139015080148469 34483266199419282663763919)
      ·
        refine ⟨51724899299128923995645879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34483266199419282663763919 51724899299128923995645879)
        ·
          refine ⟨77587348948693385993468819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51724899299128923995645879 77587348948693385993468819)
          ·
            refine ⟨116381023423040078990203229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77587348948693385993468819 116381023423040078990203229)
            ·
              refine ⟨43642883783640029621326211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 116381023423040078990203229 43642883783640029621326211)
              ·
                refine ⟨65464325675460044431989317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43642883783640029621326211 65464325675460044431989317)
                ·
                  refine ⟨12274561064148758330997997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65464325675460044431989317 12274561064148758330997997)
                  ·
                    refine ⟨4602960399055784374124249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12274561064148758330997997 4602960399055784374124249)
                    ·
                      refine ⟨3452220299291838280593187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4602960399055784374124249 3452220299291838280593187)
                      ·
                        rfl

theorem cell23_6723175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 1, 4, 3, 2].length) (baseStart_6723175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6723175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6723175 prefixEnd_6723175 := by exact prefixLift 6723175
  have htrace : WordTrace (prefixWord ++ tailWord_6723175) baseStart_6723175 baseEnd_6723175 := by
    simpa [prefixWord, tailWord_6723175, baseEnd_6723175] using wordTrace_append hprefix tailTrace_6723175
  have hstable : (prefixWord ++ tailWord_6723175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6723175).length < 2 ^ (prefixWord ++ tailWord_6723175).sum := by decide
  have hdescent : baseEnd_6723175 < baseStart_6723175 := by decide
  rcases family_descends (prefixWord ++ tailWord_6723175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6723211 : List Nat := [1, 1, 1, 1, 4, 1, 3, 11]
def baseStart_6723211 : Nat := 118140960795 + 6723211 * 2 ^ 59
def prefixEnd_6723211 : Nat := 4983230072969 + 3 ^ 40 * 6723211 * 2
def baseEnd_6723211 : Nat := 127860695725755560731223

theorem tailTrace_6723211 : CollatzResearch.WordTrace tailWord_6723211 prefixEnd_6723211 127860695725755560731223 := by
  unfold tailWord_6723211
  simp only [CollatzResearch.WordTrace]
  refine ⟨245215650445962254868409487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163477100297308169912272991 245215650445962254868409487)
  ·
    refine ⟨367823475668943382302614231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245215650445962254868409487 367823475668943382302614231)
    ·
      refine ⟨551735213503415073453921347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 367823475668943382302614231 551735213503415073453921347)
      ·
        refine ⟨827602820255122610180882021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 551735213503415073453921347 827602820255122610180882021)
        ·
          refine ⟨155175528797835489408915379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 827602820255122610180882021 155175528797835489408915379)
          ·
            refine ⟨232763293196753234113373069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155175528797835489408915379 232763293196753234113373069)
            ·
              refine ⟨87286234948782462792514901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 232763293196753234113373069 87286234948782462792514901)
              ·
                refine ⟨127860695725755560731223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 87286234948782462792514901 127860695725755560731223)
                ·
                  rfl

theorem cell23_6723211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 11].length) (baseStart_6723211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6723211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6723211 prefixEnd_6723211 := by exact prefixLift 6723211
  have htrace : WordTrace (prefixWord ++ tailWord_6723211) baseStart_6723211 baseEnd_6723211 := by
    simpa [prefixWord, tailWord_6723211, baseEnd_6723211] using wordTrace_append hprefix tailTrace_6723211
  have hstable : (prefixWord ++ tailWord_6723211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6723211).length < 2 ^ (prefixWord ++ tailWord_6723211).sum := by decide
  have hdescent : baseEnd_6723211 < baseStart_6723211 := by decide
  rcases family_descends (prefixWord ++ tailWord_6723211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6723228 : List Nat := [2, 2, 3, 2, 3, 11]
def baseStart_6723228 : Nat := 118140960795 + 6723228 * 2 ^ 59
def prefixEnd_6723228 : Nat := 4983230072969 + 3 ^ 40 * 6723228 * 2
def baseEnd_6723228 : Nat := 14206779892043319231401

theorem tailTrace_6723228 : CollatzResearch.WordTrace tailWord_6723228 prefixEnd_6723228 14206779892043319231401 := by
  unfold tailWord_6723228
  simp only [CollatzResearch.WordTrace]
  refine ⟨122608135243450333385889169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163477513657933777847852225 122608135243450333385889169)
  ·
    refine ⟨91956101432587750039416877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122608135243450333385889169 91956101432587750039416877)
    ·
      refine ⟨34483538037220406264781329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91956101432587750039416877 34483538037220406264781329)
      ·
        refine ⟨25862653527915304698585997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34483538037220406264781329 25862653527915304698585997)
        ·
          refine ⟨9698495072968239261969749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25862653527915304698585997 9698495072968239261969749)
          ·
            refine ⟨14206779892043319231401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 9698495072968239261969749 14206779892043319231401)
            ·
              rfl

theorem cell23_6723228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 11].length) (baseStart_6723228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6723228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6723228 prefixEnd_6723228 := by exact prefixLift 6723228
  have htrace : WordTrace (prefixWord ++ tailWord_6723228) baseStart_6723228 baseEnd_6723228 := by
    simpa [prefixWord, tailWord_6723228, baseEnd_6723228] using wordTrace_append hprefix tailTrace_6723228
  have hstable : (prefixWord ++ tailWord_6723228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6723228).length < 2 ^ (prefixWord ++ tailWord_6723228).sum := by decide
  have hdescent : baseEnd_6723228 < baseStart_6723228 := by decide
  rcases family_descends (prefixWord ++ tailWord_6723228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
