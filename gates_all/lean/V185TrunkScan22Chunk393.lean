import V185TrunkScan22Chunk392

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_3505659 : List Nat := [1, 1, 1, 1, 1, 3, 2, 4, 5, 3]
def baseStart_3505659 : Nat := 118140960795 + 3505659 * 2 ^ 59
def prefixEnd_3505659 : Nat := 4983230072969 + 3 ^ 40 * 3505659 * 2
def baseEnd_3505659 : Nat := 1200058718506803217826849

theorem tailTrace_3505659 : CollatzResearch.WordTrace tailWord_3505659 prefixEnd_3505659 1200058718506803217826849 := by
  unfold tailWord_3505659
  simp only [CollatzResearch.WordTrace]
  refine ⟨127861888006603636735864031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85241258671069091157242687 127861888006603636735864031)
  ·
    refine ⟨191792832009905455103796047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127861888006603636735864031 191792832009905455103796047)
    ·
      refine ⟨287689248014858182655694071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191792832009905455103796047 287689248014858182655694071)
      ·
        refine ⟨431533872022287273983541107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287689248014858182655694071 431533872022287273983541107)
        ·
          refine ⟨647300808033430910975311661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 431533872022287273983541107 647300808033430910975311661)
          ·
            refine ⟨242737803012536591615741873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 647300808033430910975311661 242737803012536591615741873)
            ·
              refine ⟨182053352259402443711806405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 242737803012536591615741873 182053352259402443711806405)
              ·
                refine ⟨34135003548637958195963701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 182053352259402443711806405 34135003548637958195963701)
                ·
                  refine ⟨3200156582684808580871597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34135003548637958195963701 3200156582684808580871597)
                  ·
                    refine ⟨1200058718506803217826849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3200156582684808580871597 1200058718506803217826849)
                    ·
                      rfl

theorem cell22_3505659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 4, 5, 3].length) (baseStart_3505659 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3505659 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3505659 prefixEnd_3505659 := by exact prefixLift 3505659
  have htrace : WordTrace (prefixWord ++ tailWord_3505659) baseStart_3505659 baseEnd_3505659 := by
    simpa [prefixWord, tailWord_3505659, baseEnd_3505659] using wordTrace_append hprefix tailTrace_3505659
  have hstable : (prefixWord ++ tailWord_3505659).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3505659).length < 2 ^ (prefixWord ++ tailWord_3505659).sum := by decide
  have hdescent : baseEnd_3505659 < baseStart_3505659 := by decide
  rcases family_descends (prefixWord ++ tailWord_3505659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3505674 : List Nat := [3, 1, 2, 2, 2, 2, 1, 1, 2, 6]
def baseStart_3505674 : Nat := 118140960795 + 3505674 * 2 ^ 59
def prefixEnd_3505674 : Nat := 4983230072969 + 3 ^ 40 * 3505674 * 2
def baseEnd_3505674 : Nat := 1200063853313348178701803

theorem tailTrace_3505674 : CollatzResearch.WordTrace tailWord_3505674 prefixEnd_3505674 1200063853313348178701803 := by
  unfold tailWord_3505674
  simp only [CollatzResearch.WordTrace]
  refine ⟨31965608775387323574415019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85241623401032862865106717 31965608775387323574415019)
  ·
    refine ⟨47948413163080985361622529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31965608775387323574415019 47948413163080985361622529)
    ·
      refine ⟨35961309872310739021216897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47948413163080985361622529 35961309872310739021216897)
      ·
        refine ⟨26970982404233054265912673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35961309872310739021216897 26970982404233054265912673)
        ·
          refine ⟨20228236803174790699434505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26970982404233054265912673 20228236803174790699434505)
          ·
            refine ⟨15171177602381093024575879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20228236803174790699434505 15171177602381093024575879)
            ·
              refine ⟨22756766403571639536863819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15171177602381093024575879 22756766403571639536863819)
              ·
                refine ⟨34135149605357459305295729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22756766403571639536863819 34135149605357459305295729)
                ·
                  refine ⟨25601362204018094478971797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34135149605357459305295729 25601362204018094478971797)
                  ·
                    refine ⟨1200063853313348178701803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25601362204018094478971797 1200063853313348178701803)
                    ·
                      rfl

theorem cell22_3505674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 1, 2, 6].length) (baseStart_3505674 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3505674 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3505674 prefixEnd_3505674 := by exact prefixLift 3505674
  have htrace : WordTrace (prefixWord ++ tailWord_3505674) baseStart_3505674 baseEnd_3505674 := by
    simpa [prefixWord, tailWord_3505674, baseEnd_3505674] using wordTrace_append hprefix tailTrace_3505674
  have hstable : (prefixWord ++ tailWord_3505674).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3505674).length < 2 ^ (prefixWord ++ tailWord_3505674).sum := by decide
  have hdescent : baseEnd_3505674 < baseStart_3505674 := by decide
  rcases family_descends (prefixWord ++ tailWord_3505674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3505678 : List Nat := [4, 1, 1, 2, 5, 1, 1, 7]
def baseStart_3505678 : Nat := 118140960795 + 3505678 * 2 ^ 59
def prefixEnd_3505678 : Nat := 4983230072969 + 3 ^ 40 * 3505678 * 2
def baseEnd_3505678 : Nat := 133340580288343722400199

theorem tailTrace_3505678 : CollatzResearch.WordTrace tailWord_3505678 prefixEnd_3505678 133340580288343722400199 := by
  unfold tailWord_3505678
  simp only [CollatzResearch.WordTrace]
  refine ⟨15982822624191850372600711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85241720662356535320537125 15982822624191850372600711)
  ·
    refine ⟨23974233936287775558901067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15982822624191850372600711 23974233936287775558901067)
    ·
      refine ⟨35961350904431663338351601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23974233936287775558901067 35961350904431663338351601)
      ·
        refine ⟨26971013178323747503763701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35961350904431663338351601 26971013178323747503763701)
        ·
          refine ⟨2528532485467851328477847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26971013178323747503763701 2528532485467851328477847)
          ·
            refine ⟨3792798728201776992716771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2528532485467851328477847 3792798728201776992716771)
            ·
              refine ⟨5689198092302665489075157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3792798728201776992716771 5689198092302665489075157)
              ·
                refine ⟨133340580288343722400199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5689198092302665489075157 133340580288343722400199)
                ·
                  rfl

theorem cell22_3505678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 1, 7].length) (baseStart_3505678 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3505678 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3505678 prefixEnd_3505678 := by exact prefixLift 3505678
  have htrace : WordTrace (prefixWord ++ tailWord_3505678) baseStart_3505678 baseEnd_3505678 := by
    simpa [prefixWord, tailWord_3505678, baseEnd_3505678] using wordTrace_append hprefix tailTrace_3505678
  have hstable : (prefixWord ++ tailWord_3505678).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3505678).length < 2 ^ (prefixWord ++ tailWord_3505678).sum := by decide
  have hdescent : baseEnd_3505678 < baseStart_3505678 := by decide
  rcases family_descends (prefixWord ++ tailWord_3505678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3505710 : List Nat := [4, 1, 3, 1, 2, 1, 1, 5, 1, 3]
def baseStart_3505710 : Nat := 118140960795 + 3505710 * 2 ^ 59
def prefixEnd_3505710 : Nat := 4983230072969 + 3 ^ 40 * 3505710 * 2
def baseEnd_3505710 : Nat := 1200076176849056084801693

theorem tailTrace_3505710 : CollatzResearch.WordTrace tailWord_3505710 prefixEnd_3505710 1200076176849056084801693 := by
  unfold tailWord_3505710
  simp only [CollatzResearch.WordTrace]
  refine ⟨15982968516177359055746323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85242498752945914963980389 15982968516177359055746323)
  ·
    refine ⟨23974452774266038583619485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15982968516177359055746323 23974452774266038583619485)
    ·
      refine ⟨8990419790349764468857307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23974452774266038583619485 8990419790349764468857307)
      ·
        refine ⟨13485629685524646703285961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8990419790349764468857307 13485629685524646703285961)
        ·
          refine ⟨10114222264143485027464471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13485629685524646703285961 10114222264143485027464471)
          ·
            refine ⟨15171333396215227541196707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10114222264143485027464471 15171333396215227541196707)
            ·
              refine ⟨22757000094322841311795061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15171333396215227541196707 22757000094322841311795061)
              ·
                refine ⟨2133468758842766372980787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22757000094322841311795061 2133468758842766372980787)
                ·
                  refine ⟨3200203138264149559471181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2133468758842766372980787 3200203138264149559471181)
                  ·
                    refine ⟨1200076176849056084801693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3200203138264149559471181 1200076176849056084801693)
                    ·
                      rfl

theorem cell22_3505710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 5, 1, 3].length) (baseStart_3505710 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3505710 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3505710 prefixEnd_3505710 := by exact prefixLift 3505710
  have htrace : WordTrace (prefixWord ++ tailWord_3505710) baseStart_3505710 baseEnd_3505710 := by
    simpa [prefixWord, tailWord_3505710, baseEnd_3505710] using wordTrace_append hprefix tailTrace_3505710
  have hstable : (prefixWord ++ tailWord_3505710).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3505710).length < 2 ^ (prefixWord ++ tailWord_3505710).sum := by decide
  have hdescent : baseEnd_3505710 < baseStart_3505710 := by decide
  rcases family_descends (prefixWord ++ tailWord_3505710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3505809 : List Nat := [1, 2, 2, 1, 1, 1, 1, 3, 4, 6]
def baseStart_3505809 : Nat := 118140960795 + 3505809 * 2 ^ 59
def prefixEnd_3505809 : Nat := 4983230072969 + 3 ^ 40 * 3505809 * 2
def baseEnd_3505809 : Nat := 1200110066572252826576389

theorem tailTrace_3505809 : CollatzResearch.WordTrace tailWord_3505809 prefixEnd_3505809 1200110066572252826576389 := by
  unfold tailWord_3505809
  simp only [CollatzResearch.WordTrace]
  refine ⟨127867358956060212353824481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85244905970706808235882987 127867358956060212353824481)
  ·
    refine ⟨95900519217045159265368361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127867358956060212353824481 95900519217045159265368361)
    ·
      refine ⟨71925389412783869449026271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95900519217045159265368361 71925389412783869449026271)
      ·
        refine ⟨107888084119175804173539407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71925389412783869449026271 107888084119175804173539407)
        ·
          refine ⟨161832126178763706260309111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107888084119175804173539407 161832126178763706260309111)
          ·
            refine ⟨242748189268145559390463667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161832126178763706260309111 242748189268145559390463667)
            ·
              refine ⟨364122283902218339085695501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 242748189268145559390463667 364122283902218339085695501)
              ·
                refine ⟨136545856463331877157135813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 364122283902218339085695501 136545856463331877157135813)
                ·
                  refine ⟨25602348086874726966962965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 136545856463331877157135813 25602348086874726966962965)
                  ·
                    refine ⟨1200110066572252826576389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25602348086874726966962965 1200110066572252826576389)
                    ·
                      rfl

theorem cell22_3505809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 6].length) (baseStart_3505809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3505809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3505809 prefixEnd_3505809 := by exact prefixLift 3505809
  have htrace : WordTrace (prefixWord ++ tailWord_3505809) baseStart_3505809 baseEnd_3505809 := by
    simpa [prefixWord, tailWord_3505809, baseEnd_3505809] using wordTrace_append hprefix tailTrace_3505809
  have hstable : (prefixWord ++ tailWord_3505809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3505809).length < 2 ^ (prefixWord ++ tailWord_3505809).sum := by decide
  have hdescent : baseEnd_3505809 < baseStart_3505809 := by decide
  rcases family_descends (prefixWord ++ tailWord_3505809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3505856 : List Nat := [2, 1, 1, 2, 4, 1, 3, 1, 2, 5]
def baseStart_3505856 : Nat := 118140960795 + 3505856 * 2 ^ 59
def prefixEnd_3505856 : Nat := 4983230072969 + 3 ^ 40 * 3505856 * 2
def baseEnd_3505856 : Nat := 1200126155632760370651245

theorem tailTrace_3505856 : CollatzResearch.WordTrace tailWord_3505856 prefixEnd_3505856 1200126155632760370651245 := by
  unfold tailWord_3505856
  simp only [CollatzResearch.WordTrace]
  refine ⟨63934536593444969690392711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85246048791259959587190281 63934536593444969690392711)
  ·
    refine ⟨95901804890167454535589067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63934536593444969690392711 95901804890167454535589067)
    ·
      refine ⟨143852707335251181803383601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95901804890167454535589067 143852707335251181803383601)
      ·
        refine ⟨107889530501438386352537701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143852707335251181803383601 107889530501438386352537701)
        ·
          refine ⟨20229286969019697441100819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 107889530501438386352537701 20229286969019697441100819)
          ·
            refine ⟨30343930453529546161651229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20229286969019697441100819 30343930453529546161651229)
            ·
              refine ⟨11378973920073579810619211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30343930453529546161651229 11378973920073579810619211)
              ·
                refine ⟨17068460880110369715928817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11378973920073579810619211 17068460880110369715928817)
                ·
                  refine ⟨12801345660082777286946613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17068460880110369715928817 12801345660082777286946613)
                  ·
                    refine ⟨1200126155632760370651245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12801345660082777286946613 1200126155632760370651245)
                    ·
                      rfl

theorem cell22_3505856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 1, 2, 5].length) (baseStart_3505856 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3505856 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3505856 prefixEnd_3505856 := by exact prefixLift 3505856
  have htrace : WordTrace (prefixWord ++ tailWord_3505856) baseStart_3505856 baseEnd_3505856 := by
    simpa [prefixWord, tailWord_3505856, baseEnd_3505856] using wordTrace_append hprefix tailTrace_3505856
  have hstable : (prefixWord ++ tailWord_3505856).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3505856).length < 2 ^ (prefixWord ++ tailWord_3505856).sum := by decide
  have hdescent : baseEnd_3505856 < baseStart_3505856 := by decide
  rcases family_descends (prefixWord ++ tailWord_3505856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3505862 : List Nat := [6, 1, 2, 1, 1, 1, 1, 1, 5, 3]
def baseStart_3505862 : Nat := 118140960795 + 3505862 * 2 ^ 59
def prefixEnd_3505862 : Nat := 4983230072969 + 3 ^ 40 * 3505862 * 2
def baseEnd_3505862 : Nat := 1200128209555378355001227

theorem tailTrace_3505862 : CollatzResearch.WordTrace tailWord_3505862 prefixEnd_3505862 1200128209555378355001227 := by
  unfold tailWord_3505862
  simp only [CollatzResearch.WordTrace]
  refine ⟨3995915375777131325171995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 85246194683245468270335893 3995915375777131325171995)
  ·
    refine ⟨5993873063665696987757993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3995915375777131325171995 5993873063665696987757993)
    ·
      refine ⟨4495404797749272740818495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5993873063665696987757993 4495404797749272740818495)
      ·
        refine ⟨6743107196623909111227743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4495404797749272740818495 6743107196623909111227743)
        ·
          refine ⟨10114660794935863666841615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6743107196623909111227743 10114660794935863666841615)
          ·
            refine ⟨15171991192403795500262423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10114660794935863666841615 15171991192403795500262423)
            ·
              refine ⟨22757986788605693250393635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15171991192403795500262423 22757986788605693250393635)
              ·
                refine ⟨34136980182908539875590453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22757986788605693250393635 34136980182908539875590453)
                ·
                  refine ⟨3200341892147675613336605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34136980182908539875590453 3200341892147675613336605)
                  ·
                    refine ⟨1200128209555378355001227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3200341892147675613336605 1200128209555378355001227)
                    ·
                      rfl

theorem cell22_3505862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 1, 5, 3].length) (baseStart_3505862 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3505862 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3505862 prefixEnd_3505862 := by exact prefixLift 3505862
  have htrace : WordTrace (prefixWord ++ tailWord_3505862) baseStart_3505862 baseEnd_3505862 := by
    simpa [prefixWord, tailWord_3505862, baseEnd_3505862] using wordTrace_append hprefix tailTrace_3505862
  have hstable : (prefixWord ++ tailWord_3505862).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3505862).length < 2 ^ (prefixWord ++ tailWord_3505862).sum := by decide
  have hdescent : baseEnd_3505862 < baseStart_3505862 := by decide
  rcases family_descends (prefixWord ++ tailWord_3505862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3505903 : List Nat := [1, 1, 2, 1, 5, 1, 1, 6, 4]
def baseStart_3505903 : Nat := 118140960795 + 3505903 * 2 ^ 59
def prefixEnd_3505903 : Nat := 4983230072969 + 3 ^ 40 * 3505903 * 2
def baseEnd_3505903 : Nat := 400047414897755971575367

theorem tailTrace_3505903 : CollatzResearch.WordTrace tailWord_3505903 prefixEnd_3505903 400047414897755971575367 := by
  unfold tailWord_3505903
  simp only [CollatzResearch.WordTrace]
  refine ⟨127870787417719666407746363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85247191611813110938497575 127870787417719666407746363)
  ·
    refine ⟨191806181126579499611619545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127870787417719666407746363 191806181126579499611619545)
    ·
      refine ⟨143854635844934624708714659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191806181126579499611619545 143854635844934624708714659)
      ·
        refine ⟨215781953767401937063071989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143854635844934624708714659 215781953767401937063071989)
        ·
          refine ⟨20229558165693931599662999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 215781953767401937063071989 20229558165693931599662999)
          ·
            refine ⟨30344337248540897399494499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20229558165693931599662999 30344337248540897399494499)
            ·
              refine ⟨45516505872811346099241749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30344337248540897399494499 45516505872811346099241749)
              ·
                refine ⟨2133586212788031848401957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 45516505872811346099241749 2133586212788031848401957)
                ·
                  refine ⟨400047414897755971575367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2133586212788031848401957 400047414897755971575367)
                  ·
                    rfl

theorem cell22_3505903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 6, 4].length) (baseStart_3505903 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3505903 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3505903 prefixEnd_3505903 := by exact prefixLift 3505903
  have htrace : WordTrace (prefixWord ++ tailWord_3505903) baseStart_3505903 baseEnd_3505903 := by
    simpa [prefixWord, tailWord_3505903, baseEnd_3505903] using wordTrace_append hprefix tailTrace_3505903
  have hstable : (prefixWord ++ tailWord_3505903).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3505903).length < 2 ^ (prefixWord ++ tailWord_3505903).sum := by decide
  have hdescent : baseEnd_3505903 < baseStart_3505903 := by decide
  rcases family_descends (prefixWord ++ tailWord_3505903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3505916 : List Nat := [2, 2, 2, 1, 3, 1, 1, 1, 3, 6]
def baseStart_3505916 : Nat := 118140960795 + 3505916 * 2 ^ 59
def prefixEnd_3505916 : Nat := 4983230072969 + 3 ^ 40 * 3505916 * 2
def baseEnd_3505916 : Nat := 1200146694858940214151061

theorem tailTrace_3505916 : CollatzResearch.WordTrace tailWord_3505916 prefixEnd_3505916 1200146694858940214151061 := by
  unfold tailWord_3505916
  simp only [CollatzResearch.WordTrace]
  refine ⟨63935630783336284813984801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85247507711115046418646401 63935630783336284813984801)
  ·
    refine ⟨47951723087502213610488601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63935630783336284813984801 47951723087502213610488601)
    ·
      refine ⟨35963792315626660207866451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47951723087502213610488601 35963792315626660207866451)
      ·
        refine ⟨53945688473439990311799677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35963792315626660207866451 53945688473439990311799677)
        ·
          refine ⟨20229633177539996366924879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53945688473439990311799677 20229633177539996366924879)
          ·
            refine ⟨30344449766309994550387319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20229633177539996366924879 30344449766309994550387319)
            ·
              refine ⟨45516674649464991825580979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30344449766309994550387319 45516674649464991825580979)
              ·
                refine ⟨68275011974197487738371469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45516674649464991825580979 68275011974197487738371469)
                ·
                  refine ⟨25603129490324057901889301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68275011974197487738371469 25603129490324057901889301)
                  ·
                    refine ⟨1200146694858940214151061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25603129490324057901889301 1200146694858940214151061)
                    ·
                      rfl

theorem cell22_3505916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 1, 3, 6].length) (baseStart_3505916 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3505916 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3505916 prefixEnd_3505916 := by exact prefixLift 3505916
  have htrace : WordTrace (prefixWord ++ tailWord_3505916) baseStart_3505916 baseEnd_3505916 := by
    simpa [prefixWord, tailWord_3505916, baseEnd_3505916] using wordTrace_append hprefix tailTrace_3505916
  have hstable : (prefixWord ++ tailWord_3505916).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3505916).length < 2 ^ (prefixWord ++ tailWord_3505916).sum := by decide
  have hdescent : baseEnd_3505916 < baseStart_3505916 := by decide
  rcases family_descends (prefixWord ++ tailWord_3505916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3506023 : List Nat := [1, 1, 5, 1, 2, 1, 1, 1, 5, 4]
def baseStart_3506023 : Nat := 118140960795 + 3506023 * 2 ^ 59
def prefixEnd_3506023 : Nat := 4983230072969 + 3 ^ 40 * 3506023 * 2
def baseEnd_3506023 : Nat := 1200183323145627601725733

theorem tailTrace_3506023 : CollatzResearch.WordTrace tailWord_3506023 prefixEnd_3506023 1200183323145627601725733 := by
  unfold tailWord_3506023
  simp only [CollatzResearch.WordTrace]
  refine ⟨127875164177284926902114723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85250109451523284601409815 127875164177284926902114723)
  ·
    refine ⟨191812746265927390353172085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127875164177284926902114723 191812746265927390353172085)
    ·
      refine ⟨17982444962430692845609883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 191812746265927390353172085 17982444962430692845609883)
      ·
        refine ⟨26973667443646039268414825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17982444962430692845609883 26973667443646039268414825)
        ·
          refine ⟨20230250582734529451311119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26973667443646039268414825 20230250582734529451311119)
          ·
            refine ⟨30345375874101794176966679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20230250582734529451311119 30345375874101794176966679)
            ·
              refine ⟨45518063811152691265450019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30345375874101794176966679 45518063811152691265450019)
              ·
                refine ⟨68277095716729036898175029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45518063811152691265450019 68277095716729036898175029)
                ·
                  refine ⟨6400977723443347209203909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 68277095716729036898175029 6400977723443347209203909)
                  ·
                    refine ⟨1200183323145627601725733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6400977723443347209203909 1200183323145627601725733)
                    ·
                      rfl

theorem cell22_3506023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 1, 5, 4].length) (baseStart_3506023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3506023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3506023 prefixEnd_3506023 := by exact prefixLift 3506023
  have htrace : WordTrace (prefixWord ++ tailWord_3506023) baseStart_3506023 baseEnd_3506023 := by
    simpa [prefixWord, tailWord_3506023, baseEnd_3506023] using wordTrace_append hprefix tailTrace_3506023
  have hstable : (prefixWord ++ tailWord_3506023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3506023).length < 2 ^ (prefixWord ++ tailWord_3506023).sum := by decide
  have hdescent : baseEnd_3506023 < baseStart_3506023 := by decide
  rcases family_descends (prefixWord ++ tailWord_3506023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3506053 : List Nat := [1, 3, 1, 1, 3, 2, 1, 4, 1, 5]
def baseStart_3506053 : Nat := 118140960795 + 3506053 * 2 ^ 59
def prefixEnd_3506053 : Nat := 4983230072969 + 3 ^ 40 * 3506053 * 2
def baseEnd_3506053 : Nat := 1200193592758717523475641

theorem tailTrace_3506053 : CollatzResearch.WordTrace tailWord_3506053 prefixEnd_3506053 1200193592758717523475641 := by
  unfold tailWord_3506053
  simp only [CollatzResearch.WordTrace]
  refine ⟨127876258367176242025706813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85250838911450828017137875 127876258367176242025706813)
  ·
    refine ⟨47953596887691090759640055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127876258367176242025706813 47953596887691090759640055)
    ·
      refine ⟨71930395331536636139460083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47953596887691090759640055 71930395331536636139460083)
      ·
        refine ⟨107895592997304954209190125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71930395331536636139460083 107895592997304954209190125)
        ·
          refine ⟨40460847373989357828446297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107895592997304954209190125 40460847373989357828446297)
          ·
            refine ⟨30345635530492018371334723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40460847373989357828446297 30345635530492018371334723)
            ·
              refine ⟨45518453295738027557002085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30345635530492018371334723 45518453295738027557002085)
              ·
                refine ⟨8534709992950880166937891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45518453295738027557002085 8534709992950880166937891)
                ·
                  refine ⟨12802064989426320250406837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8534709992950880166937891 12802064989426320250406837)
                  ·
                    refine ⟨1200193592758717523475641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12802064989426320250406837 1200193592758717523475641)
                    ·
                      rfl

theorem cell22_3506053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 4, 1, 5].length) (baseStart_3506053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3506053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3506053 prefixEnd_3506053 := by exact prefixLift 3506053
  have htrace : WordTrace (prefixWord ++ tailWord_3506053) baseStart_3506053 baseEnd_3506053 := by
    simpa [prefixWord, tailWord_3506053, baseEnd_3506053] using wordTrace_append hprefix tailTrace_3506053
  have hstable : (prefixWord ++ tailWord_3506053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3506053).length < 2 ^ (prefixWord ++ tailWord_3506053).sum := by decide
  have hdescent : baseEnd_3506053 < baseStart_3506053 := by decide
  rcases family_descends (prefixWord ++ tailWord_3506053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3506072 : List Nat := [2, 1, 2, 6, 1, 1, 2, 1, 6]
def baseStart_3506072 : Nat := 118140960795 + 3506072 * 2 ^ 59
def prefixEnd_3506072 : Nat := 4983230072969 + 3 ^ 40 * 3506072 * 2
def baseEnd_3506072 : Nat := 400066698949002602416861

theorem tailTrace_3506072 : CollatzResearch.WordTrace tailWord_3506072 prefixEnd_3506072 400066698949002602416861 := by
  unfold tailWord_3506072
  simp only [CollatzResearch.WordTrace]
  refine ⟨63938475677053704135324235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85251300902738272180432313 63938475677053704135324235)
  ·
    refine ⟨95907713515580556202986353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63938475677053704135324235 95907713515580556202986353)
    ·
      refine ⟨71930785136685417152239765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95907713515580556202986353 71930785136685417152239765)
      ·
        refine ⟨3371755553282128929011239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 71930785136685417152239765 3371755553282128929011239)
        ·
          refine ⟨5057633329923193393516859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3371755553282128929011239 5057633329923193393516859)
          ·
            refine ⟨7586449994884790090275289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5057633329923193393516859 7586449994884790090275289)
            ·
              refine ⟨5689837496163592567706467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7586449994884790090275289 5689837496163592567706467)
              ·
                refine ⟨8534756244245388851559701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5689837496163592567706467 8534756244245388851559701)
                ·
                  refine ⟨400066698949002602416861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8534756244245388851559701 400066698949002602416861)
                  ·
                    rfl

theorem cell22_3506072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 2, 1, 6].length) (baseStart_3506072 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3506072 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3506072 prefixEnd_3506072 := by exact prefixLift 3506072
  have htrace : WordTrace (prefixWord ++ tailWord_3506072) baseStart_3506072 baseEnd_3506072 := by
    simpa [prefixWord, tailWord_3506072, baseEnd_3506072] using wordTrace_append hprefix tailTrace_3506072
  have hstable : (prefixWord ++ tailWord_3506072).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3506072).length < 2 ^ (prefixWord ++ tailWord_3506072).sum := by decide
  have hdescent : baseEnd_3506072 < baseStart_3506072 := by decide
  rcases family_descends (prefixWord ++ tailWord_3506072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3506087 : List Nat := [1, 1, 6, 1, 2, 3, 1, 1, 1, 5]
def baseStart_3506087 : Nat := 118140960795 + 3506087 * 2 ^ 59
def prefixEnd_3506087 : Nat := 4983230072969 + 3 ^ 40 * 3506087 * 2
def baseEnd_3506087 : Nat := 1200205231653552768125537

theorem tailTrace_3506087 : CollatzResearch.WordTrace tailWord_3506087 prefixEnd_3506087 1200205231653552768125537 := by
  unfold tailWord_3506087
  simp only [CollatzResearch.WordTrace]
  refine ⟨127877498449053065832444515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85251665632702043888296343 127877498449053065832444515)
  ·
    refine ⟨191816247673579598748666773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127877498449053065832444515 191816247673579598748666773)
    ·
      refine ⟨8991386609699043691343755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 191816247673579598748666773 8991386609699043691343755)
      ·
        refine ⟨13487079914548565537015633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8991386609699043691343755 13487079914548565537015633)
        ·
          refine ⟨10115309935911424152761725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13487079914548565537015633 10115309935911424152761725)
          ·
            refine ⟨3793241225966784057285647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10115309935911424152761725 3793241225966784057285647)
            ·
              refine ⟨5689861838950176085928471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3793241225966784057285647 5689861838950176085928471)
              ·
                refine ⟨8534792758425264128892707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5689861838950176085928471 8534792758425264128892707)
                ·
                  refine ⟨12802189137637896193339061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8534792758425264128892707 12802189137637896193339061)
                  ·
                    refine ⟨1200205231653552768125537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12802189137637896193339061 1200205231653552768125537)
                    ·
                      rfl

theorem cell22_3506087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 1, 1, 1, 5].length) (baseStart_3506087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3506087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3506087 prefixEnd_3506087 := by exact prefixLift 3506087
  have htrace : WordTrace (prefixWord ++ tailWord_3506087) baseStart_3506087 baseEnd_3506087 := by
    simpa [prefixWord, tailWord_3506087, baseEnd_3506087] using wordTrace_append hprefix tailTrace_3506087
  have hstable : (prefixWord ++ tailWord_3506087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3506087).length < 2 ^ (prefixWord ++ tailWord_3506087).sum := by decide
  have hdescent : baseEnd_3506087 < baseStart_3506087 := by decide
  rcases family_descends (prefixWord ++ tailWord_3506087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3506128 : List Nat := [2, 1, 1, 1, 1, 2, 6, 1, 7]
def baseStart_3506128 : Nat := 118140960795 + 3506128 * 2 ^ 59
def prefixEnd_3506128 : Nat := 4983230072969 + 3 ^ 40 * 3506128 * 2
def baseEnd_3506128 : Nat := 400073088930480775950137

theorem tailTrace_3506128 : CollatzResearch.WordTrace tailWord_3506128 prefixEnd_3506128 400073088930480775950137 := by
  unfold tailWord_3506128
  simp only [CollatzResearch.WordTrace]
  refine ⟨63939496920952264917343519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85252662561269686556458025 63939496920952264917343519)
  ·
    refine ⟨95909245381428397376015279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63939496920952264917343519 95909245381428397376015279)
    ·
      refine ⟨143863868072142596064022919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95909245381428397376015279 143863868072142596064022919)
      ·
        refine ⟨215795802108213894096034379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143863868072142596064022919 215795802108213894096034379)
        ·
          refine ⟨323693703162320841144051569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215795802108213894096034379 323693703162320841144051569)
          ·
            refine ⟨242770277371740630858038677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 323693703162320841144051569 242770277371740630858038677)
            ·
              refine ⟨11379856751800342071470563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 242770277371740630858038677 11379856751800342071470563)
              ·
                refine ⟨17069785127700513107205845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11379856751800342071470563 17069785127700513107205845)
                ·
                  refine ⟨400073088930480775950137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17069785127700513107205845 400073088930480775950137)
                  ·
                    rfl

theorem cell22_3506128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 1, 7].length) (baseStart_3506128 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3506128 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3506128 prefixEnd_3506128 := by exact prefixLift 3506128
  have htrace : WordTrace (prefixWord ++ tailWord_3506128) baseStart_3506128 baseEnd_3506128 := by
    simpa [prefixWord, tailWord_3506128, baseEnd_3506128] using wordTrace_append hprefix tailTrace_3506128
  have hstable : (prefixWord ++ tailWord_3506128).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3506128).length < 2 ^ (prefixWord ++ tailWord_3506128).sum := by decide
  have hdescent : baseEnd_3506128 < baseStart_3506128 := by decide
  rcases family_descends (prefixWord ++ tailWord_3506128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3506175 : List Nat := [1, 1, 2, 2, 1, 2, 1, 7, 1, 4]
def baseStart_3506175 : Nat := 118140960795 + 3506175 * 2 ^ 59
def prefixEnd_3506175 : Nat := 4983230072969 + 3 ^ 40 * 3506175 * 2
def baseEnd_3506175 : Nat := 1200235355851949871925267

theorem tailTrace_3506175 : CollatzResearch.WordTrace tailWord_3506175 prefixEnd_3506175 1200235355851949871925267 := by
  unfold tailWord_3506175
  simp only [CollatzResearch.WordTrace]
  refine ⟨127880708072734256861647979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85253805381822837907765319 127880708072734256861647979)
  ·
    refine ⟨191821062109101385292471969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127880708072734256861647979 191821062109101385292471969)
    ·
      refine ⟨143865796581826038969353977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191821062109101385292471969 143865796581826038969353977)
      ·
        refine ⟨107899347436369529227015483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143865796581826038969353977 107899347436369529227015483)
        ·
          refine ⟨161849021154554293840523225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107899347436369529227015483 161849021154554293840523225)
          ·
            refine ⟨121386765865915720380392419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 161849021154554293840523225 121386765865915720380392419)
            ·
              refine ⟨182080148798873580570588629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121386765865915720380392419 182080148798873580570588629)
              ·
                refine ⟨4267503487473599544623171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 182080148798873580570588629 4267503487473599544623171)
                ·
                  refine ⟨6401255231210399316934757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4267503487473599544623171 6401255231210399316934757)
                  ·
                    refine ⟨1200235355851949871925267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6401255231210399316934757 1200235355851949871925267)
                    ·
                      rfl

theorem cell22_3506175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 7, 1, 4].length) (baseStart_3506175 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3506175 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3506175 prefixEnd_3506175 := by exact prefixLift 3506175
  have htrace : WordTrace (prefixWord ++ tailWord_3506175) baseStart_3506175 baseEnd_3506175 := by
    simpa [prefixWord, tailWord_3506175, baseEnd_3506175] using wordTrace_append hprefix tailTrace_3506175
  have hstable : (prefixWord ++ tailWord_3506175).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3506175).length < 2 ^ (prefixWord ++ tailWord_3506175).sum := by decide
  have hdescent : baseEnd_3506175 < baseStart_3506175 := by decide
  rcases family_descends (prefixWord ++ tailWord_3506175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3506190 : List Nat := [4, 1, 1, 2, 2, 1, 2, 3, 6]
def baseStart_3506190 : Nat := 118140960795 + 3506190 * 2 ^ 59
def prefixEnd_3506190 : Nat := 4983230072969 + 3 ^ 40 * 3506190 * 2
def baseEnd_3506190 : Nat := 400080163552831610933407

theorem tailTrace_3506190 : CollatzResearch.WordTrace tailWord_3506190 prefixEnd_3506190 400080163552831610933407 := by
  unfold tailWord_3506190
  simp only [CollatzResearch.WordTrace]
  refine ⟨15985156895959989302930503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85254170111786609615629349 15985156895959989302930503)
  ·
    refine ⟨23977735343939983954395755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15985156895959989302930503 23977735343939983954395755)
    ·
      refine ⟨35966603015909975931593633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23977735343939983954395755 35966603015909975931593633)
      ·
        refine ⟨26974952261932481948695225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35966603015909975931593633 26974952261932481948695225)
        ·
          refine ⟨20231214196449361461521419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26974952261932481948695225 20231214196449361461521419)
          ·
            refine ⟨30346821294674042192282129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20231214196449361461521419 30346821294674042192282129)
            ·
              refine ⟨22760115971005531644211597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30346821294674042192282129 22760115971005531644211597)
              ·
                refine ⟨8535043489127074366579349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22760115971005531644211597 8535043489127074366579349)
                ·
                  refine ⟨400080163552831610933407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8535043489127074366579349 400080163552831610933407)
                  ·
                    rfl

theorem cell22_3506190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 3, 6].length) (baseStart_3506190 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3506190 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3506190 prefixEnd_3506190 := by exact prefixLift 3506190
  have htrace : WordTrace (prefixWord ++ tailWord_3506190) baseStart_3506190 baseEnd_3506190 := by
    simpa [prefixWord, tailWord_3506190, baseEnd_3506190] using wordTrace_append hprefix tailTrace_3506190
  have hstable : (prefixWord ++ tailWord_3506190).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3506190).length < 2 ^ (prefixWord ++ tailWord_3506190).sum := by decide
  have hdescent : baseEnd_3506190 < baseStart_3506190 := by decide
  rcases family_descends (prefixWord ++ tailWord_3506190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3506220 : List Nat := [2, 2, 1, 1, 1, 2, 2, 5, 2, 4]
def baseStart_3506220 : Nat := 118140960795 + 3506220 * 2 ^ 59
def prefixEnd_3506220 : Nat := 4983230072969 + 3 ^ 40 * 3506220 * 2
def baseEnd_3506220 : Nat := 1200250760271584754550129

theorem tailTrace_3506220 : CollatzResearch.WordTrace tailWord_3506220 prefixEnd_3506220 1200250760271584754550129 := by
  unfold tailWord_3506220
  simp only [CollatzResearch.WordTrace]
  refine ⟨63941174678785614773518057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85254899571714153031357409 63941174678785614773518057)
  ·
    refine ⟨47955881009089211080138543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63941174678785614773518057 47955881009089211080138543)
    ·
      refine ⟨71933821513633816620207815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47955881009089211080138543 71933821513633816620207815)
      ·
        refine ⟨107900732270450724930311723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71933821513633816620207815 107900732270450724930311723)
        ·
          refine ⟨161851098405676087395467585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107900732270450724930311723 161851098405676087395467585)
          ·
            refine ⟨121388323804257065546600689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 161851098405676087395467585 121388323804257065546600689)
            ·
              refine ⟨91041242853192799159950517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121388323804257065546600689 91041242853192799159950517)
              ·
                refine ⟨8535116517486824921245361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 91041242853192799159950517 8535116517486824921245361)
                ·
                  refine ⟨6401337388115118690934021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8535116517486824921245361 6401337388115118690934021)
                  ·
                    refine ⟨1200250760271584754550129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6401337388115118690934021 1200250760271584754550129)
                    ·
                      rfl

theorem cell22_3506220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 4].length) (baseStart_3506220 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3506220 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3506220 prefixEnd_3506220 := by exact prefixLift 3506220
  have htrace : WordTrace (prefixWord ++ tailWord_3506220) baseStart_3506220 baseEnd_3506220 := by
    simpa [prefixWord, tailWord_3506220, baseEnd_3506220] using wordTrace_append hprefix tailTrace_3506220
  have hstable : (prefixWord ++ tailWord_3506220).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3506220).length < 2 ^ (prefixWord ++ tailWord_3506220).sum := by decide
  have hdescent : baseEnd_3506220 < baseStart_3506220 := by decide
  rcases family_descends (prefixWord ++ tailWord_3506220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3506222 : List Nat := [4, 1, 3, 1, 1, 2, 2, 2, 1, 5]
def baseStart_3506222 : Nat := 118140960795 + 3506222 * 2 ^ 59
def prefixEnd_3506222 : Nat := 4983230072969 + 3 ^ 40 * 3506222 * 2
def baseEnd_3506222 : Nat := 1200251444912457416000123

theorem tailTrace_3506222 : CollatzResearch.WordTrace tailWord_3506222 prefixEnd_3506222 1200251444912457416000123 := by
  unfold tailWord_3506222
  simp only [CollatzResearch.WordTrace]
  refine ⟨15985302787945497986076115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85254948202375989259072613 15985302787945497986076115)
  ·
    refine ⟨23977954181918246979114173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15985302787945497986076115 23977954181918246979114173)
    ·
      refine ⟨8991732818219342617167815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23977954181918246979114173 8991732818219342617167815)
      ·
        refine ⟨13487599227329013925751723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8991732818219342617167815 13487599227329013925751723)
        ·
          refine ⟨20231398840993520888627585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13487599227329013925751723 20231398840993520888627585)
          ·
            refine ⟨15173549130745140666470689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20231398840993520888627585 15173549130745140666470689)
            ·
              refine ⟨11380161848058855499853017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15173549130745140666470689 11380161848058855499853017)
              ·
                refine ⟨8535121386044141624889763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11380161848058855499853017 8535121386044141624889763)
                ·
                  refine ⟨12802682079066212437334645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8535121386044141624889763 12802682079066212437334645)
                  ·
                    refine ⟨1200251444912457416000123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12802682079066212437334645 1200251444912457416000123)
                    ·
                      rfl

theorem cell22_3506222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 2, 1, 5].length) (baseStart_3506222 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3506222 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3506222 prefixEnd_3506222 := by exact prefixLift 3506222
  have htrace : WordTrace (prefixWord ++ tailWord_3506222) baseStart_3506222 baseEnd_3506222 := by
    simpa [prefixWord, tailWord_3506222, baseEnd_3506222] using wordTrace_append hprefix tailTrace_3506222
  have hstable : (prefixWord ++ tailWord_3506222).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3506222).length < 2 ^ (prefixWord ++ tailWord_3506222).sum := by decide
  have hdescent : baseEnd_3506222 < baseStart_3506222 := by decide
  rcases family_descends (prefixWord ++ tailWord_3506222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3506269 : List Nat := [1, 4, 4, 1, 1, 1, 4, 6]
def baseStart_3506269 : Nat := 118140960795 + 3506269 * 2 ^ 59
def prefixEnd_3506269 : Nat := 4983230072969 + 3 ^ 40 * 3506269 * 2
def baseEnd_3506269 : Nat := 133363059330329440008331

theorem tailTrace_3506269 : CollatzResearch.WordTrace tailWord_3506269 prefixEnd_3506269 133363059330329440008331 := by
  unfold tailWord_3506269
  simp only [CollatzResearch.WordTrace]
  refine ⟨127884136534393710915569861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85256091022929140610379907 127884136534393710915569861)
  ·
    refine ⟨23978275600198820796669349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 127884136534393710915569861 23978275600198820796669349)
    ·
      refine ⟨4495926675037278899375503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23978275600198820796669349 4495926675037278899375503)
      ·
        refine ⟨6743890012555918349063255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4495926675037278899375503 6743890012555918349063255)
        ·
          refine ⟨10115835018833877523594883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6743890012555918349063255 10115835018833877523594883)
          ·
            refine ⟨15173752528250816285392325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10115835018833877523594883 15173752528250816285392325)
            ·
              refine ⟨2845078599047028053511061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15173752528250816285392325 2845078599047028053511061)
              ·
                refine ⟨133363059330329440008331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2845078599047028053511061 133363059330329440008331)
                ·
                  rfl

theorem cell22_3506269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 4, 6].length) (baseStart_3506269 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3506269 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3506269 prefixEnd_3506269 := by exact prefixLift 3506269
  have htrace : WordTrace (prefixWord ++ tailWord_3506269) baseStart_3506269 baseEnd_3506269 := by
    simpa [prefixWord, tailWord_3506269, baseEnd_3506269] using wordTrace_append hprefix tailTrace_3506269
  have hstable : (prefixWord ++ tailWord_3506269).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3506269).length < 2 ^ (prefixWord ++ tailWord_3506269).sum := by decide
  have hdescent : baseEnd_3506269 < baseStart_3506269 := by decide
  rcases family_descends (prefixWord ++ tailWord_3506269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3506314 : List Nat := [3, 1, 2, 3, 1, 2, 4, 1, 5]
def baseStart_3506314 : Nat := 118140960795 + 3506314 * 2 ^ 59
def prefixEnd_3506314 : Nat := 4983230072969 + 3 ^ 40 * 3506314 * 2
def baseEnd_3506314 : Nat := 400094312797533280899947

theorem tailTrace_3506314 : CollatzResearch.WordTrace tailWord_3506314 prefixEnd_3506314 400094312797533280899947 := by
  unfold tailWord_3506314
  simp only [CollatzResearch.WordTrace]
  refine ⟨31971444454807670900239499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85257185212820455733971997 31971444454807670900239499)
  ·
    refine ⟨47957166682211506350359249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31971444454807670900239499 47957166682211506350359249)
    ·
      refine ⟨35967875011658629762769437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47957166682211506350359249 35967875011658629762769437)
      ·
        refine ⟨13487953129371986161038539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35967875011658629762769437 13487953129371986161038539)
        ·
          refine ⟨20231929694057979241557809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13487953129371986161038539 20231929694057979241557809)
          ·
            refine ⟨15173947270543484431168357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20231929694057979241557809 15173947270543484431168357)
            ·
              refine ⟨2845115113226903330844067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15173947270543484431168357 2845115113226903330844067)
              ·
                refine ⟨4267672669840354996266101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2845115113226903330844067 4267672669840354996266101)
                ·
                  refine ⟨400094312797533280899947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4267672669840354996266101 400094312797533280899947)
                  ·
                    rfl

theorem cell22_3506314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 4, 1, 5].length) (baseStart_3506314 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3506314 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3506314 prefixEnd_3506314 := by exact prefixLift 3506314
  have htrace : WordTrace (prefixWord ++ tailWord_3506314) baseStart_3506314 baseEnd_3506314 := by
    simpa [prefixWord, tailWord_3506314, baseEnd_3506314] using wordTrace_append hprefix tailTrace_3506314
  have hstable : (prefixWord ++ tailWord_3506314).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3506314).length < 2 ^ (prefixWord ++ tailWord_3506314).sum := by decide
  have hdescent : baseEnd_3506314 < baseStart_3506314 := by decide
  rcases family_descends (prefixWord ++ tailWord_3506314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3506325 : List Nat := [1, 3, 2, 1, 1, 1, 4, 1, 8]
def baseStart_3506325 : Nat := 118140960795 + 3506325 * 2 ^ 59
def prefixEnd_3506325 : Nat := 4983230072969 + 3 ^ 40 * 3506325 * 2
def baseEnd_3506325 : Nat := 400095567972466493558269

theorem tailTrace_3506325 : CollatzResearch.WordTrace tailWord_3506325 prefixEnd_3506325 400095567972466493558269 := by
  unfold tailWord_3506325
  simp only [CollatzResearch.WordTrace]
  refine ⟨127886179022190832479608429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85257452681460554986405619 127886179022190832479608429)
  ·
    refine ⟨47957317133321562179853161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127886179022190832479608429 47957317133321562179853161)
    ·
      refine ⟨35967987849991171634889871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47957317133321562179853161 35967987849991171634889871)
      ·
        refine ⟨53951981774986757452334807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35967987849991171634889871 53951981774986757452334807)
        ·
          refine ⟨80927972662480136178502211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53951981774986757452334807 80927972662480136178502211)
          ·
            refine ⟨121391958993720204267753317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80927972662480136178502211 121391958993720204267753317)
            ·
              refine ⟨22760992311322538300203747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 121391958993720204267753317 22760992311322538300203747)
              ·
                refine ⟨34141488466983807450305621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22760992311322538300203747 34141488466983807450305621)
                ·
                  refine ⟨400095567972466493558269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34141488466983807450305621 400095567972466493558269)
                  ·
                    rfl

theorem cell22_3506325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 1, 8].length) (baseStart_3506325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3506325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3506325 prefixEnd_3506325 := by exact prefixLift 3506325
  have htrace : WordTrace (prefixWord ++ tailWord_3506325) baseStart_3506325 baseEnd_3506325 := by
    simpa [prefixWord, tailWord_3506325, baseEnd_3506325] using wordTrace_append hprefix tailTrace_3506325
  have hstable : (prefixWord ++ tailWord_3506325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3506325).length < 2 ^ (prefixWord ++ tailWord_3506325).sum := by decide
  have hdescent : baseEnd_3506325 < baseStart_3506325 := by decide
  rcases family_descends (prefixWord ++ tailWord_3506325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3506355 : List Nat := [1, 1, 1, 2, 3, 2, 1, 2, 3, 6]
def baseStart_3506355 : Nat := 118140960795 + 3506355 * 2 ^ 59
def prefixEnd_3506355 : Nat := 4983230072969 + 3 ^ 40 * 3506355 * 2
def baseEnd_3506355 : Nat := 1200296973530489402424715

theorem tailTrace_3506355 : CollatzResearch.WordTrace tailWord_3506355 prefixEnd_3506355 1200296973530489402424715 := by
  unfold tailWord_3506355
  simp only [CollatzResearch.WordTrace]
  refine ⟨127887273212082147603200519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85258182141388098402133679 127887273212082147603200519)
  ·
    refine ⟨191830909818123221404800779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127887273212082147603200519 191830909818123221404800779)
    ·
      refine ⟨287746364727184832107201169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191830909818123221404800779 287746364727184832107201169)
      ·
        refine ⟨215809773545388624080400877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 287746364727184832107201169 215809773545388624080400877)
        ·
          refine ⟨80928665079520734030150329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 215809773545388624080400877 80928665079520734030150329)
          ·
            refine ⟨60696498809640550522612747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80928665079520734030150329 60696498809640550522612747)
            ·
              refine ⟨91044748214460825783919121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60696498809640550522612747 91044748214460825783919121)
              ·
                refine ⟨68283561160845619337939341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91044748214460825783919121 68283561160845619337939341)
                ·
                  refine ⟨25606335435317107251727253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68283561160845619337939341 25606335435317107251727253)
                  ·
                    refine ⟨1200296973530489402424715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25606335435317107251727253 1200296973530489402424715)
                    ·
                      rfl

theorem cell22_3506355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 2, 3, 6].length) (baseStart_3506355 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3506355 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3506355 prefixEnd_3506355 := by exact prefixLift 3506355
  have htrace : WordTrace (prefixWord ++ tailWord_3506355) baseStart_3506355 baseEnd_3506355 := by
    simpa [prefixWord, tailWord_3506355, baseEnd_3506355] using wordTrace_append hprefix tailTrace_3506355
  have hstable : (prefixWord ++ tailWord_3506355).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3506355).length < 2 ^ (prefixWord ++ tailWord_3506355).sum := by decide
  have hdescent : baseEnd_3506355 < baseStart_3506355 := by decide
  rcases family_descends (prefixWord ++ tailWord_3506355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3506359 : List Nat := [1, 1, 3, 1, 4, 3, 1, 4, 4]
def baseStart_3506359 : Nat := 118140960795 + 3506359 * 2 ^ 59
def prefixEnd_3506359 : Nat := 4983230072969 + 3 ^ 40 * 3506359 * 2
def baseEnd_3506359 : Nat := 400099447604078241774901

theorem tailTrace_3506359 : CollatzResearch.WordTrace tailWord_3506359 prefixEnd_3506359 400099447604078241774901 := by
  unfold tailWord_3506359
  simp only [CollatzResearch.WordTrace]
  refine ⟨127887419104067656286346131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85258279402711770857564087 127887419104067656286346131)
  ·
    refine ⟨191831128656101484429519197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127887419104067656286346131 191831128656101484429519197)
    ·
      refine ⟨71936673246038056661069699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 191831128656101484429519197 71936673246038056661069699)
      ·
        refine ⟨107905009869057084991604549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71936673246038056661069699 107905009869057084991604549)
        ·
          refine ⟨20232189350448203435925853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 107905009869057084991604549 20232189350448203435925853)
          ·
            refine ⟨7587071006418076288472195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20232189350448203435925853 7587071006418076288472195)
            ·
              refine ⟨11380606509627114432708293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7587071006418076288472195 11380606509627114432708293)
              ·
                refine ⟨2133863720555083956132805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11380606509627114432708293 2133863720555083956132805)
                ·
                  refine ⟨400099447604078241774901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2133863720555083956132805 400099447604078241774901)
                  ·
                    rfl

theorem cell22_3506359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 4, 4].length) (baseStart_3506359 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3506359 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3506359 prefixEnd_3506359 := by exact prefixLift 3506359
  have htrace : WordTrace (prefixWord ++ tailWord_3506359) baseStart_3506359 baseEnd_3506359 := by
    simpa [prefixWord, tailWord_3506359, baseEnd_3506359] using wordTrace_append hprefix tailTrace_3506359
  have hstable : (prefixWord ++ tailWord_3506359).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3506359).length < 2 ^ (prefixWord ++ tailWord_3506359).sum := by decide
  have hdescent : baseEnd_3506359 < baseStart_3506359 := by decide
  rcases family_descends (prefixWord ++ tailWord_3506359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3506389 : List Nat := [1, 3, 2, 4, 2, 1, 1, 1, 1, 6]
def baseStart_3506389 : Nat := 118140960795 + 3506389 * 2 ^ 59
def prefixEnd_3506389 : Nat := 4983230072969 + 3 ^ 40 * 3506389 * 2
def baseEnd_3506389 : Nat := 1200308612425324647074611

theorem tailTrace_3506389 : CollatzResearch.WordTrace tailWord_3506389 prefixEnd_3506389 1200308612425324647074611 := by
  unfold tailWord_3506389
  simp only [CollatzResearch.WordTrace]
  refine ⟨127888513293958971409938221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85259008862639314273292147 127888513293958971409938221)
  ·
    refine ⟨47958192485234614278726833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127888513293958971409938221 47958192485234614278726833)
    ·
      refine ⟨35968644363925960709045125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47958192485234614278726833 35968644363925960709045125)
      ·
        refine ⟨6744120818236117632945961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35968644363925960709045125 6744120818236117632945961)
        ·
          refine ⟨5058090613677088224709471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6744120818236117632945961 5058090613677088224709471)
          ·
            refine ⟨7587135920515632337064207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5058090613677088224709471 7587135920515632337064207)
            ·
              refine ⟨11380703880773448505596311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7587135920515632337064207 11380703880773448505596311)
              ·
                refine ⟨17071055821160172758394467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11380703880773448505596311 17071055821160172758394467)
                ·
                  refine ⟨25606583731740259137591701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17071055821160172758394467 25606583731740259137591701)
                  ·
                    refine ⟨1200308612425324647074611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25606583731740259137591701 1200308612425324647074611)
                    ·
                      rfl

theorem cell22_3506389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 1, 1, 6].length) (baseStart_3506389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3506389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3506389 prefixEnd_3506389 := by exact prefixLift 3506389
  have htrace : WordTrace (prefixWord ++ tailWord_3506389) baseStart_3506389 baseEnd_3506389 := by
    simpa [prefixWord, tailWord_3506389, baseEnd_3506389] using wordTrace_append hprefix tailTrace_3506389
  have hstable : (prefixWord ++ tailWord_3506389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3506389).length < 2 ^ (prefixWord ++ tailWord_3506389).sum := by decide
  have hdescent : baseEnd_3506389 < baseStart_3506389 := by decide
  rcases family_descends (prefixWord ++ tailWord_3506389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3506419 : List Nat := [1, 1, 1, 2, 2, 4, 4, 1, 3, 3]
def baseStart_3506419 : Nat := 118140960795 + 3506419 * 2 ^ 59
def prefixEnd_3506419 : Nat := 4983230072969 + 3 ^ 40 * 3506419 * 2
def baseEnd_3506419 : Nat := 1200318882038414568824519

theorem tailTrace_3506419 : CollatzResearch.WordTrace tailWord_3506419 prefixEnd_3506419 1200318882038414568824519 := by
  unfold tailWord_3506419
  simp only [CollatzResearch.WordTrace]
  refine ⟨127889607483850286533530311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85259738322566857689020207 127889607483850286533530311)
  ·
    refine ⟨191834411225775429800295467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127889607483850286533530311 191834411225775429800295467)
    ·
      refine ⟨287751616838663144700443201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191834411225775429800295467 287751616838663144700443201)
      ·
        refine ⟨215813712628997358525332401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 287751616838663144700443201 215813712628997358525332401)
        ·
          refine ⟨161860284471748018893999301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 215813712628997358525332401 161860284471748018893999301)
          ·
            refine ⟨30348803338452753542624869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 161860284471748018893999301 30348803338452753542624869)
            ·
              refine ⟨5690400625959891289242163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30348803338452753542624869 5690400625959891289242163)
              ·
                refine ⟨8535600938939836933863245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5690400625959891289242163 8535600938939836933863245)
                ·
                  refine ⟨3200850352102438850198717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8535600938939836933863245 3200850352102438850198717)
                  ·
                    refine ⟨1200318882038414568824519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3200850352102438850198717 1200318882038414568824519)
                    ·
                      rfl

theorem cell22_3506419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 4, 1, 3, 3].length) (baseStart_3506419 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3506419 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3506419 prefixEnd_3506419 := by exact prefixLift 3506419
  have htrace : WordTrace (prefixWord ++ tailWord_3506419) baseStart_3506419 baseEnd_3506419 := by
    simpa [prefixWord, tailWord_3506419, baseEnd_3506419] using wordTrace_append hprefix tailTrace_3506419
  have hstable : (prefixWord ++ tailWord_3506419).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3506419).length < 2 ^ (prefixWord ++ tailWord_3506419).sum := by decide
  have hdescent : baseEnd_3506419 < baseStart_3506419 := by decide
  rcases family_descends (prefixWord ++ tailWord_3506419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3506432 : List Nat := [2, 1, 1, 2, 1, 1, 4, 5, 5]
def baseStart_3506432 : Nat := 118140960795 + 3506432 * 2 ^ 59
def prefixEnd_3506432 : Nat := 4983230072969 + 3 ^ 40 * 3506432 * 2
def baseEnd_3506432 : Nat := 400107777401362289416493

theorem tailTrace_3506432 : CollatzResearch.WordTrace tailWord_3506432 prefixEnd_3506432 400107777401362289416493 := by
  unfold tailWord_3506432
  simp only [CollatzResearch.WordTrace]
  refine ⟨63945040816401594876876775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85260054421868793169169033 63945040816401594876876775)
  ·
    refine ⟨95917561224602392315315163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63945040816401594876876775 95917561224602392315315163)
    ·
      refine ⟨143876341836903588472972745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95917561224602392315315163 143876341836903588472972745)
      ·
        refine ⟨107907256377677691354729559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143876341836903588472972745 107907256377677691354729559)
        ·
          refine ⟨161860884566516537032094339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107907256377677691354729559 161860884566516537032094339)
          ·
            refine ⟨242791326849774805548141509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161860884566516537032094339 242791326849774805548141509)
            ·
              refine ⟨45523373784332776040276533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 242791326849774805548141509 45523373784332776040276533)
              ·
                refine ⟨4267816292281197753775925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45523373784332776040276533 4267816292281197753775925)
                ·
                  refine ⟨400107777401362289416493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4267816292281197753775925 400107777401362289416493)
                  ·
                    rfl

theorem cell22_3506432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 5, 5].length) (baseStart_3506432 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3506432 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3506432 prefixEnd_3506432 := by exact prefixLift 3506432
  have htrace : WordTrace (prefixWord ++ tailWord_3506432) baseStart_3506432 baseEnd_3506432 := by
    simpa [prefixWord, tailWord_3506432, baseEnd_3506432] using wordTrace_append hprefix tailTrace_3506432
  have hstable : (prefixWord ++ tailWord_3506432).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3506432).length < 2 ^ (prefixWord ++ tailWord_3506432).sum := by decide
  have hdescent : baseEnd_3506432 < baseStart_3506432 := by decide
  rcases family_descends (prefixWord ++ tailWord_3506432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3506631 : List Nat := [1, 1, 4, 1, 1, 4, 2, 3, 1, 4]
def baseStart_3506631 : Nat := 118140960795 + 3506631 * 2 ^ 59
def prefixEnd_3506631 : Nat := 4983230072969 + 3 ^ 40 * 3506631 * 2
def baseEnd_3506631 : Nat := 1200391453970916682523869

theorem tailTrace_3506631 : CollatzResearch.WordTrace tailWord_3506631 prefixEnd_3506631 1200391453970916682523869 := by
  unfold tailWord_3506631
  simp only [CollatzResearch.WordTrace]
  refine ⟨127897339759082246740247747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85264893172721497826831831 127897339759082246740247747)
  ·
    refine ⟨191846009638623370110371621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127897339759082246740247747 191846009638623370110371621)
    ·
      refine ⟨35971126807241881895694679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 191846009638623370110371621 35971126807241881895694679)
      ·
        refine ⟨53956690210862822843542019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35971126807241881895694679 53956690210862822843542019)
        ·
          refine ⟨80935035316294234265313029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53956690210862822843542019 80935035316294234265313029)
          ·
            refine ⟨15175319121805168924746193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80935035316294234265313029 15175319121805168924746193)
            ·
              refine ⟨11381489341353876693559645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15175319121805168924746193 11381489341353876693559645)
              ·
                refine ⟨4268058503007703760084867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11381489341353876693559645 4268058503007703760084867)
                ·
                  refine ⟨6402087754511555640127301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4268058503007703760084867 6402087754511555640127301)
                  ·
                    refine ⟨1200391453970916682523869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6402087754511555640127301 1200391453970916682523869)
                    ·
                      rfl

theorem cell22_3506631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 3, 1, 4].length) (baseStart_3506631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3506631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3506631 prefixEnd_3506631 := by exact prefixLift 3506631
  have htrace : WordTrace (prefixWord ++ tailWord_3506631) baseStart_3506631 baseEnd_3506631 := by
    simpa [prefixWord, tailWord_3506631, baseEnd_3506631] using wordTrace_append hprefix tailTrace_3506631
  have hstable : (prefixWord ++ tailWord_3506631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3506631).length < 2 ^ (prefixWord ++ tailWord_3506631).sum := by decide
  have hdescent : baseEnd_3506631 < baseStart_3506631 := by decide
  rcases family_descends (prefixWord ++ tailWord_3506631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3506695 : List Nat := [1, 1, 4, 3, 3, 1, 2, 2, 2, 3]
def baseStart_3506695 : Nat := 118140960795 + 3506695 * 2 ^ 59
def prefixEnd_3506695 : Nat := 4983230072969 + 3 ^ 40 * 3506695 * 2
def baseEnd_3506695 : Nat := 1200413362478841848923673

theorem tailTrace_3506695 : CollatzResearch.WordTrace tailWord_3506695 prefixEnd_3506695 1200413362478841848923673 := by
  unfold tailWord_3506695
  simp only [CollatzResearch.WordTrace]
  refine ⟨127899674030850385670577539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85266449353900257113718359 127899674030850385670577539)
  ·
    refine ⟨191849511046275578505866309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127899674030850385670577539 191849511046275578505866309)
    ·
      refine ⟨35971783321176670969849933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 191849511046275578505866309 35971783321176670969849933)
      ·
        refine ⟨13489418745441251613693725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35971783321176670969849933 13489418745441251613693725)
        ·
          refine ⟨5058532029540469355135147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13489418745441251613693725 5058532029540469355135147)
          ·
            refine ⟨7587798044310704032702721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5058532029540469355135147 7587798044310704032702721)
            ·
              refine ⟨5690848533233028024527041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7587798044310704032702721 5690848533233028024527041)
              ·
                refine ⟨4268136399924771018395281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5690848533233028024527041 4268136399924771018395281)
                ·
                  refine ⟨3201102299943578263796461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4268136399924771018395281 3201102299943578263796461)
                  ·
                    refine ⟨1200413362478841848923673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3201102299943578263796461 1200413362478841848923673)
                    ·
                      rfl

theorem cell22_3506695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 2, 2, 2, 3].length) (baseStart_3506695 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3506695 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3506695 prefixEnd_3506695 := by exact prefixLift 3506695
  have htrace : WordTrace (prefixWord ++ tailWord_3506695) baseStart_3506695 baseEnd_3506695 := by
    simpa [prefixWord, tailWord_3506695, baseEnd_3506695] using wordTrace_append hprefix tailTrace_3506695
  have hstable : (prefixWord ++ tailWord_3506695).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3506695).length < 2 ^ (prefixWord ++ tailWord_3506695).sum := by decide
  have hdescent : baseEnd_3506695 < baseStart_3506695 := by decide
  rcases family_descends (prefixWord ++ tailWord_3506695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3506708 : List Nat := [2, 4, 3, 1, 1, 1, 3, 7]
def baseStart_3506708 : Nat := 118140960795 + 3506708 * 2 ^ 59
def prefixEnd_3506708 : Nat := 4983230072969 + 3 ^ 40 * 3506708 * 2
def baseEnd_3506708 : Nat := 133379756960501572038737

theorem tailTrace_3506708 : CollatzResearch.WordTrace tailWord_3506708 prefixEnd_3506708 133379756960501572038737 := by
  unfold tailWord_3506708
  simp only [CollatzResearch.WordTrace]
  refine ⟨63950074089901644445400389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85266765453202192593867185 63950074089901644445400389)
  ·
    refine ⟨11990638891856558333512573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63950074089901644445400389 11990638891856558333512573)
    ·
      refine ⟨4496489584446209375067215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11990638891856558333512573 4496489584446209375067215)
      ·
        refine ⟨6744734376669314062600823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4496489584446209375067215 6744734376669314062600823)
        ·
          refine ⟨10117101565003971093901235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6744734376669314062600823 10117101565003971093901235)
          ·
            refine ⟨15175652347505956640851853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10117101565003971093901235 15175652347505956640851853)
            ·
              refine ⟨5690869630314733740319445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15175652347505956640851853 5690869630314733740319445)
              ·
                refine ⟨133379756960501572038737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5690869630314733740319445 133379756960501572038737)
                ·
                  rfl

theorem cell22_3506708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 3, 7].length) (baseStart_3506708 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3506708 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3506708 prefixEnd_3506708 := by exact prefixLift 3506708
  have htrace : WordTrace (prefixWord ++ tailWord_3506708) baseStart_3506708 baseEnd_3506708 := by
    simpa [prefixWord, tailWord_3506708, baseEnd_3506708] using wordTrace_append hprefix tailTrace_3506708
  have hstable : (prefixWord ++ tailWord_3506708).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3506708).length < 2 ^ (prefixWord ++ tailWord_3506708).sum := by decide
  have hdescent : baseEnd_3506708 < baseStart_3506708 := by decide
  rcases family_descends (prefixWord ++ tailWord_3506708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3506719 : List Nat := [1, 1, 2, 4, 1, 1, 1, 2, 9]
def baseStart_3506719 : Nat := 118140960795 + 3506719 * 2 ^ 59
def prefixEnd_3506719 : Nat := 4983230072969 + 3 ^ 40 * 3506719 * 2
def baseEnd_3506719 : Nat := 400140526056437928774533

theorem tailTrace_3506719 : CollatzResearch.WordTrace tailWord_3506719 prefixEnd_3506719 400140526056437928774533 := by
  unfold tailWord_3506719
  simp only [CollatzResearch.WordTrace]
  refine ⟨127900549382763437769451211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85267032921842291846300807 127900549382763437769451211)
  ·
    refine ⟨191850824074145156654176817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127900549382763437769451211 191850824074145156654176817)
    ·
      refine ⟨143888118055608867490632613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191850824074145156654176817 143888118055608867490632613)
      ·
        refine ⟨26979022135426662654493615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 143888118055608867490632613 26979022135426662654493615)
        ·
          refine ⟨40468533203139993981740423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26979022135426662654493615 40468533203139993981740423)
          ·
            refine ⟨60702799804709990972610635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40468533203139993981740423 60702799804709990972610635)
            ·
              refine ⟨91054199707064986458915953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60702799804709990972610635 91054199707064986458915953)
              ·
                refine ⟨68290649780298739844186965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91054199707064986458915953 68290649780298739844186965)
                ·
                  refine ⟨400140526056437928774533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 68290649780298739844186965 400140526056437928774533)
                  ·
                    rfl

theorem cell22_3506719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 2, 9].length) (baseStart_3506719 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3506719 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3506719 prefixEnd_3506719 := by exact prefixLift 3506719
  have htrace : WordTrace (prefixWord ++ tailWord_3506719) baseStart_3506719 baseEnd_3506719 := by
    simpa [prefixWord, tailWord_3506719, baseEnd_3506719] using wordTrace_append hprefix tailTrace_3506719
  have hstable : (prefixWord ++ tailWord_3506719).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3506719).length < 2 ^ (prefixWord ++ tailWord_3506719).sum := by decide
  have hdescent : baseEnd_3506719 < baseStart_3506719 := by decide
  rcases family_descends (prefixWord ++ tailWord_3506719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3506723 : List Nat := [1, 1, 1, 4, 4, 2, 1, 2, 3, 3]
def baseStart_3506723 : Nat := 118140960795 + 3506723 * 2 ^ 59
def prefixEnd_3506723 : Nat := 4983230072969 + 3 ^ 40 * 3506723 * 2
def baseEnd_3506723 : Nat := 1200422947451059109223587

theorem tailTrace_3506723 : CollatzResearch.WordTrace tailWord_3506723 prefixEnd_3506723 1200422947451059109223587 := by
  unfold tailWord_3506723
  simp only [CollatzResearch.WordTrace]
  refine ⟨127900695274748946452596823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85267130183165964301731215 127900695274748946452596823)
  ·
    refine ⟨191851042912123419678895235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127900695274748946452596823 191851042912123419678895235)
    ·
      refine ⟨287776564368185129518342853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191851042912123419678895235 287776564368185129518342853)
      ·
        refine ⟨53958105819034711784689285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 287776564368185129518342853 53958105819034711784689285)
        ·
          refine ⟨10117144841069008459629241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53958105819034711784689285 10117144841069008459629241)
          ·
            refine ⟨7587858630801756344721931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10117144841069008459629241 7587858630801756344721931)
            ·
              refine ⟨11381787946202634517082897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7587858630801756344721931 11381787946202634517082897)
              ·
                refine ⟨8536340959651975887812173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11381787946202634517082897 8536340959651975887812173)
                ·
                  refine ⟨3201127859869490957929565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8536340959651975887812173 3201127859869490957929565)
                  ·
                    refine ⟨1200422947451059109223587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3201127859869490957929565 1200422947451059109223587)
                    ·
                      rfl

theorem cell22_3506723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 2, 3, 3].length) (baseStart_3506723 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3506723 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3506723 prefixEnd_3506723 := by exact prefixLift 3506723
  have htrace : WordTrace (prefixWord ++ tailWord_3506723) baseStart_3506723 baseEnd_3506723 := by
    simpa [prefixWord, tailWord_3506723, baseEnd_3506723] using wordTrace_append hprefix tailTrace_3506723
  have hstable : (prefixWord ++ tailWord_3506723).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3506723).length < 2 ^ (prefixWord ++ tailWord_3506723).sum := by decide
  have hdescent : baseEnd_3506723 < baseStart_3506723 := by decide
  rcases family_descends (prefixWord ++ tailWord_3506723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3506727 : List Nat := [1, 1, 7, 2, 1, 2, 1, 1, 2, 4]
def baseStart_3506727 : Nat := 118140960795 + 3506727 * 2 ^ 59
def prefixEnd_3506727 : Nat := 4983230072969 + 3 ^ 40 * 3506727 * 2
def baseEnd_3506727 : Nat := 1200424316732804432123575

theorem tailTrace_3506727 : CollatzResearch.WordTrace tailWord_3506727 prefixEnd_3506727 1200424316732804432123575 := by
  unfold tailWord_3506727
  simp only [CollatzResearch.WordTrace]
  refine ⟨127900841166734455135742435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85267227444489636757161623 127900841166734455135742435)
  ·
    refine ⟨191851261750101682703613653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127900841166734455135742435 191851261750101682703613653)
    ·
      refine ⟨4496513947268008188365945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 191851261750101682703613653 4496513947268008188365945)
      ·
        refine ⟨3372385460451006141274459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4496513947268008188365945 3372385460451006141274459)
        ·
          refine ⟨5058578190676509211911689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3372385460451006141274459 5058578190676509211911689)
          ·
            refine ⟨3793933643007381908933767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5058578190676509211911689 3793933643007381908933767)
            ·
              refine ⟨5690900464511072863400651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3793933643007381908933767 5690900464511072863400651)
              ·
                refine ⟨8536350696766609295100977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5690900464511072863400651 8536350696766609295100977)
                ·
                  refine ⟨6402263022574956971325733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8536350696766609295100977 6402263022574956971325733)
                  ·
                    refine ⟨1200424316732804432123575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6402263022574956971325733 1200424316732804432123575)
                    ·
                      rfl

theorem cell22_3506727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 1, 1, 2, 4].length) (baseStart_3506727 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3506727 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3506727 prefixEnd_3506727 := by exact prefixLift 3506727
  have htrace : WordTrace (prefixWord ++ tailWord_3506727) baseStart_3506727 baseEnd_3506727 := by
    simpa [prefixWord, tailWord_3506727, baseEnd_3506727] using wordTrace_append hprefix tailTrace_3506727
  have hstable : (prefixWord ++ tailWord_3506727).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3506727).length < 2 ^ (prefixWord ++ tailWord_3506727).sum := by decide
  have hdescent : baseEnd_3506727 < baseStart_3506727 := by decide
  rcases family_descends (prefixWord ++ tailWord_3506727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3506753 : List Nat := [1, 2, 5, 1, 1, 2, 3, 2, 5]
def baseStart_3506753 : Nat := 118140960795 + 3506753 * 2 ^ 59
def prefixEnd_3506753 : Nat := 4983230072969 + 3 ^ 40 * 3506753 * 2
def baseEnd_3506753 : Nat := 400144405688049676991165

theorem tailTrace_3506753 : CollatzResearch.WordTrace tailWord_3506753 prefixEnd_3506753 400144405688049676991165 := by
  unfold tailWord_3506753
  simp only [CollatzResearch.WordTrace]
  refine ⟨127901789464640261576188913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85267859643093507717459275 127901789464640261576188913)
  ·
    refine ⟨95926342098480196182141685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127901789464640261576188913 95926342098480196182141685)
    ·
      refine ⟨8993094571732518392075783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 95926342098480196182141685 8993094571732518392075783)
      ·
        refine ⟨13489641857598777588113675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8993094571732518392075783 13489641857598777588113675)
        ·
          refine ⟨20234462786398166382170513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13489641857598777588113675 20234462786398166382170513)
          ·
            refine ⟨15175847089798624786627885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20234462786398166382170513 15175847089798624786627885)
            ·
              refine ⟨5690942658674484294985457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15175847089798624786627885 5690942658674484294985457)
              ·
                refine ⟨4268206994005863221239093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5690942658674484294985457 4268206994005863221239093)
                ·
                  refine ⟨400144405688049676991165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4268206994005863221239093 400144405688049676991165)
                  ·
                    rfl

theorem cell22_3506753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 3, 2, 5].length) (baseStart_3506753 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3506753 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3506753 prefixEnd_3506753 := by exact prefixLift 3506753
  have htrace : WordTrace (prefixWord ++ tailWord_3506753) baseStart_3506753 baseEnd_3506753 := by
    simpa [prefixWord, tailWord_3506753, baseEnd_3506753] using wordTrace_append hprefix tailTrace_3506753
  have hstable : (prefixWord ++ tailWord_3506753).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3506753).length < 2 ^ (prefixWord ++ tailWord_3506753).sum := by decide
  have hdescent : baseEnd_3506753 < baseStart_3506753 := by decide
  rcases family_descends (prefixWord ++ tailWord_3506753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3506766 : List Nat := [4, 1, 1, 1, 1, 2, 2, 1, 5, 4]
def baseStart_3506766 : Nat := 118140960795 + 3506766 * 2 ^ 59
def prefixEnd_3506766 : Nat := 4983230072969 + 3 ^ 40 * 3506766 * 2
def baseEnd_3506766 : Nat := 1200437667229821330398455

theorem tailTrace_3506766 : CollatzResearch.WordTrace tailWord_3506766 prefixEnd_3506766 1200437667229821330398455 := by
  unfold tailWord_3506766
  simp only [CollatzResearch.WordTrace]
  refine ⟨15987782951699145599551519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85268175742395443197608101 15987782951699145599551519)
  ·
    refine ⟨23981674427548718399327279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15987782951699145599551519 23981674427548718399327279)
    ·
      refine ⟨35972511641323077598990919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23981674427548718399327279 35972511641323077598990919)
      ·
        refine ⟨53958767461984616398486379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35972511641323077598990919 53958767461984616398486379)
        ·
          refine ⟨80938151192976924597729569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53958767461984616398486379 80938151192976924597729569)
          ·
            refine ⟨60703613394732693448297177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80938151192976924597729569 60703613394732693448297177)
            ·
              refine ⟨45527710046049520086222883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60703613394732693448297177 45527710046049520086222883)
              ·
                refine ⟨68291565069074280129334325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45527710046049520086222883 68291565069074280129334325)
                ·
                  refine ⟨6402334225225713762125093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 68291565069074280129334325 6402334225225713762125093)
                  ·
                    refine ⟨1200437667229821330398455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6402334225225713762125093 1200437667229821330398455)
                    ·
                      rfl

theorem cell22_3506766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 1, 5, 4].length) (baseStart_3506766 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3506766 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3506766 prefixEnd_3506766 := by exact prefixLift 3506766
  have htrace : WordTrace (prefixWord ++ tailWord_3506766) baseStart_3506766 baseEnd_3506766 := by
    simpa [prefixWord, tailWord_3506766, baseEnd_3506766] using wordTrace_append hprefix tailTrace_3506766
  have hstable : (prefixWord ++ tailWord_3506766).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3506766).length < 2 ^ (prefixWord ++ tailWord_3506766).sum := by decide
  have hdescent : baseEnd_3506766 < baseStart_3506766 := by decide
  rcases family_descends (prefixWord ++ tailWord_3506766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3506796 : List Nat := [2, 2, 1, 1, 3, 1, 2, 4, 1, 5]
def baseStart_3506796 : Nat := 118140960795 + 3506796 * 2 ^ 59
def prefixEnd_3506796 : Nat := 4983230072969 + 3 ^ 40 * 3506796 * 2
def baseEnd_3506796 : Nat := 1200447936842911252148363

theorem tailTrace_3506796 : CollatzResearch.WordTrace tailWord_3506796 prefixEnd_3506796 1200447936842911252148363 := by
  unfold tailWord_3506796
  simp only [CollatzResearch.WordTrace]
  refine ⟨63951678901742239960002121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85268905202322986613336161 63951678901742239960002121)
  ·
    refine ⟨47963759176306679970001591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63951678901742239960002121 47963759176306679970001591)
    ·
      refine ⟨71945638764460019955002387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47963759176306679970001591 71945638764460019955002387)
      ·
        refine ⟨107918458146690029932503581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71945638764460019955002387 107918458146690029932503581)
        ·
          refine ⟨40469421805008761224688843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107918458146690029932503581 40469421805008761224688843)
          ·
            refine ⟨60704132707513141837033265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40469421805008761224688843 60704132707513141837033265)
            ·
              refine ⟨45528099530634856377774949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60704132707513141837033265 45528099530634856377774949)
              ·
                refine ⟨8536518661994035570832803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45528099530634856377774949 8536518661994035570832803)
                ·
                  refine ⟨12804777992991053356249205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8536518661994035570832803 12804777992991053356249205)
                  ·
                    refine ⟨1200447936842911252148363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12804777992991053356249205 1200447936842911252148363)
                    ·
                      rfl

theorem cell22_3506796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 5].length) (baseStart_3506796 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3506796 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3506796 prefixEnd_3506796 := by exact prefixLift 3506796
  have htrace : WordTrace (prefixWord ++ tailWord_3506796) baseStart_3506796 baseEnd_3506796 := by
    simpa [prefixWord, tailWord_3506796, baseEnd_3506796] using wordTrace_append hprefix tailTrace_3506796
  have hstable : (prefixWord ++ tailWord_3506796).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3506796).length < 2 ^ (prefixWord ++ tailWord_3506796).sum := by decide
  have hdescent : baseEnd_3506796 < baseStart_3506796 := by decide
  rcases family_descends (prefixWord ++ tailWord_3506796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3506830 : List Nat := [4, 1, 1, 3, 1, 1, 3, 3, 2, 3]
def baseStart_3506830 : Nat := 118140960795 + 3506830 * 2 ^ 59
def prefixEnd_3506830 : Nat := 4983230072969 + 3 ^ 40 * 3506830 * 2
def baseEnd_3506830 : Nat := 1200459575737746496798259

theorem tailTrace_3506830 : CollatzResearch.WordTrace tailWord_3506830 prefixEnd_3506830 1200459575737746496798259 := by
  unfold tailWord_3506830
  simp only [CollatzResearch.WordTrace]
  refine ⟨15988074735670162965842743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85269731923574202484494629 15988074735670162965842743)
  ·
    refine ⟨23982112103505244448764115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15988074735670162965842743 23982112103505244448764115)
    ·
      refine ⟨35973168155257866673146173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23982112103505244448764115 35973168155257866673146173)
      ·
        refine ⟨13489938058221700002429815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35973168155257866673146173 13489938058221700002429815)
        ·
          refine ⟨20234907087332550003644723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13489938058221700002429815 20234907087332550003644723)
          ·
            refine ⟨30352360630998825005467085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20234907087332550003644723 30352360630998825005467085)
            ·
              refine ⟨11382135236624559377050157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30352360630998825005467085 11382135236624559377050157)
              ·
                refine ⟨4268300713734209766393809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11382135236624559377050157 4268300713734209766393809)
                ·
                  refine ⟨3201225535300657324795357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4268300713734209766393809 3201225535300657324795357)
                  ·
                    refine ⟨1200459575737746496798259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3201225535300657324795357 1200459575737746496798259)
                    ·
                      rfl

theorem cell22_3506830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 3, 2, 3].length) (baseStart_3506830 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3506830 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3506830 prefixEnd_3506830 := by exact prefixLift 3506830
  have htrace : WordTrace (prefixWord ++ tailWord_3506830) baseStart_3506830 baseEnd_3506830 := by
    simpa [prefixWord, tailWord_3506830, baseEnd_3506830] using wordTrace_append hprefix tailTrace_3506830
  have hstable : (prefixWord ++ tailWord_3506830).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3506830).length < 2 ^ (prefixWord ++ tailWord_3506830).sum := by decide
  have hdescent : baseEnd_3506830 < baseStart_3506830 := by decide
  rcases family_descends (prefixWord ++ tailWord_3506830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3506888 : List Nat := [2, 1, 3, 1, 2, 3, 2, 3, 5]
def baseStart_3506888 : Nat := 118140960795 + 3506888 * 2 ^ 59
def prefixEnd_3506888 : Nat := 4983230072969 + 3 ^ 40 * 3506888 * 2
def baseEnd_3506888 : Nat := 400159810107684559616027

theorem tailTrace_3506888 : CollatzResearch.WordTrace tailWord_3506888 prefixEnd_3506888 400159810107684559616027 := by
  unfold tailWord_3506888
  simp only [CollatzResearch.WordTrace]
  refine ⟨63953356659575589816176659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85271142212767453088235545 63953356659575589816176659)
  ·
    refine ⟨95930034989363384724264989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63953356659575589816176659 95930034989363384724264989)
    ·
      refine ⟨35973763121011269271599371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95930034989363384724264989 35973763121011269271599371)
      ·
        refine ⟨53960644681516903907399057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35973763121011269271599371 53960644681516903907399057)
        ·
          refine ⟨40470483511137677930549293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53960644681516903907399057 40470483511137677930549293)
          ·
            refine ⟨15176431316676629223955985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40470483511137677930549293 15176431316676629223955985)
            ·
              refine ⟨11382323487507471917966989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15176431316676629223955985 11382323487507471917966989)
              ·
                refine ⟨4268371307815301969237621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11382323487507471917966989 4268371307815301969237621)
                ·
                  refine ⟨400159810107684559616027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4268371307815301969237621 400159810107684559616027)
                  ·
                    rfl

theorem cell22_3506888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 3, 5].length) (baseStart_3506888 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3506888 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3506888 prefixEnd_3506888 := by exact prefixLift 3506888
  have htrace : WordTrace (prefixWord ++ tailWord_3506888) baseStart_3506888 baseEnd_3506888 := by
    simpa [prefixWord, tailWord_3506888, baseEnd_3506888] using wordTrace_append hprefix tailTrace_3506888
  have hstable : (prefixWord ++ tailWord_3506888).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3506888).length < 2 ^ (prefixWord ++ tailWord_3506888).sum := by decide
  have hdescent : baseEnd_3506888 < baseStart_3506888 := by decide
  rcases family_descends (prefixWord ++ tailWord_3506888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3506963 : List Nat := [1, 1, 1, 2, 1, 3, 4, 3, 2, 4]
def baseStart_3506963 : Nat := 118140960795 + 3506963 * 2 ^ 59
def prefixEnd_3506963 : Nat := 4983230072969 + 3 ^ 40 * 3506963 * 2
def baseEnd_3506963 : Nat := 1200505104355778483222851

theorem tailTrace_3506963 : CollatzResearch.WordTrace tailWord_3506963 prefixEnd_3506963 1200505104355778483222851 := by
  unfold tailWord_3506963
  simp only [CollatzResearch.WordTrace]
  refine ⟨127909448793879467441333543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85272965862586311627555695 127909448793879467441333543)
  ·
    refine ⟨191864173190819201162000315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127909448793879467441333543 191864173190819201162000315)
    ·
      refine ⟨287796259786228801743000473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191864173190819201162000315 287796259786228801743000473)
      ·
        refine ⟨215847194839671601307250355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 287796259786228801743000473 215847194839671601307250355)
        ·
          refine ⟨323770792259507401960875533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215847194839671601307250355 323770792259507401960875533)
          ·
            refine ⟨121414047097315275735328325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 323770792259507401960875533 121414047097315275735328325)
            ·
              refine ⟨22765133830746614200374061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 121414047097315275735328325 22765133830746614200374061)
              ·
                refine ⟨8536925186529980325140273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22765133830746614200374061 8536925186529980325140273)
                ·
                  refine ⟨6402693889897485243855205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8536925186529980325140273 6402693889897485243855205)
                  ·
                    refine ⟨1200505104355778483222851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6402693889897485243855205 1200505104355778483222851)
                    ·
                      rfl

theorem cell22_3506963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 3, 2, 4].length) (baseStart_3506963 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3506963 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3506963 prefixEnd_3506963 := by exact prefixLift 3506963
  have htrace : WordTrace (prefixWord ++ tailWord_3506963) baseStart_3506963 baseEnd_3506963 := by
    simpa [prefixWord, tailWord_3506963, baseEnd_3506963] using wordTrace_append hprefix tailTrace_3506963
  have hstable : (prefixWord ++ tailWord_3506963).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3506963).length < 2 ^ (prefixWord ++ tailWord_3506963).sum := by decide
  have hdescent : baseEnd_3506963 < baseStart_3506963 := by decide
  rcases family_descends (prefixWord ++ tailWord_3506963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3506978 : List Nat := [3, 3, 1, 1, 2, 2, 10]
def baseStart_3506978 : Nat := 118140960795 + 3506978 * 2 ^ 59
def prefixEnd_3506978 : Nat := 4983230072969 + 3 ^ 40 * 3506978 * 2
def baseEnd_3506978 : Nat := 44463342191197164596215

theorem tailTrace_3506978 : CollatzResearch.WordTrace tailWord_3506978 prefixEnd_3506978 44463342191197164596215 := by
  unfold tailWord_3506978
  simp only [CollatzResearch.WordTrace]
  refine ⟨31977498972206281250782397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85273330592550083335419725 31977498972206281250782397)
  ·
    refine ⟨11991562114577355469043399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31977498972206281250782397 11991562114577355469043399)
    ·
      refine ⟨17987343171866033203565099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11991562114577355469043399 17987343171866033203565099)
      ·
        refine ⟨26981014757799049805347649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17987343171866033203565099 26981014757799049805347649)
        ·
          refine ⟨20235761068349287354010737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26981014757799049805347649 20235761068349287354010737)
          ·
            refine ⟨15176820801261965515508053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20235761068349287354010737 15176820801261965515508053)
            ·
              refine ⟨44463342191197164596215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 15176820801261965515508053 44463342191197164596215)
              ·
                rfl

theorem cell22_3506978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 10].length) (baseStart_3506978 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3506978 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3506978 prefixEnd_3506978 := by exact prefixLift 3506978
  have htrace : WordTrace (prefixWord ++ tailWord_3506978) baseStart_3506978 baseEnd_3506978 := by
    simpa [prefixWord, tailWord_3506978, baseEnd_3506978] using wordTrace_append hprefix tailTrace_3506978
  have hstable : (prefixWord ++ tailWord_3506978).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3506978).length < 2 ^ (prefixWord ++ tailWord_3506978).sum := by decide
  have hdescent : baseEnd_3506978 < baseStart_3506978 := by decide
  rcases family_descends (prefixWord ++ tailWord_3506978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3507040 : List Nat := [2, 1, 1, 3, 3, 1, 4, 2, 5]
def baseStart_3507040 : Nat := 118140960795 + 3507040 * 2 ^ 59
def prefixEnd_3507040 : Nat := 4983230072969 + 3 ^ 40 * 3507040 * 2
def baseEnd_3507040 : Nat := 400177154343125316349205

theorem tailTrace_3507040 : CollatzResearch.WordTrace tailWord_3507040 prefixEnd_3507040 400177154343125316349205 := by
  unfold tailWord_3507040
  simp only [CollatzResearch.WordTrace]
  refine ⟨63956128607300254795943287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85274838143067006394591049 63956128607300254795943287)
  ·
    refine ⟨95934192910950382193914931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63956128607300254795943287 95934192910950382193914931)
    ·
      refine ⟨143901289366425573290872397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95934192910950382193914931 143901289366425573290872397)
      ·
        refine ⟨53962983512409589984077149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143901289366425573290872397 53962983512409589984077149)
        ·
          refine ⟨20236118817153596244028931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53962983512409589984077149 20236118817153596244028931)
          ·
            refine ⟨30354178225730394366043397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20236118817153596244028931 30354178225730394366043397)
            ·
              refine ⟨5691408417324448943633137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30354178225730394366043397 5691408417324448943633137)
              ·
                refine ⟨4268556312993336707724853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5691408417324448943633137 4268556312993336707724853)
                ·
                  refine ⟨400177154343125316349205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4268556312993336707724853 400177154343125316349205)
                  ·
                    rfl

theorem cell22_3507040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 4, 2, 5].length) (baseStart_3507040 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3507040 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3507040 prefixEnd_3507040 := by exact prefixLift 3507040
  have htrace : WordTrace (prefixWord ++ tailWord_3507040) baseStart_3507040 baseEnd_3507040 := by
    simpa [prefixWord, tailWord_3507040, baseEnd_3507040] using wordTrace_append hprefix tailTrace_3507040
  have hstable : (prefixWord ++ tailWord_3507040).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3507040).length < 2 ^ (prefixWord ++ tailWord_3507040).sum := by decide
  have hdescent : baseEnd_3507040 < baseStart_3507040 := by decide
  rcases family_descends (prefixWord ++ tailWord_3507040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3507044 : List Nat := [2, 3, 1, 1, 4, 2, 1, 4, 1, 3]
def baseStart_3507044 : Nat := 118140960795 + 3507044 * 2 ^ 59
def prefixEnd_3507044 : Nat := 4983230072969 + 3 ^ 40 * 3507044 * 2
def baseEnd_3507044 : Nat := 1200532832311121271947603

theorem tailTrace_3507044 : CollatzResearch.WordTrace tailWord_3507044 prefixEnd_3507044 1200532832311121271947603 := by
  unfold tailWord_3507044
  simp only [CollatzResearch.WordTrace]
  refine ⟨63956201553293009137516093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85274935404390678850021457 63956201553293009137516093)
  ·
    refine ⟨23983575582484878426568535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63956201553293009137516093 23983575582484878426568535)
    ·
      refine ⟨35975363373727317639852803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23983575582484878426568535 35975363373727317639852803)
      ·
        refine ⟨53963045060590976459779205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35975363373727317639852803 53963045060590976459779205)
        ·
          refine ⟨10118070948860808086208601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53963045060590976459779205 10118070948860808086208601)
          ·
            refine ⟨7588553211645606064656451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10118070948860808086208601 7588553211645606064656451)
            ·
              refine ⟨11382829817468409096984677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7588553211645606064656451 11382829817468409096984677)
              ·
                refine ⟨2134280590775326705684627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11382829817468409096984677 2134280590775326705684627)
                ·
                  refine ⟨3201420886162990058526941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2134280590775326705684627 3201420886162990058526941)
                  ·
                    refine ⟨1200532832311121271947603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3201420886162990058526941 1200532832311121271947603)
                    ·
                      rfl

theorem cell22_3507044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 4, 1, 3].length) (baseStart_3507044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3507044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3507044 prefixEnd_3507044 := by exact prefixLift 3507044
  have htrace : WordTrace (prefixWord ++ tailWord_3507044) baseStart_3507044 baseEnd_3507044 := by
    simpa [prefixWord, tailWord_3507044, baseEnd_3507044] using wordTrace_append hprefix tailTrace_3507044
  have hstable : (prefixWord ++ tailWord_3507044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3507044).length < 2 ^ (prefixWord ++ tailWord_3507044).sum := by decide
  have hdescent : baseEnd_3507044 < baseStart_3507044 := by decide
  rcases family_descends (prefixWord ++ tailWord_3507044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3507113 : List Nat := [1, 2, 1, 1, 1, 1, 6, 9]
def baseStart_3507113 : Nat := 118140960795 + 3507113 * 2 ^ 59
def prefixEnd_3507113 : Nat := 4983230072969 + 3 ^ 40 * 3507113 * 2
def baseEnd_3507113 : Nat := 133395161380136454663599

theorem tailTrace_3507113 : CollatzResearch.WordTrace tailWord_3507113 prefixEnd_3507113 133395161380136454663599 := by
  unfold tailWord_3507113
  simp only [CollatzResearch.WordTrace]
  refine ⟨127914919743336043059293993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85276613162224028706195995 127914919743336043059293993)
  ·
    refine ⟨95936189807502032294470495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127914919743336043059293993 95936189807502032294470495)
    ·
      refine ⟨143904284711253048441705743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95936189807502032294470495 143904284711253048441705743)
      ·
        refine ⟨215856427066879572662558615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143904284711253048441705743 215856427066879572662558615)
        ·
          refine ⟨323784640600319358993837923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215856427066879572662558615 323784640600319358993837923)
          ·
            refine ⟨485676960900479038490756885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 323784640600319358993837923 485676960900479038490756885)
            ·
              refine ⟨22766107542209954929254229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 485676960900479038490756885 22766107542209954929254229)
              ·
                refine ⟨133395161380136454663599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 22766107542209954929254229 133395161380136454663599)
                ·
                  rfl

theorem cell22_3507113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 9].length) (baseStart_3507113 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3507113 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3507113 prefixEnd_3507113 := by exact prefixLift 3507113
  have htrace : WordTrace (prefixWord ++ tailWord_3507113) baseStart_3507113 baseEnd_3507113 := by
    simpa [prefixWord, tailWord_3507113, baseEnd_3507113] using wordTrace_append hprefix tailTrace_3507113
  have hstable : (prefixWord ++ tailWord_3507113).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3507113).length < 2 ^ (prefixWord ++ tailWord_3507113).sum := by decide
  have hdescent : baseEnd_3507113 < baseStart_3507113 := by decide
  rcases family_descends (prefixWord ++ tailWord_3507113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3507239 : List Nat := [1, 1, 7, 1, 1, 1, 2, 1, 3, 4]
def baseStart_3507239 : Nat := 118140960795 + 3507239 * 2 ^ 59
def prefixEnd_3507239 : Nat := 4983230072969 + 3 ^ 40 * 3507239 * 2
def baseEnd_3507239 : Nat := 1200599584796205763322005

theorem tailTrace_3507239 : CollatzResearch.WordTrace tailWord_3507239 prefixEnd_3507239 1200599584796205763322005 := by
  unfold tailWord_3507239
  simp only [CollatzResearch.WordTrace]
  refine ⟨127919515340879566578380771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85279676893919711052253847 127919515340879566578380771)
  ·
    refine ⟨191879273011319349867571157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127919515340879566578380771 191879273011319349867571157)
    ·
      refine ⟨4497170461202797262521199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 191879273011319349867571157 4497170461202797262521199)
      ·
        refine ⟨6745755691804195893781799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4497170461202797262521199 6745755691804195893781799)
        ·
          refine ⟨10118633537706293840672699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6745755691804195893781799 10118633537706293840672699)
          ·
            refine ⟨15177950306559440761009049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10118633537706293840672699 15177950306559440761009049)
            ·
              refine ⟨11383462729919580570756787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15177950306559440761009049 11383462729919580570756787)
              ·
                refine ⟨17075194094879370856135181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11383462729919580570756787 17075194094879370856135181)
                ·
                  refine ⟨6403197785579764071050693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17075194094879370856135181 6403197785579764071050693)
                  ·
                    refine ⟨1200599584796205763322005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6403197785579764071050693 1200599584796205763322005)
                    ·
                      rfl

theorem cell22_3507239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_3507239 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3507239 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3507239 prefixEnd_3507239 := by exact prefixLift 3507239
  have htrace : WordTrace (prefixWord ++ tailWord_3507239) baseStart_3507239 baseEnd_3507239 := by
    simpa [prefixWord, tailWord_3507239, baseEnd_3507239] using wordTrace_append hprefix tailTrace_3507239
  have hstable : (prefixWord ++ tailWord_3507239).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3507239).length < 2 ^ (prefixWord ++ tailWord_3507239).sum := by decide
  have hdescent : baseEnd_3507239 < baseStart_3507239 := by decide
  rcases family_descends (prefixWord ++ tailWord_3507239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3507256 : List Nat := [2, 1, 2, 1, 5, 3, 2, 1, 1, 4]
def baseStart_3507256 : Nat := 118140960795 + 3507256 * 2 ^ 59
def prefixEnd_3507256 : Nat := 4983230072969 + 3 ^ 40 * 3507256 * 2
def baseEnd_3507256 : Nat := 1200605404243623385646953

theorem tailTrace_3507256 : CollatzResearch.WordTrace tailWord_3507256 prefixEnd_3507256 1200605404243623385646953 := by
  unfold tailWord_3507256
  simp only [CollatzResearch.WordTrace]
  refine ⟨63960067690908989240874811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85280090254545318987833081 63960067690908989240874811)
  ·
    refine ⟨95940101536363483861312217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63960067690908989240874811 95940101536363483861312217)
    ·
      refine ⟨71955076152272612895984163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95940101536363483861312217 71955076152272612895984163)
      ·
        refine ⟨107932614228408919343976245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71955076152272612895984163 107932614228408919343976245)
        ·
          refine ⟨10118682583913336188497773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 107932614228408919343976245 10118682583913336188497773)
          ·
            refine ⟨3794505968967501070686665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10118682583913336188497773 3794505968967501070686665)
            ·
              refine ⟨2845879476725625803014999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3794505968967501070686665 2845879476725625803014999)
              ·
                refine ⟨4268819215088438704522499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2845879476725625803014999 4268819215088438704522499)
                ·
                  refine ⟨6403228822632658056783749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4268819215088438704522499 6403228822632658056783749)
                  ·
                    refine ⟨1200605404243623385646953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6403228822632658056783749 1200605404243623385646953)
                    ·
                      rfl

theorem cell22_3507256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 2, 1, 1, 4].length) (baseStart_3507256 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3507256 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3507256 prefixEnd_3507256 := by exact prefixLift 3507256
  have htrace : WordTrace (prefixWord ++ tailWord_3507256) baseStart_3507256 baseEnd_3507256 := by
    simpa [prefixWord, tailWord_3507256, baseEnd_3507256] using wordTrace_append hprefix tailTrace_3507256
  have hstable : (prefixWord ++ tailWord_3507256).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3507256).length < 2 ^ (prefixWord ++ tailWord_3507256).sum := by decide
  have hdescent : baseEnd_3507256 < baseStart_3507256 := by decide
  rcases family_descends (prefixWord ++ tailWord_3507256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3507269 : List Nat := [1, 3, 1, 1, 1, 3, 5, 2, 2, 3]
def baseStart_3507269 : Nat := 118140960795 + 3507269 * 2 ^ 59
def prefixEnd_3507269 : Nat := 4983230072969 + 3 ^ 40 * 3507269 * 2
def baseEnd_3507269 : Nat := 1200609854409295685071913

theorem tailTrace_3507269 : CollatzResearch.WordTrace tailWord_3507269 prefixEnd_3507269 1200609854409295685071913 := by
  unfold tailWord_3507269
  simp only [CollatzResearch.WordTrace]
  refine ⟨127920609530770881701972861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85280406353847254467981907 127920609530770881701972861)
  ·
    refine ⟨47970228574039080638239823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127920609530770881701972861 47970228574039080638239823)
    ·
      refine ⟨71955342861058620957359735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47970228574039080638239823 71955342861058620957359735)
      ·
        refine ⟨107933014291587931436039603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71955342861058620957359735 107933014291587931436039603)
        ·
          refine ⟨161899521437381897154059405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107933014291587931436039603 161899521437381897154059405)
          ·
            refine ⟨60712320539018211432772277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 161899521437381897154059405 60712320539018211432772277)
            ·
              refine ⟨5691780050532957321822401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 60712320539018211432772277 5691780050532957321822401)
              ·
                refine ⟨4268835037899717991366801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5691780050532957321822401 4268835037899717991366801)
                ·
                  refine ⟨3201626278424788493525101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4268835037899717991366801 3201626278424788493525101)
                  ·
                    refine ⟨1200609854409295685071913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3201626278424788493525101 1200609854409295685071913)
                    ·
                      rfl

theorem cell22_3507269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 5, 2, 2, 3].length) (baseStart_3507269 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3507269 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3507269 prefixEnd_3507269 := by exact prefixLift 3507269
  have htrace : WordTrace (prefixWord ++ tailWord_3507269) baseStart_3507269 baseEnd_3507269 := by
    simpa [prefixWord, tailWord_3507269, baseEnd_3507269] using wordTrace_append hprefix tailTrace_3507269
  have hstable : (prefixWord ++ tailWord_3507269).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3507269).length < 2 ^ (prefixWord ++ tailWord_3507269).sum := by decide
  have hdescent : baseEnd_3507269 < baseStart_3507269 := by decide
  rcases family_descends (prefixWord ++ tailWord_3507269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3507382 : List Nat := [5, 1, 3, 2, 1, 1, 1, 4, 1, 3]
def baseStart_3507382 : Nat := 118140960795 + 3507382 * 2 ^ 59
def prefixEnd_3507382 : Nat := 4983230072969 + 3 ^ 40 * 3507382 * 2
def baseEnd_3507382 : Nat := 1200648536618601056996567

theorem tailTrace_3507382 : CollatzResearch.WordTrace tailWord_3507382 prefixEnd_3507382 1200648536618601056996567 := by
  unfold tailWord_3507382
  simp only [CollatzResearch.WordTrace]
  refine ⟨7995295686210093875052275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 85283153986241001333890933 7995295686210093875052275)
  ·
    refine ⟨11992943529315140812578413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7995295686210093875052275 11992943529315140812578413)
    ·
      refine ⟨4497353823493177804716905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11992943529315140812578413 4497353823493177804716905)
      ·
        refine ⟨3373015367619883353537679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4497353823493177804716905 3373015367619883353537679)
        ·
          refine ⟨5059523051429825030306519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3373015367619883353537679 5059523051429825030306519)
          ·
            refine ⟨7589284577144737545459779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5059523051429825030306519 7589284577144737545459779)
            ·
              refine ⟨11383926865717106318189669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7589284577144737545459779 11383926865717106318189669)
              ·
                refine ⟨2134486287321957434660563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11383926865717106318189669 2134486287321957434660563)
                ·
                  refine ⟨3201729430982936151990845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2134486287321957434660563 3201729430982936151990845)
                  ·
                    refine ⟨1200648536618601056996567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3201729430982936151990845 1200648536618601056996567)
                    ·
                      rfl

theorem cell22_3507382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 4, 1, 3].length) (baseStart_3507382 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3507382 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3507382 prefixEnd_3507382 := by exact prefixLift 3507382
  have htrace : WordTrace (prefixWord ++ tailWord_3507382) baseStart_3507382 baseEnd_3507382 := by
    simpa [prefixWord, tailWord_3507382, baseEnd_3507382] using wordTrace_append hprefix tailTrace_3507382
  have hstable : (prefixWord ++ tailWord_3507382).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3507382).length < 2 ^ (prefixWord ++ tailWord_3507382).sum := by decide
  have hdescent : baseEnd_3507382 < baseStart_3507382 := by decide
  rcases family_descends (prefixWord ++ tailWord_3507382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3507539 : List Nat := [1, 1, 1, 2, 1, 1, 7, 2, 1, 5]
def baseStart_3507539 : Nat := 118140960795 + 3507539 * 2 ^ 59
def prefixEnd_3507539 : Nat := 4983230072969 + 3 ^ 40 * 3507539 * 2
def baseEnd_3507539 : Nat := 1200702280927104980821085

theorem tailTrace_3507539 : CollatzResearch.WordTrace tailWord_3507539 prefixEnd_3507539 1200702280927104980821085 := by
  unfold tailWord_3507539
  simp only [CollatzResearch.WordTrace]
  refine ⟨127930457239792717814301671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85286971493195145209534447 127930457239792717814301671)
  ·
    refine ⟨191895685859689076721452507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127930457239792717814301671 191895685859689076721452507)
    ·
      refine ⟨287843528789533615082178761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191895685859689076721452507 287843528789533615082178761)
      ·
        refine ⟨215882646592150211311634071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 287843528789533615082178761 215882646592150211311634071)
        ·
          refine ⟨323823969888225316967451107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215882646592150211311634071 323823969888225316967451107)
          ·
            refine ⟨485735954832337975451176661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 323823969888225316967451107 485735954832337975451176661)
            ·
              refine ⟨11384436441382921299636953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 485735954832337975451176661 11384436441382921299636953)
              ·
                refine ⟨8538327331037190974727715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11384436441382921299636953 8538327331037190974727715)
                ·
                  refine ⟨12807490996555786462091573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8538327331037190974727715 12807490996555786462091573)
                  ·
                    refine ⟨1200702280927104980821085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12807490996555786462091573 1200702280927104980821085)
                    ·
                      rfl

theorem cell22_3507539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 2, 1, 5].length) (baseStart_3507539 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3507539 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3507539 prefixEnd_3507539 := by exact prefixLift 3507539
  have htrace : WordTrace (prefixWord ++ tailWord_3507539) baseStart_3507539 baseEnd_3507539 := by
    simpa [prefixWord, tailWord_3507539, baseEnd_3507539] using wordTrace_append hprefix tailTrace_3507539
  have hstable : (prefixWord ++ tailWord_3507539).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3507539).length < 2 ^ (prefixWord ++ tailWord_3507539).sum := by decide
  have hdescent : baseEnd_3507539 < baseStart_3507539 := by decide
  rcases family_descends (prefixWord ++ tailWord_3507539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3507543 : List Nat := [1, 1, 3, 2, 3, 3, 3, 1, 1, 4]
def baseStart_3507543 : Nat := 118140960795 + 3507543 * 2 ^ 59
def prefixEnd_3507543 : Nat := 4983230072969 + 3 ^ 40 * 3507543 * 2
def baseEnd_3507543 : Nat := 1200703650208850303721073

theorem tailTrace_3507543 : CollatzResearch.WordTrace tailWord_3507543 prefixEnd_3507543 1200703650208850303721073 := by
  unfold tailWord_3507543
  simp only [CollatzResearch.WordTrace]
  refine ⟨127930603131778226497447283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85287068754518817664964855 127930603131778226497447283)
  ·
    refine ⟨191895904697667339746170925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127930603131778226497447283 191895904697667339746170925)
    ·
      refine ⟨71960964261625252404814097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 191895904697667339746170925 71960964261625252404814097)
      ·
        refine ⟨53970723196218939303610573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71960964261625252404814097 53970723196218939303610573)
        ·
          refine ⟨20239021198582102238853965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53970723196218939303610573 20239021198582102238853965)
          ·
            refine ⟨7589632949468288339570237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20239021198582102238853965 7589632949468288339570237)
            ·
              refine ⟨2846112356050608127338839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7589632949468288339570237 2846112356050608127338839)
              ·
                refine ⟨4269168534075912191008259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2846112356050608127338839 4269168534075912191008259)
                ·
                  refine ⟨6403752801113868286512389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4269168534075912191008259 6403752801113868286512389)
                  ·
                    refine ⟨1200703650208850303721073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6403752801113868286512389 1200703650208850303721073)
                    ·
                      rfl

theorem cell22_3507543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 3, 1, 1, 4].length) (baseStart_3507543 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3507543 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3507543 prefixEnd_3507543 := by exact prefixLift 3507543
  have htrace : WordTrace (prefixWord ++ tailWord_3507543) baseStart_3507543 baseEnd_3507543 := by
    simpa [prefixWord, tailWord_3507543, baseEnd_3507543] using wordTrace_append hprefix tailTrace_3507543
  have hstable : (prefixWord ++ tailWord_3507543).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3507543).length < 2 ^ (prefixWord ++ tailWord_3507543).sum := by decide
  have hdescent : baseEnd_3507543 < baseStart_3507543 := by decide
  rcases family_descends (prefixWord ++ tailWord_3507543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3507569 : List Nat := [1, 2, 2, 2, 1, 2, 5, 7]
def baseStart_3507569 : Nat := 118140960795 + 3507569 * 2 ^ 59
def prefixEnd_3507569 : Nat := 4983230072969 + 3 ^ 40 * 3507569 * 2
def baseEnd_3507569 : Nat := 133412505615577211396777

theorem tailTrace_3507569 : CollatzResearch.WordTrace tailWord_3507569 prefixEnd_3507569 133412505615577211396777 := by
  unfold tailWord_3507569
  simp only [CollatzResearch.WordTrace]
  refine ⟨127931551429684032937893761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85287700953122688625262507 127931551429684032937893761)
  ·
    refine ⟨95948663572263024703420321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127931551429684032937893761 95948663572263024703420321)
    ·
      refine ⟨71961497679197268527565241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95948663572263024703420321 71961497679197268527565241)
      ·
        refine ⟨53971123259397951395673931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71961497679197268527565241 53971123259397951395673931)
        ·
          refine ⟨80956684889096927093510897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53971123259397951395673931 80956684889096927093510897)
          ·
            refine ⟨60717513666822695320133173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80956684889096927093510897 60717513666822695320133173)
            ·
              refine ⟨5692266906264627686262485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 60717513666822695320133173 5692266906264627686262485)
              ·
                refine ⟨133412505615577211396777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5692266906264627686262485 133412505615577211396777)
                ·
                  rfl

theorem cell22_3507569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 5, 7].length) (baseStart_3507569 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3507569 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3507569 prefixEnd_3507569 := by exact prefixLift 3507569
  have htrace : WordTrace (prefixWord ++ tailWord_3507569) baseStart_3507569 baseEnd_3507569 := by
    simpa [prefixWord, tailWord_3507569, baseEnd_3507569] using wordTrace_append hprefix tailTrace_3507569
  have hstable : (prefixWord ++ tailWord_3507569).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3507569).length < 2 ^ (prefixWord ++ tailWord_3507569).sum := by decide
  have hdescent : baseEnd_3507569 < baseStart_3507569 := by decide
  rcases family_descends (prefixWord ++ tailWord_3507569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3507573 : List Nat := [1, 3, 4, 1, 3, 1, 2, 1, 1, 5]
def baseStart_3507573 : Nat := 118140960795 + 3507573 * 2 ^ 59
def prefixEnd_3507573 : Nat := 4983230072969 + 3 ^ 40 * 3507573 * 2
def baseEnd_3507573 : Nat := 1200713919821940225470981

theorem tailTrace_3507573 : CollatzResearch.WordTrace tailWord_3507573 prefixEnd_3507573 1200713919821940225470981 := by
  unfold tailWord_3507573
  simp only [CollatzResearch.WordTrace]
  refine ⟨127931697321669541621039373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85287798214446361080692915 127931697321669541621039373)
  ·
    refine ⟨47974386495626078107889765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127931697321669541621039373 47974386495626078107889765)
    ·
      refine ⟨8995197467929889645229331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47974386495626078107889765 8995197467929889645229331)
      ·
        refine ⟨13492796201894834467843997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8995197467929889645229331 13492796201894834467843997)
        ·
          refine ⟨5059798575710562925441499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13492796201894834467843997 5059798575710562925441499)
          ·
            refine ⟨7589697863565844388162249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5059798575710562925441499 7589697863565844388162249)
            ·
              refine ⟨5692273397674383291121687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7589697863565844388162249 5692273397674383291121687)
              ·
                refine ⟨8538410096511574936682531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5692273397674383291121687 8538410096511574936682531)
                ·
                  refine ⟨12807615144767362405023797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8538410096511574936682531 12807615144767362405023797)
                  ·
                    refine ⟨1200713919821940225470981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12807615144767362405023797 1200713919821940225470981)
                    ·
                      rfl

theorem cell22_3507573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 2, 1, 1, 5].length) (baseStart_3507573 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3507573 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3507573 prefixEnd_3507573 := by exact prefixLift 3507573
  have htrace : WordTrace (prefixWord ++ tailWord_3507573) baseStart_3507573 baseEnd_3507573 := by
    simpa [prefixWord, tailWord_3507573, baseEnd_3507573] using wordTrace_append hprefix tailTrace_3507573
  have hstable : (prefixWord ++ tailWord_3507573).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3507573).length < 2 ^ (prefixWord ++ tailWord_3507573).sum := by decide
  have hdescent : baseEnd_3507573 < baseStart_3507573 := by decide
  rcases family_descends (prefixWord ++ tailWord_3507573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3507588 : List Nat := [2, 3, 2, 1, 1, 5, 1, 1, 2, 4]
def baseStart_3507588 : Nat := 118140960795 + 3507588 * 2 ^ 59
def prefixEnd_3507588 : Nat := 4983230072969 + 3 ^ 40 * 3507588 * 2
def baseEnd_3507588 : Nat := 1200719054628485186345935

theorem tailTrace_3507588 : CollatzResearch.WordTrace tailWord_3507588 prefixEnd_3507588 1200719054628485186345935 := by
  unfold tailWord_3507588
  simp only [CollatzResearch.WordTrace]
  refine ⟨63966122208307599591417709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85288162944410132788556945 63966122208307599591417709)
  ·
    refine ⟨23987295828115349846781641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63966122208307599591417709 23987295828115349846781641)
    ·
      refine ⟨17990471871086512385086231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23987295828115349846781641 17990471871086512385086231)
      ·
        refine ⟨26985707806629768577629347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17990471871086512385086231 26985707806629768577629347)
        ·
          refine ⟨40478561709944652866444021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26985707806629768577629347 40478561709944652866444021)
          ·
            refine ⟨3794865160307311206229127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 40478561709944652866444021 3794865160307311206229127)
            ·
              refine ⟨5692297740460966809343691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3794865160307311206229127 5692297740460966809343691)
              ·
                refine ⟨8538446610691450214015537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5692297740460966809343691 8538446610691450214015537)
                ·
                  refine ⟨6403834958018587660511653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8538446610691450214015537 6403834958018587660511653)
                  ·
                    refine ⟨1200719054628485186345935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6403834958018587660511653 1200719054628485186345935)
                    ·
                      rfl

theorem cell22_3507588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 1, 1, 2, 4].length) (baseStart_3507588 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3507588 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3507588 prefixEnd_3507588 := by exact prefixLift 3507588
  have htrace : WordTrace (prefixWord ++ tailWord_3507588) baseStart_3507588 baseEnd_3507588 := by
    simpa [prefixWord, tailWord_3507588, baseEnd_3507588] using wordTrace_append hprefix tailTrace_3507588
  have hstable : (prefixWord ++ tailWord_3507588).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3507588).length < 2 ^ (prefixWord ++ tailWord_3507588).sum := by decide
  have hdescent : baseEnd_3507588 < baseStart_3507588 := by decide
  rcases family_descends (prefixWord ++ tailWord_3507588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3507618 : List Nat := [3, 3, 1, 2, 1, 2, 1, 3, 3, 3]
def baseStart_3507618 : Nat := 118140960795 + 3507618 * 2 ^ 59
def prefixEnd_3507618 : Nat := 4983230072969 + 3 ^ 40 * 3507618 * 2
def baseEnd_3507618 : Nat := 1200729324241575108095843

theorem tailTrace_3507618 : CollatzResearch.WordTrace tailWord_3507618 prefixEnd_3507618 1200729324241575108095843 := by
  unfold tailWord_3507618
  simp only [CollatzResearch.WordTrace]
  refine ⟨31983334651626628576606877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85288892404337676204285005 31983334651626628576606877)
  ·
    refine ⟨11993750494359985716227579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31983334651626628576606877 11993750494359985716227579)
    ·
      refine ⟨17990625741539978574341369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11993750494359985716227579 17990625741539978574341369)
      ·
        refine ⟨13492969306154983930756027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17990625741539978574341369 13492969306154983930756027)
        ·
          refine ⟨20239453959232475896134041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13492969306154983930756027 20239453959232475896134041)
          ·
            refine ⟨15179590469424356922100531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20239453959232475896134041 15179590469424356922100531)
            ·
              refine ⟨22769385704136535383150797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15179590469424356922100531 22769385704136535383150797)
              ·
                refine ⟨8538519639051200768681549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22769385704136535383150797 8538519639051200768681549)
                ·
                  refine ⟨3201944864644200288255581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8538519639051200768681549 3201944864644200288255581)
                  ·
                    refine ⟨1200729324241575108095843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3201944864644200288255581 1200729324241575108095843)
                    ·
                      rfl

theorem cell22_3507618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 3, 3, 3].length) (baseStart_3507618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3507618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3507618 prefixEnd_3507618 := by exact prefixLift 3507618
  have htrace : WordTrace (prefixWord ++ tailWord_3507618) baseStart_3507618 baseEnd_3507618 := by
    simpa [prefixWord, tailWord_3507618, baseEnd_3507618] using wordTrace_append hprefix tailTrace_3507618
  have hstable : (prefixWord ++ tailWord_3507618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3507618).length < 2 ^ (prefixWord ++ tailWord_3507618).sum := by decide
  have hdescent : baseEnd_3507618 < baseStart_3507618 := by decide
  rcases family_descends (prefixWord ++ tailWord_3507618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3507652 : List Nat := [2, 3, 3, 2, 1, 1, 3, 3, 1, 3]
def baseStart_3507652 : Nat := 118140960795 + 3507652 * 2 ^ 59
def prefixEnd_3507652 : Nat := 4983230072969 + 3 ^ 40 * 3507652 * 2
def baseEnd_3507652 : Nat := 1200740963136410352745739

theorem tailTrace_3507652 : CollatzResearch.WordTrace tailWord_3507652 prefixEnd_3507652 1200740963136410352745739 := by
  unfold tailWord_3507652
  simp only [CollatzResearch.WordTrace]
  refine ⟨63967289344191669056582605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85289719125588892075443473 63967289344191669056582605)
  ·
    refine ⟨23987733504071875896218477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63967289344191669056582605 23987733504071875896218477)
    ·
      refine ⟨8995400064026953461081929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23987733504071875896218477 8995400064026953461081929)
      ·
        refine ⟨6746550048020215095811447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8995400064026953461081929 6746550048020215095811447)
        ·
          refine ⟨10119825072030322643717171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6746550048020215095811447 10119825072030322643717171)
          ·
            refine ⟨15179737608045483965575757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10119825072030322643717171 15179737608045483965575757)
            ·
              refine ⟨5692401603017056487090909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15179737608045483965575757 5692401603017056487090909)
              ·
                refine ⟨2134650601131396182659091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5692401603017056487090909 2134650601131396182659091)
                ·
                  refine ⟨3201975901697094273988637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2134650601131396182659091 3201975901697094273988637)
                  ·
                    refine ⟨1200740963136410352745739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3201975901697094273988637 1200740963136410352745739)
                    ·
                      rfl

theorem cell22_3507652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 3, 3, 1, 3].length) (baseStart_3507652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3507652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3507652 prefixEnd_3507652 := by exact prefixLift 3507652
  have htrace : WordTrace (prefixWord ++ tailWord_3507652) baseStart_3507652 baseEnd_3507652 := by
    simpa [prefixWord, tailWord_3507652, baseEnd_3507652] using wordTrace_append hprefix tailTrace_3507652
  have hstable : (prefixWord ++ tailWord_3507652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3507652).length < 2 ^ (prefixWord ++ tailWord_3507652).sum := by decide
  have hdescent : baseEnd_3507652 < baseStart_3507652 := by decide
  rcases family_descends (prefixWord ++ tailWord_3507652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3507659 : List Nat := [1, 1, 1, 1, 3, 3, 2, 2, 8]
def baseStart_3507659 : Nat := 118140960795 + 3507659 * 2 ^ 59
def prefixEnd_3507659 : Nat := 4983230072969 + 3 ^ 40 * 3507659 * 2
def baseEnd_3507659 : Nat := 400247786459821555940239

theorem tailTrace_3507659 : CollatzResearch.WordTrace tailWord_3507659 prefixEnd_3507659 400247786459821555940239 := by
  unfold tailWord_3507659
  simp only [CollatzResearch.WordTrace]
  refine ⟨127934833999357978308670031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85289889332905318872446687 127934833999357978308670031)
  ·
    refine ⟨191902250999036967463005047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127934833999357978308670031 191902250999036967463005047)
    ·
      refine ⟨287853376498555451194507571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191902250999036967463005047 287853376498555451194507571)
      ·
        refine ⟨431780064747833176791761357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287853376498555451194507571 431780064747833176791761357)
        ·
          refine ⟨161917524280437441296910509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 431780064747833176791761357 161917524280437441296910509)
          ·
            refine ⟨60719071605164040486341441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 161917524280437441296910509 60719071605164040486341441)
            ·
              refine ⟨45539303703873030364756081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60719071605164040486341441 45539303703873030364756081)
              ·
                refine ⟨34154477777904772773567061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45539303703873030364756081 34154477777904772773567061)
                ·
                  refine ⟨400247786459821555940239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34154477777904772773567061 400247786459821555940239)
                  ·
                    rfl

theorem cell22_3507659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 2, 8].length) (baseStart_3507659 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3507659 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3507659 prefixEnd_3507659 := by exact prefixLift 3507659
  have htrace : WordTrace (prefixWord ++ tailWord_3507659) baseStart_3507659 baseEnd_3507659 := by
    simpa [prefixWord, tailWord_3507659, baseEnd_3507659] using wordTrace_append hprefix tailTrace_3507659
  have hstable : (prefixWord ++ tailWord_3507659).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3507659).length < 2 ^ (prefixWord ++ tailWord_3507659).sum := by decide
  have hdescent : baseEnd_3507659 < baseStart_3507659 := by decide
  rcases family_descends (prefixWord ++ tailWord_3507659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3507691 : List Nat := [1, 1, 1, 1, 2, 3, 2, 2, 6, 3]
def baseStart_3507691 : Nat := 118140960795 + 3507691 * 2 ^ 59
def prefixEnd_3507691 : Nat := 4983230072969 + 3 ^ 40 * 3507691 * 2
def baseEnd_3507691 : Nat := 1200754313633427251020619

theorem tailTrace_3507691 : CollatzResearch.WordTrace tailWord_3507691 prefixEnd_3507691 1200754313633427251020619 := by
  unfold tailWord_3507691
  simp only [CollatzResearch.WordTrace]
  refine ⟨127936001135242047773834927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85290667423494698515889951 127936001135242047773834927)
  ·
    refine ⟨191904001702863071660752391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127936001135242047773834927 191904001702863071660752391)
    ·
      refine ⟨287856002554294607491128587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191904001702863071660752391 287856002554294607491128587)
      ·
        refine ⟨431784003831441911236692881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287856002554294607491128587 431784003831441911236692881)
        ·
          refine ⟨323838002873581433427519661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 431784003831441911236692881 323838002873581433427519661)
          ·
            refine ⟨121439251077593037535319873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 323838002873581433427519661 121439251077593037535319873)
            ·
              refine ⟨91079438308194778151489905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121439251077593037535319873 91079438308194778151489905)
              ·
                refine ⟨68309578731146083613617429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91079438308194778151489905 68309578731146083613617429)
                ·
                  refine ⟨3202011503022472669388317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 68309578731146083613617429 3202011503022472669388317)
                  ·
                    refine ⟨1200754313633427251020619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3202011503022472669388317 1200754313633427251020619)
                    ·
                      rfl

theorem cell22_3507691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 2, 6, 3].length) (baseStart_3507691 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3507691 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3507691 prefixEnd_3507691 := by exact prefixLift 3507691
  have htrace : WordTrace (prefixWord ++ tailWord_3507691) baseStart_3507691 baseEnd_3507691 := by
    simpa [prefixWord, tailWord_3507691, baseEnd_3507691] using wordTrace_append hprefix tailTrace_3507691
  have hstable : (prefixWord ++ tailWord_3507691).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3507691).length < 2 ^ (prefixWord ++ tailWord_3507691).sum := by decide
  have hdescent : baseEnd_3507691 < baseStart_3507691 := by decide
  rcases family_descends (prefixWord ++ tailWord_3507691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3507781 : List Nat := [1, 3, 1, 1, 1, 4, 1, 1, 4, 5]
def baseStart_3507781 : Nat := 118140960795 + 3507781 * 2 ^ 59
def prefixEnd_3507781 : Nat := 4983230072969 + 3 ^ 40 * 3507781 * 2
def baseEnd_3507781 : Nat := 1200785122472697016270343

theorem tailTrace_3507781 : CollatzResearch.WordTrace tailWord_3507781 prefixEnd_3507781 1200785122472697016270343 := by
  unfold tailWord_3507781
  simp only [CollatzResearch.WordTrace]
  refine ⟨127939283704915993144611197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85292855803277328763074131 127939283704915993144611197)
  ·
    refine ⟨47977231389343497429229199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127939283704915993144611197 47977231389343497429229199)
    ·
      refine ⟨71965847084015246143843799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47977231389343497429229199 71965847084015246143843799)
      ·
        refine ⟨107948770626022869215765699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71965847084015246143843799 107948770626022869215765699)
        ·
          refine ⟨161923155939034303823648549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107948770626022869215765699 161923155939034303823648549)
          ·
            refine ⟨30360591738568931966934103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 161923155939034303823648549 30360591738568931966934103)
            ·
              refine ⟨45540887607853397950401155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30360591738568931966934103 45540887607853397950401155)
              ·
                refine ⟨68311331411780096925601733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45540887607853397950401155 68311331411780096925601733)
                ·
                  refine ⟨12808374639708768173550325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 68311331411780096925601733 12808374639708768173550325)
                  ·
                    refine ⟨1200785122472697016270343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12808374639708768173550325 1200785122472697016270343)
                    ·
                      rfl

theorem cell22_3507781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 1, 4, 5].length) (baseStart_3507781 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3507781 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3507781 prefixEnd_3507781 := by exact prefixLift 3507781
  have htrace : WordTrace (prefixWord ++ tailWord_3507781) baseStart_3507781 baseEnd_3507781 := by
    simpa [prefixWord, tailWord_3507781, baseEnd_3507781] using wordTrace_append hprefix tailTrace_3507781
  have hstable : (prefixWord ++ tailWord_3507781).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3507781).length < 2 ^ (prefixWord ++ tailWord_3507781).sum := by decide
  have hdescent : baseEnd_3507781 < baseStart_3507781 := by decide
  rcases family_descends (prefixWord ++ tailWord_3507781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3507783 : List Nat := [1, 1, 4, 1, 5, 1, 1, 1, 7]
def baseStart_3507783 : Nat := 118140960795 + 3507783 * 2 ^ 59
def prefixEnd_3507783 : Nat := 4983230072969 + 3 ^ 40 * 3507783 * 2
def baseEnd_3507783 : Nat := 400261935704523225906779

theorem tailTrace_3507783 : CollatzResearch.WordTrace tailWord_3507783 prefixEnd_3507783 400261935704523225906779 := by
  unfold tailWord_3507783
  simp only [CollatzResearch.WordTrace]
  refine ⟨127939356650908747486184003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85292904433939164990789335 127939356650908747486184003)
  ·
    refine ⟨191909034976363121229276005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127939356650908747486184003 191909034976363121229276005)
    ·
      refine ⟨35982944058068085230489251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 191909034976363121229276005 35982944058068085230489251)
      ·
        refine ⟨53974416087102127845733877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35982944058068085230489251 53974416087102127845733877)
        ·
          refine ⟨5060101508165824485537551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 53974416087102127845733877 5060101508165824485537551)
          ·
            refine ⟨7590152262248736728306327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5060101508165824485537551 7590152262248736728306327)
            ·
              refine ⟨11385228393373105092459491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7590152262248736728306327 11385228393373105092459491)
              ·
                refine ⟨17077842590059657638689237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11385228393373105092459491 17077842590059657638689237)
                ·
                  refine ⟨400261935704523225906779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17077842590059657638689237 400261935704523225906779)
                  ·
                    rfl

theorem cell22_3507783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 1, 7].length) (baseStart_3507783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3507783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3507783 prefixEnd_3507783 := by exact prefixLift 3507783
  have htrace : WordTrace (prefixWord ++ tailWord_3507783) baseStart_3507783 baseEnd_3507783 := by
    simpa [prefixWord, tailWord_3507783, baseEnd_3507783] using wordTrace_append hprefix tailTrace_3507783
  have hstable : (prefixWord ++ tailWord_3507783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3507783).length < 2 ^ (prefixWord ++ tailWord_3507783).sum := by decide
  have hdescent : baseEnd_3507783 < baseStart_3507783 := by decide
  rcases family_descends (prefixWord ++ tailWord_3507783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3507821 : List Nat := [1, 5, 1, 1, 5, 1, 1, 3, 1, 3]
def baseStart_3507821 : Nat := 118140960795 + 3507821 * 2 ^ 59
def prefixEnd_3507821 : Nat := 4983230072969 + 3 ^ 40 * 3507821 * 2
def baseEnd_3507821 : Nat := 1200798815290150245270221

theorem tailTrace_3507821 : CollatzResearch.WordTrace tailWord_3507821 prefixEnd_3507821 1200798815290150245270221 := by
  unfold tailWord_3507821
  simp only [CollatzResearch.WordTrace]
  refine ⟨127940742624771079976067317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85293828416514053317378211 127940742624771079976067317)
  ·
    refine ⟨11994444621072288747756311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 127940742624771079976067317 11994444621072288747756311)
    ·
      refine ⟨17991666931608433121634467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11994444621072288747756311 17991666931608433121634467)
      ·
        refine ⟨26987500397412649682451701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17991666931608433121634467 26987500397412649682451701)
        ·
          refine ⟨2530078162257435907729847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26987500397412649682451701 2530078162257435907729847)
          ·
            refine ⟨3795117243386153861594771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2530078162257435907729847 3795117243386153861594771)
            ·
              refine ⟨5692675865079230792392157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3795117243386153861594771 5692675865079230792392157)
              ·
                refine ⟨2134753449404711547147059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5692675865079230792392157 2134753449404711547147059)
                ·
                  refine ⟨3202130174107067320720589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2134753449404711547147059 3202130174107067320720589)
                  ·
                    refine ⟨1200798815290150245270221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3202130174107067320720589 1200798815290150245270221)
                    ·
                      rfl

theorem cell22_3507821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 1, 3, 1, 3].length) (baseStart_3507821 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3507821 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3507821 prefixEnd_3507821 := by exact prefixLift 3507821
  have htrace : WordTrace (prefixWord ++ tailWord_3507821) baseStart_3507821 baseEnd_3507821 := by
    simpa [prefixWord, tailWord_3507821, baseEnd_3507821] using wordTrace_append hprefix tailTrace_3507821
  have hstable : (prefixWord ++ tailWord_3507821).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3507821).length < 2 ^ (prefixWord ++ tailWord_3507821).sum := by decide
  have hdescent : baseEnd_3507821 < baseStart_3507821 := by decide
  rcases family_descends (prefixWord ++ tailWord_3507821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3507873 : List Nat := [1, 2, 3, 3, 2, 1, 2, 8]
def baseStart_3507873 : Nat := 118140960795 + 3507873 * 2 ^ 59
def prefixEnd_3507873 : Nat := 4983230072969 + 3 ^ 40 * 3507873 * 2
def baseEnd_3507873 : Nat := 133424068439204382552229

theorem tailTrace_3507873 : CollatzResearch.WordTrace tailWord_3507873 prefixEnd_3507873 133424068439204382552229 := by
  unfold tailWord_3507873
  simp only [CollatzResearch.WordTrace]
  refine ⟨127942639220582692856960273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85295092813721795237973515 127942639220582692856960273)
  ·
    refine ⟨95956979415437019642720205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127942639220582692856960273 95956979415437019642720205)
    ·
      refine ⟨35983867280788882366020077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95956979415437019642720205 35983867280788882366020077)
      ·
        refine ⟨13493950230295830887257529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35983867280788882366020077 13493950230295830887257529)
        ·
          refine ⟨10120462672721873165443147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13493950230295830887257529 10120462672721873165443147)
          ·
            refine ⟨15180694009082809748164721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10120462672721873165443147 15180694009082809748164721)
            ·
              refine ⟨11385520506812107311123541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15180694009082809748164721 11385520506812107311123541)
              ·
                refine ⟨133424068439204382552229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11385520506812107311123541 133424068439204382552229)
                ·
                  rfl

theorem cell22_3507873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 8].length) (baseStart_3507873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3507873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3507873 prefixEnd_3507873 := by exact prefixLift 3507873
  have htrace : WordTrace (prefixWord ++ tailWord_3507873) baseStart_3507873 baseEnd_3507873 := by
    simpa [prefixWord, tailWord_3507873, baseEnd_3507873] using wordTrace_append hprefix tailTrace_3507873
  have hstable : (prefixWord ++ tailWord_3507873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3507873).length < 2 ^ (prefixWord ++ tailWord_3507873).sum := by decide
  have hdescent : baseEnd_3507873 < baseStart_3507873 := by decide
  rcases family_descends (prefixWord ++ tailWord_3507873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3507894 : List Nat := [5, 1, 3, 1, 1, 1, 1, 4, 2, 3]
def baseStart_3507894 : Nat := 118140960795 + 3507894 * 2 ^ 59
def prefixEnd_3507894 : Nat := 4983230072969 + 3 ^ 40 * 3507894 * 2
def baseEnd_3507894 : Nat := 1200823804682002388194997

theorem tailTrace_3507894 : CollatzResearch.WordTrace tailWord_3507894 prefixEnd_3507894 1200823804682002388194997 := by
  unfold tailWord_3507894
  simp only [CollatzResearch.WordTrace]
  refine ⟨7996462822094163340217171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 85295603435671075628983157 7996462822094163340217171)
  ·
    refine ⟨11994694233141245010325757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7996462822094163340217171 11994694233141245010325757)
    ·
      refine ⟨4498010337427966878872159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11994694233141245010325757 4498010337427966878872159)
      ·
        refine ⟨6747015506141950318308239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4498010337427966878872159 6747015506141950318308239)
        ·
          refine ⟨10120523259212925477462359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6747015506141950318308239 10120523259212925477462359)
          ·
            refine ⟨15180784888819388216193539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10120523259212925477462359 15180784888819388216193539)
            ·
              refine ⟨22771177333229082324290309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15180784888819388216193539 22771177333229082324290309)
              ·
                refine ⟨4269595749980452935804433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22771177333229082324290309 4269595749980452935804433)
                ·
                  refine ⟨3202196812485339701853325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4269595749980452935804433 3202196812485339701853325)
                  ·
                    refine ⟨1200823804682002388194997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3202196812485339701853325 1200823804682002388194997)
                    ·
                      rfl

theorem cell22_3507894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 4, 2, 3].length) (baseStart_3507894 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3507894 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3507894 prefixEnd_3507894 := by exact prefixLift 3507894
  have htrace : WordTrace (prefixWord ++ tailWord_3507894) baseStart_3507894 baseEnd_3507894 := by
    simpa [prefixWord, tailWord_3507894, baseEnd_3507894] using wordTrace_append hprefix tailTrace_3507894
  have hstable : (prefixWord ++ tailWord_3507894).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3507894).length < 2 ^ (prefixWord ++ tailWord_3507894).sum := by decide
  have hdescent : baseEnd_3507894 < baseStart_3507894 := by decide
  rcases family_descends (prefixWord ++ tailWord_3507894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3507922 : List Nat := [3, 2, 2, 2, 2, 2, 1, 2, 3, 3]
def baseStart_3507922 : Nat := 118140960795 + 3507922 * 2 ^ 59
def prefixEnd_3507922 : Nat := 4983230072969 + 3 ^ 40 * 3507922 * 2
def baseEnd_3507922 : Nat := 1200833389654219648494911

theorem tailTrace_3507922 : CollatzResearch.WordTrace tailWord_3507922 prefixEnd_3507922 1200833389654219648494911 := by
  unfold tailWord_3507922
  simp only [CollatzResearch.WordTrace]
  refine ⟨31986106599351293556373505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85296284264936782816996013 31986106599351293556373505)
  ·
    refine ⟨23989579949513470167280129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31986106599351293556373505 23989579949513470167280129)
    ·
      refine ⟨17992184962135102625460097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23989579949513470167280129 17992184962135102625460097)
      ·
        refine ⟨13494138721601326969095073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17992184962135102625460097 13494138721601326969095073)
        ·
          refine ⟨10120604041200995226821305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13494138721601326969095073 10120604041200995226821305)
          ·
            refine ⟨7590453030900746420115979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10120604041200995226821305 7590453030900746420115979)
            ·
              refine ⟨11385679546351119630173969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7590453030900746420115979 11385679546351119630173969)
              ·
                refine ⟨8539259659763339722630477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11385679546351119630173969 8539259659763339722630477)
                ·
                  refine ⟨3202222372411252395986429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8539259659763339722630477 3202222372411252395986429)
                  ·
                    refine ⟨1200833389654219648494911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3202222372411252395986429 1200833389654219648494911)
                    ·
                      rfl

theorem cell22_3507922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 2, 3, 3].length) (baseStart_3507922 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3507922 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3507922 prefixEnd_3507922 := by exact prefixLift 3507922
  have htrace : WordTrace (prefixWord ++ tailWord_3507922) baseStart_3507922 baseEnd_3507922 := by
    simpa [prefixWord, tailWord_3507922, baseEnd_3507922] using wordTrace_append hprefix tailTrace_3507922
  have hstable : (prefixWord ++ tailWord_3507922).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3507922).length < 2 ^ (prefixWord ++ tailWord_3507922).sum := by decide
  have hdescent : baseEnd_3507922 < baseStart_3507922 := by decide
  rcases family_descends (prefixWord ++ tailWord_3507922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3507926 : List Nat := [5, 2, 1, 3, 1, 2, 1, 1, 2, 4]
def baseStart_3507926 : Nat := 118140960795 + 3507926 * 2 ^ 59
def prefixEnd_3507926 : Nat := 4983230072969 + 3 ^ 40 * 3507926 * 2
def baseEnd_3507926 : Nat := 1200834758935964971394899

theorem tailTrace_3507926 : CollatzResearch.WordTrace tailWord_3507926 prefixEnd_3507926 1200834758935964971394899 := by
  unfold tailWord_3507926
  simp only [CollatzResearch.WordTrace]
  refine ⟨7996535768086917681789977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 85296381526260455272426421 7996535768086917681789977)
  ·
    refine ⟨5997401826065188261342483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7996535768086917681789977 5997401826065188261342483)
    ·
      refine ⟨8996102739097782392013725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5997401826065188261342483 8996102739097782392013725)
      ·
        refine ⟨3373538527161668397005147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8996102739097782392013725 3373538527161668397005147)
        ·
          refine ⟨5060307790742502595507721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3373538527161668397005147 5060307790742502595507721)
          ·
            refine ⟨3795230843056876946630791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5060307790742502595507721 3795230843056876946630791)
            ·
              refine ⟨5692846264585315419946187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3795230843056876946630791 5692846264585315419946187)
              ·
                refine ⟨8539269396877973129919281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5692846264585315419946187 8539269396877973129919281)
                ·
                  refine ⟨6404452047658479847439461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8539269396877973129919281 6404452047658479847439461)
                  ·
                    refine ⟨1200834758935964971394899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6404452047658479847439461 1200834758935964971394899)
                    ·
                      rfl

theorem cell22_3507926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 1, 1, 2, 4].length) (baseStart_3507926 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3507926 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3507926 prefixEnd_3507926 := by exact prefixLift 3507926
  have htrace : WordTrace (prefixWord ++ tailWord_3507926) baseStart_3507926 baseEnd_3507926 := by
    simpa [prefixWord, tailWord_3507926, baseEnd_3507926] using wordTrace_append hprefix tailTrace_3507926
  have hstable : (prefixWord ++ tailWord_3507926).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3507926).length < 2 ^ (prefixWord ++ tailWord_3507926).sum := by decide
  have hdescent : baseEnd_3507926 < baseStart_3507926 := by decide
  rcases family_descends (prefixWord ++ tailWord_3507926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3507956 : List Nat := [2, 6, 1, 1, 1, 2, 2, 1, 3, 3]
def baseStart_3507956 : Nat := 118140960795 + 3507956 * 2 ^ 59
def prefixEnd_3507956 : Nat := 4983230072969 + 3 ^ 40 * 3507956 * 2
def baseEnd_3507956 : Nat := 1200845028549054893144807

theorem tailTrace_3507956 : CollatzResearch.WordTrace tailWord_3507956 prefixEnd_3507956 1200845028549054893144807 := by
  unfold tailWord_3507956
  simp only [CollatzResearch.WordTrace]
  refine ⟨63972833239640999016115861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85297110986187998688154481 63972833239640999016115861)
  ·
    refine ⟨2998726558108171828880431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 63972833239640999016115861 2998726558108171828880431)
    ·
      refine ⟨4498089837162257743320647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2998726558108171828880431 4498089837162257743320647)
      ·
        refine ⟨6747134755743386614980971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4498089837162257743320647 6747134755743386614980971)
        ·
          refine ⟨10120702133615079922471457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6747134755743386614980971 10120702133615079922471457)
          ·
            refine ⟨7590526600211309941853593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10120702133615079922471457 7590526600211309941853593)
            ·
              refine ⟨5692894950158482456390195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7590526600211309941853593 5692894950158482456390195)
              ·
                refine ⟨8539342425237723684585293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5692894950158482456390195 8539342425237723684585293)
                ·
                  refine ⟨3202253409464146381719485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8539342425237723684585293 3202253409464146381719485)
                  ·
                    refine ⟨1200845028549054893144807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3202253409464146381719485 1200845028549054893144807)
                    ·
                      rfl

theorem cell22_3507956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 2, 1, 3, 3].length) (baseStart_3507956 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3507956 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3507956 prefixEnd_3507956 := by exact prefixLift 3507956
  have htrace : WordTrace (prefixWord ++ tailWord_3507956) baseStart_3507956 baseEnd_3507956 := by
    simpa [prefixWord, tailWord_3507956, baseEnd_3507956] using wordTrace_append hprefix tailTrace_3507956
  have hstable : (prefixWord ++ tailWord_3507956).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3507956).length < 2 ^ (prefixWord ++ tailWord_3507956).sum := by decide
  have hdescent : baseEnd_3507956 < baseStart_3507956 := by decide
  rcases family_descends (prefixWord ++ tailWord_3507956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3508014 : List Nat := [4, 1, 3, 2, 2, 2, 1, 1, 6]
def baseStart_3508014 : Nat := 118140960795 + 3508014 * 2 ^ 59
def prefixEnd_3508014 : Nat := 4983230072969 + 3 ^ 40 * 3508014 * 2
def baseEnd_3508014 : Nat := 400288294378120691731543

theorem tailTrace_3508014 : CollatzResearch.WordTrace tailWord_3508014 prefixEnd_3508014 400288294378120691731543 := by
  unfold tailWord_3508014
  simp only [CollatzResearch.WordTrace]
  refine ⟨15993472739133984242230387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85298521275381249291895397 15993472739133984242230387)
  ·
    refine ⟨23990209108700976363345581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15993472739133984242230387 23990209108700976363345581)
    ·
      refine ⟨8996328415762866136254593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23990209108700976363345581 8996328415762866136254593)
      ·
        refine ⟨6747246311822149602190945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8996328415762866136254593 6747246311822149602190945)
        ·
          refine ⟨5060434733866612201643209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6747246311822149602190945 5060434733866612201643209)
          ·
            refine ⟨3795326050399959151232407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5060434733866612201643209 3795326050399959151232407)
            ·
              refine ⟨5692989075599938726848611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3795326050399959151232407 5692989075599938726848611)
              ·
                refine ⟨8539483613399908090272917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5692989075599938726848611 8539483613399908090272917)
                ·
                  refine ⟨400288294378120691731543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8539483613399908090272917 400288294378120691731543)
                  ·
                    rfl

theorem cell22_3508014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 1, 1, 6].length) (baseStart_3508014 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3508014 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3508014 prefixEnd_3508014 := by exact prefixLift 3508014
  have htrace : WordTrace (prefixWord ++ tailWord_3508014) baseStart_3508014 baseEnd_3508014 := by
    simpa [prefixWord, tailWord_3508014, baseEnd_3508014] using wordTrace_append hprefix tailTrace_3508014
  have hstable : (prefixWord ++ tailWord_3508014).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3508014).length < 2 ^ (prefixWord ++ tailWord_3508014).sum := by decide
  have hdescent : baseEnd_3508014 < baseStart_3508014 := by decide
  rcases family_descends (prefixWord ++ tailWord_3508014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3508023 : List Nat := [1, 1, 3, 1, 2, 1, 2, 2, 2, 7]
def baseStart_3508023 : Nat := 118140960795 + 3508023 * 2 ^ 59
def prefixEnd_3508023 : Nat := 4983230072969 + 3 ^ 40 * 3508023 * 2
def baseEnd_3508023 : Nat := 1200867964018289051719601

theorem tailTrace_3508023 : CollatzResearch.WordTrace tailWord_3508023 prefixEnd_3508023 1200867964018289051719601 := by
  unfold tailWord_3508023
  simp only [CollatzResearch.WordTrace]
  refine ⟨127948110170039268474920723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85298740113359512316613815 127948110170039268474920723)
  ·
    refine ⟨191922165255058902712381085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127948110170039268474920723 191922165255058902712381085)
    ·
      refine ⟨71970811970647088517142907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 191922165255058902712381085 71970811970647088517142907)
      ·
        refine ⟨107956217955970632775714361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71970811970647088517142907 107956217955970632775714361)
        ·
          refine ⟨80967163466977974581785771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107956217955970632775714361 80967163466977974581785771)
          ·
            refine ⟨121450745200466961872678657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80967163466977974581785771 121450745200466961872678657)
            ·
              refine ⟨91088058900350221404508993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121450745200466961872678657 91088058900350221404508993)
              ·
                refine ⟨68316044175262666053381745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91088058900350221404508993 68316044175262666053381745)
                ·
                  refine ⟨51237033131446999540036309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68316044175262666053381745 51237033131446999540036309)
                  ·
                    refine ⟨1200867964018289051719601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51237033131446999540036309 1200867964018289051719601)
                    ·
                      rfl

theorem cell22_3508023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 2, 2, 7].length) (baseStart_3508023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3508023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3508023 prefixEnd_3508023 := by exact prefixLift 3508023
  have htrace : WordTrace (prefixWord ++ tailWord_3508023) baseStart_3508023 baseEnd_3508023 := by
    simpa [prefixWord, tailWord_3508023, baseEnd_3508023] using wordTrace_append hprefix tailTrace_3508023
  have hstable : (prefixWord ++ tailWord_3508023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3508023).length < 2 ^ (prefixWord ++ tailWord_3508023).sum := by decide
  have hdescent : baseEnd_3508023 < baseStart_3508023 := by decide
  rcases family_descends (prefixWord ++ tailWord_3508023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3508029 : List Nat := [1, 4, 1, 4, 1, 2, 1, 3, 2, 3]
def baseStart_3508029 : Nat := 118140960795 + 3508029 * 2 ^ 59
def prefixEnd_3508029 : Nat := 4983230072969 + 3 ^ 40 * 3508029 * 2
def baseEnd_3508029 : Nat := 1200870017940907036069583

theorem tailTrace_3508029 : CollatzResearch.WordTrace tailWord_3508029 prefixEnd_3508029 1200870017940907036069583 := by
  unfold tailWord_3508029
  simp only [CollatzResearch.WordTrace]
  refine ⟨127948329008017531499639141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85298886005345020999759427 127948329008017531499639141)
  ·
    refine ⟨23990311689003287156182339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 127948329008017531499639141 23990311689003287156182339)
    ·
      refine ⟨35985467533504930734273509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23990311689003287156182339 35985467533504930734273509)
      ·
        refine ⟨6747275162532174512676283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35985467533504930734273509 6747275162532174512676283)
        ·
          refine ⟨10120912743798261769014425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6747275162532174512676283 10120912743798261769014425)
          ·
            refine ⟨7590684557848696326760819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10120912743798261769014425 7590684557848696326760819)
            ·
              refine ⟨11386026836773044490141229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7590684557848696326760819 11386026836773044490141229)
              ·
                refine ⟨4269760063789891683802961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11386026836773044490141229 4269760063789891683802961)
                ·
                  refine ⟨3202320047842418762852221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4269760063789891683802961 3202320047842418762852221)
                  ·
                    refine ⟨1200870017940907036069583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3202320047842418762852221 1200870017940907036069583)
                    ·
                      rfl

theorem cell22_3508029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 3, 2, 3].length) (baseStart_3508029 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3508029 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3508029 prefixEnd_3508029 := by exact prefixLift 3508029
  have htrace : WordTrace (prefixWord ++ tailWord_3508029) baseStart_3508029 baseEnd_3508029 := by
    simpa [prefixWord, tailWord_3508029, baseEnd_3508029] using wordTrace_append hprefix tailTrace_3508029
  have hstable : (prefixWord ++ tailWord_3508029).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3508029).length < 2 ^ (prefixWord ++ tailWord_3508029).sum := by decide
  have hdescent : baseEnd_3508029 < baseStart_3508029 := by decide
  rcases family_descends (prefixWord ++ tailWord_3508029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3508117 : List Nat := [1, 3, 2, 1, 1, 3, 3, 3, 1, 4]
def baseStart_3508117 : Nat := 118140960795 + 3508117 * 2 ^ 59
def prefixEnd_3508117 : Nat := 4983230072969 + 3 ^ 40 * 3508117 * 2
def baseEnd_3508117 : Nat := 1200900142139304139869313

theorem tailTrace_3508117 : CollatzResearch.WordTrace tailWord_3508117 prefixEnd_3508117 1200900142139304139869313 := by
  unfold tailWord_3508117
  simp only [CollatzResearch.WordTrace]
  refine ⟨127951538631698722528842605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85301025754465815019228403 127951538631698722528842605)
  ·
    refine ⟨47981826986887020948315977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127951538631698722528842605 47981826986887020948315977)
    ·
      refine ⟨35986370240165265711236983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47981826986887020948315977 35986370240165265711236983)
      ·
        refine ⟨53979555360247898566855475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35986370240165265711236983 53979555360247898566855475)
        ·
          refine ⟨80969333040371847850283213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53979555360247898566855475 80969333040371847850283213)
          ·
            refine ⟨30363499890139442943856205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80969333040371847850283213 30363499890139442943856205)
            ·
              refine ⟨11386312458802291103946077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30363499890139442943856205 11386312458802291103946077)
              ·
                refine ⟨4269867172050859163979779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11386312458802291103946077 4269867172050859163979779)
                ·
                  refine ⟨6404800758076288745969669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4269867172050859163979779 6404800758076288745969669)
                  ·
                    refine ⟨1200900142139304139869313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6404800758076288745969669 1200900142139304139869313)
                    ·
                      rfl

theorem cell22_3508117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 3, 1, 4].length) (baseStart_3508117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3508117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3508117 prefixEnd_3508117 := by exact prefixLift 3508117
  have htrace : WordTrace (prefixWord ++ tailWord_3508117) baseStart_3508117 baseEnd_3508117 := by
    simpa [prefixWord, tailWord_3508117, baseEnd_3508117] using wordTrace_append hprefix tailTrace_3508117
  have hstable : (prefixWord ++ tailWord_3508117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3508117).length < 2 ^ (prefixWord ++ tailWord_3508117).sum := by decide
  have hdescent : baseEnd_3508117 < baseStart_3508117 := by decide
  rcases family_descends (prefixWord ++ tailWord_3508117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3508132 : List Nat := [2, 3, 1, 2, 1, 4, 2, 1, 6]
def baseStart_3508132 : Nat := 118140960795 + 3508132 * 2 ^ 59
def prefixEnd_3508132 : Nat := 4983230072969 + 3 ^ 40 * 3508132 * 2
def baseEnd_3508132 : Nat := 400301758981949700248089

theorem tailTrace_3508132 : CollatzResearch.WordTrace tailWord_3508132 prefixEnd_3508132 400301758981949700248089 := by
  unfold tailWord_3508132
  simp only [CollatzResearch.WordTrace]
  refine ⟨63976042863322190045319325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85301390484429586727092433 63976042863322190045319325)
  ·
    refine ⟨23991016073745821266994747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63976042863322190045319325 23991016073745821266994747)
    ·
      refine ⟨35986524110618731900492121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23991016073745821266994747 35986524110618731900492121)
      ·
        refine ⟨26989893082964048925369091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35986524110618731900492121 26989893082964048925369091)
        ·
          refine ⟨40484839624446073388053637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26989893082964048925369091 40484839624446073388053637)
          ·
            refine ⟨7590907429583638760260057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40484839624446073388053637 7590907429583638760260057)
            ·
              refine ⟨5693180572187729070195043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7590907429583638760260057 5693180572187729070195043)
              ·
                refine ⟨8539770858281593605292565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5693180572187729070195043 8539770858281593605292565)
                ·
                  refine ⟨400301758981949700248089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8539770858281593605292565 400301758981949700248089)
                  ·
                    rfl

theorem cell22_3508132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 2, 1, 6].length) (baseStart_3508132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3508132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3508132 prefixEnd_3508132 := by exact prefixLift 3508132
  have htrace : WordTrace (prefixWord ++ tailWord_3508132) baseStart_3508132 baseEnd_3508132 := by
    simpa [prefixWord, tailWord_3508132, baseEnd_3508132] using wordTrace_append hprefix tailTrace_3508132
  have hstable : (prefixWord ++ tailWord_3508132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3508132).length < 2 ^ (prefixWord ++ tailWord_3508132).sum := by decide
  have hdescent : baseEnd_3508132 < baseStart_3508132 := by decide
  rcases family_descends (prefixWord ++ tailWord_3508132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3508160 : List Nat := [2, 1, 1, 2, 3, 2, 3, 8]
def baseStart_3508160 : Nat := 118140960795 + 3508160 * 2 ^ 59
def prefixEnd_3508160 : Nat := 4983230072969 + 3 ^ 40 * 3508160 * 2
def baseEnd_3508160 : Nat := 133434984657562929004909

theorem tailTrace_3508160 : CollatzResearch.WordTrace tailWord_3508160 prefixEnd_3508160 133434984657562929004909 := by
  unfold tailWord_3508160
  simp only [CollatzResearch.WordTrace]
  refine ⟨63976553485271470436328967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85302071313695293915105289 63976553485271470436328967)
  ·
    refine ⟨95964830227907205654493451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63976553485271470436328967 95964830227907205654493451)
    ·
      refine ⟨143947245341860808481740177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95964830227907205654493451 143947245341860808481740177)
      ·
        refine ⟨107960434006395606361305133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143947245341860808481740177 107960434006395606361305133)
        ·
          refine ⟨40485162752398352385489425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107960434006395606361305133 40485162752398352385489425)
          ·
            refine ⟨30363872064298764289117069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40485162752398352385489425 30363872064298764289117069)
            ·
              refine ⟨11386452024112036608418901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30363872064298764289117069 11386452024112036608418901)
              ·
                refine ⟨133434984657562929004909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11386452024112036608418901 133434984657562929004909)
                ·
                  rfl

theorem cell22_3508160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 8].length) (baseStart_3508160 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3508160 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3508160 prefixEnd_3508160 := by exact prefixLift 3508160
  have htrace : WordTrace (prefixWord ++ tailWord_3508160) baseStart_3508160 baseEnd_3508160 := by
    simpa [prefixWord, tailWord_3508160, baseEnd_3508160] using wordTrace_append hprefix tailTrace_3508160
  have hstable : (prefixWord ++ tailWord_3508160).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3508160).length < 2 ^ (prefixWord ++ tailWord_3508160).sum := by decide
  have hdescent : baseEnd_3508160 < baseStart_3508160 := by decide
  rcases family_descends (prefixWord ++ tailWord_3508160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3508297 : List Nat := [1, 2, 1, 1, 2, 2, 4, 1, 4, 4]
def baseStart_3508297 : Nat := 118140960795 + 3508297 * 2 ^ 59
def prefixEnd_3508297 : Nat := 4983230072969 + 3 ^ 40 * 3508297 * 2
def baseEnd_3508297 : Nat := 1200961759817843670368761

theorem tailTrace_3508297 : CollatzResearch.WordTrace tailWord_3508297 prefixEnd_3508297 1200961759817843670368761 := by
  unfold tailWord_3508297
  simp only [CollatzResearch.WordTrace]
  refine ⟨127958103771046613270395145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85305402514031075513596763 127958103771046613270395145)
  ·
    refine ⟨95968577828284959952796359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127958103771046613270395145 95968577828284959952796359)
    ·
      refine ⟨143952866742427439929194539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95968577828284959952796359 143952866742427439929194539)
      ·
        refine ⟨215929300113641159893791809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143952866742427439929194539 215929300113641159893791809)
        ·
          refine ⟨161946975085230869920343857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 215929300113641159893791809 161946975085230869920343857)
          ·
            refine ⟨121460231313923152440257893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 161946975085230869920343857 121460231313923152440257893)
            ·
              refine ⟨22773793371360591082548355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 121460231313923152440257893 22773793371360591082548355)
              ·
                refine ⟨34160690057040886623822533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22773793371360591082548355 34160690057040886623822533)
                ·
                  refine ⟨6405129385695166241966725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34160690057040886623822533 6405129385695166241966725)
                  ·
                    refine ⟨1200961759817843670368761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6405129385695166241966725 1200961759817843670368761)
                    ·
                      rfl

theorem cell22_3508297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 1, 4, 4].length) (baseStart_3508297 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3508297 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3508297 prefixEnd_3508297 := by exact prefixLift 3508297
  have htrace : WordTrace (prefixWord ++ tailWord_3508297) baseStart_3508297 baseEnd_3508297 := by
    simpa [prefixWord, tailWord_3508297, baseEnd_3508297] using wordTrace_append hprefix tailTrace_3508297
  have hstable : (prefixWord ++ tailWord_3508297).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3508297).length < 2 ^ (prefixWord ++ tailWord_3508297).sum := by decide
  have hdescent : baseEnd_3508297 < baseStart_3508297 := by decide
  rcases family_descends (prefixWord ++ tailWord_3508297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3508301 : List Nat := [1, 6, 1, 1, 1, 1, 1, 6, 4]
def baseStart_3508301 : Nat := 118140960795 + 3508301 * 2 ^ 59
def prefixEnd_3508301 : Nat := 4983230072969 + 3 ^ 40 * 3508301 * 2
def baseEnd_3508301 : Nat := 400321043033196331089583

theorem tailTrace_3508301 : CollatzResearch.WordTrace tailWord_3508301 prefixEnd_3508301 400321043033196331089583 := by
  unfold tailWord_3508301
  simp only [CollatzResearch.WordTrace]
  refine ⟨127958249663032121953540757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85305499775354747969027171 127958249663032121953540757)
  ·
    refine ⟨5998042952954630716572223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 127958249663032121953540757 5998042952954630716572223)
    ·
      refine ⟨8997064429431946074858335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5998042952954630716572223 8997064429431946074858335)
      ·
        refine ⟨13495596644147919112287503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8997064429431946074858335 13495596644147919112287503)
        ·
          refine ⟨20243394966221878668431255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13495596644147919112287503 20243394966221878668431255)
          ·
            refine ⟨30365092449332818002646883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20243394966221878668431255 30365092449332818002646883)
            ·
              refine ⟨45547638673999227003970325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30365092449332818002646883 45547638673999227003970325)
              ·
                refine ⟨2135045562843713765811109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 45547638673999227003970325 2135045562843713765811109)
                ·
                  refine ⟨400321043033196331089583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2135045562843713765811109 400321043033196331089583)
                  ·
                    rfl

theorem cell22_3508301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 6, 4].length) (baseStart_3508301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3508301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3508301 prefixEnd_3508301 := by exact prefixLift 3508301
  have htrace : WordTrace (prefixWord ++ tailWord_3508301) baseStart_3508301 baseEnd_3508301 := by
    simpa [prefixWord, tailWord_3508301, baseEnd_3508301] using wordTrace_append hprefix tailTrace_3508301
  have hstable : (prefixWord ++ tailWord_3508301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3508301).length < 2 ^ (prefixWord ++ tailWord_3508301).sum := by decide
  have hdescent : baseEnd_3508301 < baseStart_3508301 := by decide
  rcases family_descends (prefixWord ++ tailWord_3508301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3508316 : List Nat := [2, 2, 4, 1, 1, 4, 1, 1, 1, 5]
def baseStart_3508316 : Nat := 118140960795 + 3508316 * 2 ^ 59
def prefixEnd_3508316 : Nat := 4983230072969 + 3 ^ 40 * 3508316 * 2
def baseEnd_3508316 : Nat := 1200968263906133954143703

theorem tailTrace_3508316 : CollatzResearch.WordTrace tailWord_3508316 prefixEnd_3508316 1200968263906133954143703 := by
  unfold tailWord_3508316
  simp only [CollatzResearch.WordTrace]
  refine ⟨63979398378988889757668401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85305864505318519676891201 63979398378988889757668401)
  ·
    refine ⟨47984548784241667318251301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63979398378988889757668401 47984548784241667318251301)
    ·
      refine ⟨8997102897045312622172119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47984548784241667318251301 8997102897045312622172119)
      ·
        refine ⟨13495654345567968933258179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8997102897045312622172119 13495654345567968933258179)
        ·
          refine ⟨20243481518351953399887269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13495654345567968933258179 20243481518351953399887269)
          ·
            refine ⟨3795652784690991262478863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20243481518351953399887269 3795652784690991262478863)
            ·
              refine ⟨5693479177036486893718295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3795652784690991262478863 5693479177036486893718295)
              ·
                refine ⟨8540218765554730340577443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5693479177036486893718295 8540218765554730340577443)
                ·
                  refine ⟨12810328148332095510866165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8540218765554730340577443 12810328148332095510866165)
                  ·
                    refine ⟨1200968263906133954143703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12810328148332095510866165 1200968263906133954143703)
                    ·
                      rfl

theorem cell22_3508316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 1, 1, 1, 5].length) (baseStart_3508316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3508316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3508316 prefixEnd_3508316 := by exact prefixLift 3508316
  have htrace : WordTrace (prefixWord ++ tailWord_3508316) baseStart_3508316 baseEnd_3508316 := by
    simpa [prefixWord, tailWord_3508316, baseEnd_3508316] using wordTrace_append hprefix tailTrace_3508316
  have hstable : (prefixWord ++ tailWord_3508316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3508316).length < 2 ^ (prefixWord ++ tailWord_3508316).sum := by decide
  have hdescent : baseEnd_3508316 < baseStart_3508316 := by decide
  rcases family_descends (prefixWord ++ tailWord_3508316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3508327 : List Nat := [1, 1, 5, 1, 1, 2, 1, 1, 2, 7]
def baseStart_3508327 : Nat := 118140960795 + 3508327 * 2 ^ 59
def prefixEnd_3508327 : Nat := 4983230072969 + 3 ^ 40 * 3508327 * 2
def baseEnd_3508327 : Nat := 1200972029430933592118669

theorem tailTrace_3508327 : CollatzResearch.WordTrace tailWord_3508327 prefixEnd_3508327 1200972029430933592118669 := by
  unfold tailWord_3508327
  simp only [CollatzResearch.WordTrace]
  refine ⟨127959197960937928393987235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85306131973958618929324823 127959197960937928393987235)
  ·
    refine ⟨191938796941406892590980853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127959197960937928393987235 191938796941406892590980853)
    ·
      refine ⟨17994262213256896180404455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 191938796941406892590980853 17994262213256896180404455)
      ·
        refine ⟨26991393319885344270606683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17994262213256896180404455 26991393319885344270606683)
        ·
          refine ⟨40487089979828016405910025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26991393319885344270606683 40487089979828016405910025)
          ·
            refine ⟨30365317484871012304432519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40487089979828016405910025 30365317484871012304432519)
            ·
              refine ⟨45547976227306518456648779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30365317484871012304432519 45547976227306518456648779)
              ·
                refine ⟨68321964340959777684973169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45547976227306518456648779 68321964340959777684973169)
                ·
                  refine ⟨51241473255719833263729877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68321964340959777684973169 51241473255719833263729877)
                  ·
                    refine ⟨1200972029430933592118669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51241473255719833263729877 1200972029430933592118669)
                    ·
                      rfl

theorem cell22_3508327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 1, 2, 7].length) (baseStart_3508327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3508327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3508327 prefixEnd_3508327 := by exact prefixLift 3508327
  have htrace : WordTrace (prefixWord ++ tailWord_3508327) baseStart_3508327 baseEnd_3508327 := by
    simpa [prefixWord, tailWord_3508327, baseEnd_3508327] using wordTrace_append hprefix tailTrace_3508327
  have hstable : (prefixWord ++ tailWord_3508327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3508327).length < 2 ^ (prefixWord ++ tailWord_3508327).sum := by decide
  have hdescent : baseEnd_3508327 < baseStart_3508327 := by decide
  rcases family_descends (prefixWord ++ tailWord_3508327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3508412 : List Nat := [2, 2, 2, 3, 3, 2, 2, 2, 1, 3]
def baseStart_3508412 : Nat := 118140960795 + 3508412 * 2 ^ 59
def prefixEnd_3508412 : Nat := 4983230072969 + 3 ^ 40 * 3508412 * 2
def baseEnd_3508412 : Nat := 1201001126668021703743409

theorem tailTrace_3508412 : CollatzResearch.WordTrace tailWord_3508412 prefixEnd_3508412 1201001126668021703743409 := by
  unfold tailWord_3508412
  simp only [CollatzResearch.WordTrace]
  refine ⟨63981149082814993955415745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85308198777086658607220993 63981149082814993955415745)
  ·
    refine ⟨47985861812111245466561809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63981149082814993955415745 47985861812111245466561809)
    ·
      refine ⟨35989396359083434099921357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47985861812111245466561809 35989396359083434099921357)
      ·
        refine ⟨13496023634656287787470509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35989396359083434099921357 13496023634656287787470509)
        ·
          refine ⟨5061008862996107920301441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13496023634656287787470509 5061008862996107920301441)
          ·
            refine ⟨3795756647247080940226081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5061008862996107920301441 3795756647247080940226081)
            ·
              refine ⟨2846817485435310705169561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3795756647247080940226081 2846817485435310705169561)
              ·
                refine ⟨2135113114076483028877171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2846817485435310705169561 2135113114076483028877171)
                ·
                  refine ⟨3202669671114724543315757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2135113114076483028877171 3202669671114724543315757)
                  ·
                    refine ⟨1201001126668021703743409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3202669671114724543315757 1201001126668021703743409)
                    ·
                      rfl

theorem cell22_3508412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 2, 2, 1, 3].length) (baseStart_3508412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3508412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3508412 prefixEnd_3508412 := by exact prefixLift 3508412
  have htrace : WordTrace (prefixWord ++ tailWord_3508412) baseStart_3508412 baseEnd_3508412 := by
    simpa [prefixWord, tailWord_3508412, baseEnd_3508412] using wordTrace_append hprefix tailTrace_3508412
  have hstable : (prefixWord ++ tailWord_3508412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3508412).length < 2 ^ (prefixWord ++ tailWord_3508412).sum := by decide
  have hdescent : baseEnd_3508412 < baseStart_3508412 := by decide
  rcases family_descends (prefixWord ++ tailWord_3508412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3508438 : List Nat := [5, 2, 1, 2, 1, 1, 2, 1, 3, 4]
def baseStart_3508438 : Nat := 118140960795 + 3508438 * 2 ^ 59
def prefixEnd_3508438 : Nat := 4983230072969 + 3 ^ 40 * 3508438 * 2
def baseEnd_3508438 : Nat := 1201010026999366302593329

theorem tailTrace_3508438 : CollatzResearch.WordTrace tailWord_3508438 prefixEnd_3508438 1201010026999366302593329 := by
  unfold tailWord_3508438
  simp only [CollatzResearch.WordTrace]
  refine ⟨7997702903970987146954873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 85308830975690529567518645 7997702903970987146954873)
  ·
    refine ⟨5998277177978240360216155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7997702903970987146954873 5998277177978240360216155)
    ·
      refine ⟨8997415766967360540324233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5998277177978240360216155 8997415766967360540324233)
      ·
        refine ⟨6748061825225520405243175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8997415766967360540324233 6748061825225520405243175)
        ·
          refine ⟨10122092737838280607864763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6748061825225520405243175 10122092737838280607864763)
          ·
            refine ⟨15183139106757420911797145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10122092737838280607864763 15183139106757420911797145)
            ·
              refine ⟨11387354330068065683847859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15183139106757420911797145 11387354330068065683847859)
              ·
                refine ⟨17081031495102098525771789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11387354330068065683847859 17081031495102098525771789)
                ·
                  refine ⟨6405386810663286947164421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17081031495102098525771789 6405386810663286947164421)
                  ·
                    refine ⟨1201010026999366302593329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6405386810663286947164421 1201010026999366302593329)
                    ·
                      rfl

theorem cell22_3508438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 1, 3, 4].length) (baseStart_3508438 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3508438 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3508438 prefixEnd_3508438 := by exact prefixLift 3508438
  have htrace : WordTrace (prefixWord ++ tailWord_3508438) baseStart_3508438 baseEnd_3508438 := by
    simpa [prefixWord, tailWord_3508438, baseEnd_3508438] using wordTrace_append hprefix tailTrace_3508438
  have hstable : (prefixWord ++ tailWord_3508438).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3508438).length < 2 ^ (prefixWord ++ tailWord_3508438).sum := by decide
  have hdescent : baseEnd_3508438 < baseStart_3508438 := by decide
  rcases family_descends (prefixWord ++ tailWord_3508438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3508449 : List Nat := [1, 2, 3, 1, 3, 1, 3, 1, 1, 6]
def baseStart_3508449 : Nat := 118140960795 + 3508449 * 2 ^ 59
def prefixEnd_3508449 : Nat := 4983230072969 + 3 ^ 40 * 3508449 * 2
def baseEnd_3508449 : Nat := 1201013792524165940568295

theorem tailTrace_3508449 : CollatzResearch.WordTrace tailWord_3508449 prefixEnd_3508449 1201013792524165940568295 := by
  unfold tailWord_3508449
  simp only [CollatzResearch.WordTrace]
  refine ⟨127963647666495943229928401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85309098444330628819952267 127963647666495943229928401)
  ·
    refine ⟨95972735749871957422446301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127963647666495943229928401 95972735749871957422446301)
    ·
      refine ⟨35989775906201984033417363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95972735749871957422446301 35989775906201984033417363)
      ·
        refine ⟨53984663859302976050126045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35989775906201984033417363 53984663859302976050126045)
        ·
          refine ⟨20244248947238616018797267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53984663859302976050126045 20244248947238616018797267)
          ·
            refine ⟨30366373420857924028195901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20244248947238616018797267 30366373420857924028195901)
            ·
              refine ⟨11387390032821721510573463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30366373420857924028195901 11387390032821721510573463)
              ·
                refine ⟨17081085049232582265860195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11387390032821721510573463 17081085049232582265860195)
                ·
                  refine ⟨25621627573848873398790293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17081085049232582265860195 25621627573848873398790293)
                  ·
                    refine ⟨1201013792524165940568295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25621627573848873398790293 1201013792524165940568295)
                    ·
                      rfl

theorem cell22_3508449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 1, 1, 6].length) (baseStart_3508449 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3508449 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3508449 prefixEnd_3508449 := by exact prefixLift 3508449
  have htrace : WordTrace (prefixWord ++ tailWord_3508449) baseStart_3508449 baseEnd_3508449 := by
    simpa [prefixWord, tailWord_3508449, baseEnd_3508449] using wordTrace_append hprefix tailTrace_3508449
  have hstable : (prefixWord ++ tailWord_3508449).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3508449).length < 2 ^ (prefixWord ++ tailWord_3508449).sum := by decide
  have hdescent : baseEnd_3508449 < baseStart_3508449 := by decide
  rcases family_descends (prefixWord ++ tailWord_3508449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3508453 : List Nat := [1, 3, 1, 4, 2, 2, 2, 3, 4]
def baseStart_3508453 : Nat := 118140960795 + 3508453 * 2 ^ 59
def prefixEnd_3508453 : Nat := 4983230072969 + 3 ^ 40 * 3508453 * 2
def baseEnd_3508453 : Nat := 400338387268637087822761

theorem tailTrace_3508453 : CollatzResearch.WordTrace tailWord_3508453 prefixEnd_3508453 400338387268637087822761 := by
  unfold tailWord_3508453
  simp only [CollatzResearch.WordTrace]
  refine ⟨127963793558481451913074013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85309195705654301275382675 127963793558481451913074013)
  ·
    refine ⟨47986422584430544467402755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127963793558481451913074013 47986422584430544467402755)
    ·
      refine ⟨71979633876645816701104133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47986422584430544467402755 71979633876645816701104133)
      ·
        refine ⟨13496181351871090631457025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71979633876645816701104133 13496181351871090631457025)
        ·
          refine ⟨10122136013903317973592769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13496181351871090631457025 10122136013903317973592769)
          ·
            refine ⟨7591602010427488480194577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10122136013903317973592769 7591602010427488480194577)
            ·
              refine ⟨5693701507820616360145933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7591602010427488480194577 5693701507820616360145933)
              ·
                refine ⟨2135138065432731135054725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5693701507820616360145933 2135138065432731135054725)
                ·
                  refine ⟨400338387268637087822761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2135138065432731135054725 400338387268637087822761)
                  ·
                    rfl

theorem cell22_3508453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 2, 3, 4].length) (baseStart_3508453 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3508453 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3508453 prefixEnd_3508453 := by exact prefixLift 3508453
  have htrace : WordTrace (prefixWord ++ tailWord_3508453) baseStart_3508453 baseEnd_3508453 := by
    simpa [prefixWord, tailWord_3508453, baseEnd_3508453] using wordTrace_append hprefix tailTrace_3508453
  have hstable : (prefixWord ++ tailWord_3508453).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3508453).length < 2 ^ (prefixWord ++ tailWord_3508453).sum := by decide
  have hdescent : baseEnd_3508453 < baseStart_3508453 := by decide
  rcases family_descends (prefixWord ++ tailWord_3508453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3508455 : List Nat := [1, 1, 5, 3, 1, 3, 2, 1, 1, 4]
def baseStart_3508455 : Nat := 118140960795 + 3508455 * 2 ^ 59
def prefixEnd_3508455 : Nat := 4983230072969 + 3 ^ 40 * 3508455 * 2
def baseEnd_3508455 : Nat := 1201015846446783924918277

theorem tailTrace_3508455 : CollatzResearch.WordTrace tailWord_3508455 prefixEnd_3508455 1201015846446783924918277 := by
  unfold tailWord_3508455
  simp only [CollatzResearch.WordTrace]
  refine ⟨127963866504474206254646819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85309244336316137503097879 127963866504474206254646819)
  ·
    refine ⟨191945799756711309381970229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127963866504474206254646819 191945799756711309381970229)
    ·
      refine ⟨17994918727191685254559709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 191945799756711309381970229 17994918727191685254559709)
      ·
        refine ⟨6748094522696881970459891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17994918727191685254559709 6748094522696881970459891)
        ·
          refine ⟨10122141784045322955689837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6748094522696881970459891 10122141784045322955689837)
          ·
            refine ⟨3795803169016996108383689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10122141784045322955689837 3795803169016996108383689)
            ·
              refine ⟨2846852376762747081287767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3795803169016996108383689 2846852376762747081287767)
              ·
                refine ⟨4270278565144120621931651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2846852376762747081287767 4270278565144120621931651)
                ·
                  refine ⟨6405417847716180932897477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4270278565144120621931651 6405417847716180932897477)
                  ·
                    refine ⟨1201015846446783924918277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6405417847716180932897477 1201015846446783924918277)
                    ·
                      rfl

theorem cell22_3508455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 2, 1, 1, 4].length) (baseStart_3508455 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3508455 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3508455 prefixEnd_3508455 := by exact prefixLift 3508455
  have htrace : WordTrace (prefixWord ++ tailWord_3508455) baseStart_3508455 baseEnd_3508455 := by
    simpa [prefixWord, tailWord_3508455, baseEnd_3508455] using wordTrace_append hprefix tailTrace_3508455
  have hstable : (prefixWord ++ tailWord_3508455).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3508455).length < 2 ^ (prefixWord ++ tailWord_3508455).sum := by decide
  have hdescent : baseEnd_3508455 < baseStart_3508455 := by decide
  rcases family_descends (prefixWord ++ tailWord_3508455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3508524 : List Nat := [2, 2, 1, 1, 1, 3, 2, 1, 4, 5]
def baseStart_3508524 : Nat := 118140960795 + 3508524 * 2 ^ 59
def prefixEnd_3508524 : Nat := 4983230072969 + 3 ^ 40 * 3508524 * 2
def baseEnd_3508524 : Nat := 1201039466556890744943065

theorem tailTrace_3508524 : CollatzResearch.WordTrace tailWord_3508524 prefixEnd_3508524 1201039466556890744943065 := by
  unfold tailWord_3508524
  simp only [CollatzResearch.WordTrace]
  refine ⟨63983191570612115519454313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85310922094149487359272417 63983191570612115519454313)
  ·
    refine ⟨47987393677959086639590735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63983191570612115519454313 47987393677959086639590735)
    ·
      refine ⟨71981090516938629959386103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47987393677959086639590735 71981090516938629959386103)
      ·
        refine ⟨107971635775407944939079155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71981090516938629959386103 107971635775407944939079155)
        ·
          refine ⟨161957453663111917408618733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107971635775407944939079155 161957453663111917408618733)
          ·
            refine ⟨60734045123666969028232025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 161957453663111917408618733 60734045123666969028232025)
            ·
              refine ⟨45550533842750226771174019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60734045123666969028232025 45550533842750226771174019)
              ·
                refine ⟨68325800764125340156761029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45550533842750226771174019 68325800764125340156761029)
                ·
                  refine ⟨12811087643273501279392693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 68325800764125340156761029 12811087643273501279392693)
                  ·
                    refine ⟨1201039466556890744943065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12811087643273501279392693 1201039466556890744943065)
                    ·
                      rfl

theorem cell22_3508524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 5].length) (baseStart_3508524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3508524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3508524 prefixEnd_3508524 := by exact prefixLift 3508524
  have htrace : WordTrace (prefixWord ++ tailWord_3508524) baseStart_3508524 baseEnd_3508524 := by
    simpa [prefixWord, tailWord_3508524, baseEnd_3508524] using wordTrace_append hprefix tailTrace_3508524
  have hstable : (prefixWord ++ tailWord_3508524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3508524).length < 2 ^ (prefixWord ++ tailWord_3508524).sum := by decide
  have hdescent : baseEnd_3508524 < baseStart_3508524 := by decide
  rcases family_descends (prefixWord ++ tailWord_3508524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3508530 : List Nat := [3, 2, 1, 1, 5, 2, 1, 1, 3, 3]
def baseStart_3508530 : Nat := 118140960795 + 3508530 * 2 ^ 59
def prefixEnd_3508530 : Nat := 4983230072969 + 3 ^ 40 * 3508530 * 2
def baseEnd_3508530 : Nat := 1201041520479508729293047

theorem tailTrace_3508530 : CollatzResearch.WordTrace tailWord_3508530 prefixEnd_3508530 1201041520479508729293047 := by
  unfold tailWord_3508530
  simp only [CollatzResearch.WordTrace]
  refine ⟨31991650494800623515906761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85311067986134996042418029 31991650494800623515906761)
  ·
    refine ⟨23993737871100467636930071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31991650494800623515906761 23993737871100467636930071)
    ·
      refine ⟨35990606806650701455395107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23993737871100467636930071 35990606806650701455395107)
      ·
        refine ⟨53985910209976052183092661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35990606806650701455395107 53985910209976052183092661)
        ·
          refine ⟨5061179082185254892164937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 53985910209976052183092661 5061179082185254892164937)
          ·
            refine ⟨3795884311638941169123703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5061179082185254892164937 3795884311638941169123703)
            ·
              refine ⟨5693826467458411753685555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3795884311638941169123703 5693826467458411753685555)
              ·
                refine ⟨8540739701187617630528333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5693826467458411753685555 8540739701187617630528333)
                ·
                  refine ⟨3202777387945356611448125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8540739701187617630528333 3202777387945356611448125)
                  ·
                    refine ⟨1201041520479508729293047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3202777387945356611448125 1201041520479508729293047)
                    ·
                      rfl

theorem cell22_3508530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 1, 1, 3, 3].length) (baseStart_3508530 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3508530 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3508530 prefixEnd_3508530 := by exact prefixLift 3508530
  have htrace : WordTrace (prefixWord ++ tailWord_3508530) baseStart_3508530 baseEnd_3508530 := by
    simpa [prefixWord, tailWord_3508530, baseEnd_3508530] using wordTrace_append hprefix tailTrace_3508530
  have hstable : (prefixWord ++ tailWord_3508530).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3508530).length < 2 ^ (prefixWord ++ tailWord_3508530).sum := by decide
  have hdescent : baseEnd_3508530 < baseStart_3508530 := by decide
  rcases family_descends (prefixWord ++ tailWord_3508530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3508556 : List Nat := [2, 2, 1, 3, 2, 1, 3, 1, 3, 4]
def baseStart_3508556 : Nat := 118140960795 + 3508556 * 2 ^ 59
def prefixEnd_3508556 : Nat := 4983230072969 + 3 ^ 40 * 3508556 * 2
def baseEnd_3508556 : Nat := 1201050420810853328142967

theorem tailTrace_3508556 : CollatzResearch.WordTrace tailWord_3508556 prefixEnd_3508556 1201050420810853328142967 := by
  unfold tailWord_3508556
  simp only [CollatzResearch.WordTrace]
  refine ⟨63983775138554150252036761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85311700184738867002715681 63983775138554150252036761)
  ·
    refine ⟨47987831353915612689027571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63983775138554150252036761 47987831353915612689027571)
    ·
      refine ⟨71981747030873419033541357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47987831353915612689027571 71981747030873419033541357)
      ·
        refine ⟨26993155136577532137578009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71981747030873419033541357 26993155136577532137578009)
        ·
          refine ⟨20244866352433149103183507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26993155136577532137578009 20244866352433149103183507)
          ·
            refine ⟨30367299528649723654775261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20244866352433149103183507 30367299528649723654775261)
            ·
              refine ⟨11387737323243646370540723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30367299528649723654775261 11387737323243646370540723)
              ·
                refine ⟨17081605984865469555811085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11387737323243646370540723 17081605984865469555811085)
                ·
                  refine ⟨6405602244324551083429157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17081605984865469555811085 6405602244324551083429157)
                  ·
                    refine ⟨1201050420810853328142967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6405602244324551083429157 1201050420810853328142967)
                    ·
                      rfl

theorem cell22_3508556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 1, 3, 4].length) (baseStart_3508556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3508556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3508556 prefixEnd_3508556 := by exact prefixLift 3508556
  have htrace : WordTrace (prefixWord ++ tailWord_3508556) baseStart_3508556 baseEnd_3508556 := by
    simpa [prefixWord, tailWord_3508556, baseEnd_3508556] using wordTrace_append hprefix tailTrace_3508556
  have hstable : (prefixWord ++ tailWord_3508556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3508556).length < 2 ^ (prefixWord ++ tailWord_3508556).sum := by decide
  have hdescent : baseEnd_3508556 < baseStart_3508556 := by decide
  rcases family_descends (prefixWord ++ tailWord_3508556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3508599 : List Nat := [1, 1, 3, 1, 1, 2, 2, 11]
def baseStart_3508599 : Nat := 118140960795 + 3508599 * 2 ^ 59
def prefixEnd_3508599 : Nat := 4983230072969 + 3 ^ 40 * 3508599 * 2
def baseEnd_3508599 : Nat := 133451682287735061035315

theorem tailTrace_3508599 : CollatzResearch.WordTrace tailWord_3508599 prefixEnd_3508599 133451682287735061035315 := by
  unfold tailWord_3508599
  simp only [CollatzResearch.WordTrace]
  refine ⟨127969118615952518847888851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85312745743968345898592567 127969118615952518847888851)
  ·
    refine ⟨191953677923928778271833277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127969118615952518847888851 191953677923928778271833277)
    ·
      refine ⟨71982629221473291851937479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 191953677923928778271833277 71982629221473291851937479)
      ·
        refine ⟨107973943832209937777906219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71982629221473291851937479 107973943832209937777906219)
        ·
          refine ⟨161960915748314906666859329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107973943832209937777906219 161960915748314906666859329)
          ·
            refine ⟨121470686811236180000144497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 161960915748314906666859329 121470686811236180000144497)
            ·
              refine ⟨91103015108427135000108373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121470686811236180000144497 91103015108427135000108373)
              ·
                refine ⟨133451682287735061035315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 91103015108427135000108373 133451682287735061035315)
                ·
                  rfl

theorem cell22_3508599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 11].length) (baseStart_3508599 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3508599 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3508599 prefixEnd_3508599 := by exact prefixLift 3508599
  have htrace : WordTrace (prefixWord ++ tailWord_3508599) baseStart_3508599 baseEnd_3508599 := by
    simpa [prefixWord, tailWord_3508599, baseEnd_3508599] using wordTrace_append hprefix tailTrace_3508599
  have hstable : (prefixWord ++ tailWord_3508599).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3508599).length < 2 ^ (prefixWord ++ tailWord_3508599).sum := by decide
  have hdescent : baseEnd_3508599 < baseStart_3508599 := by decide
  rcases family_descends (prefixWord ++ tailWord_3508599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3508603 : List Nat := [1, 1, 1, 1, 1, 7, 2, 3, 2, 3]
def baseStart_3508603 : Nat := 118140960795 + 3508603 * 2 ^ 59
def prefixEnd_3508603 : Nat := 4983230072969 + 3 ^ 40 * 3508603 * 2
def baseEnd_3508603 : Nat := 1201066509871360872217823

theorem tailTrace_3508603 : CollatzResearch.WordTrace tailWord_3508603 prefixEnd_3508603 1201066509871360872217823 := by
  unfold tailWord_3508603
  simp only [CollatzResearch.WordTrace]
  refine ⟨127969264507938027531034463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85312843005292018354022975 127969264507938027531034463)
  ·
    refine ⟨191953896761907041296551695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127969264507938027531034463 191953896761907041296551695)
    ·
      refine ⟨287930845142860561944827543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191953896761907041296551695 287930845142860561944827543)
      ·
        refine ⟨431896267714290842917241315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287930845142860561944827543 431896267714290842917241315)
        ·
          refine ⟨647844401571436264375861973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 431896267714290842917241315 647844401571436264375861973)
          ·
            refine ⟨15183853161830537446309265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 647844401571436264375861973 15183853161830537446309265)
            ·
              refine ⟨11387889871372903084731949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15183853161830537446309265 11387889871372903084731949)
              ·
                refine ⟨4270458701764838656774481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11387889871372903084731949 4270458701764838656774481)
                ·
                  refine ⟨3202844026323628992580861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4270458701764838656774481 3202844026323628992580861)
                  ·
                    refine ⟨1201066509871360872217823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3202844026323628992580861 1201066509871360872217823)
                    ·
                      rfl

theorem cell22_3508603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 3, 2, 3].length) (baseStart_3508603 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3508603 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3508603 prefixEnd_3508603 := by exact prefixLift 3508603
  have htrace : WordTrace (prefixWord ++ tailWord_3508603) baseStart_3508603 baseEnd_3508603 := by
    simpa [prefixWord, tailWord_3508603, baseEnd_3508603] using wordTrace_append hprefix tailTrace_3508603
  have hstable : (prefixWord ++ tailWord_3508603).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3508603).length < 2 ^ (prefixWord ++ tailWord_3508603).sum := by decide
  have hdescent : baseEnd_3508603 < baseStart_3508603 := by decide
  rcases family_descends (prefixWord ++ tailWord_3508603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3508637 : List Nat := [1, 4, 2, 1, 4, 2, 1, 2, 2, 3]
def baseStart_3508637 : Nat := 118140960795 + 3508637 * 2 ^ 59
def prefixEnd_3508637 : Nat := 4983230072969 + 3 ^ 40 * 3508637 * 2
def baseEnd_3508637 : Nat := 1201078148766196116867719

theorem tailTrace_3508637 : CollatzResearch.WordTrace tailWord_3508637 prefixEnd_3508637 1201078148766196116867719 := by
  unfold tailWord_3508637
  simp only [CollatzResearch.WordTrace]
  refine ⟨127970504589814851337772165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85313669726543234225181443 127970504589814851337772165)
  ·
    refine ⟨23994469610590284625832281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 127970504589814851337772165 23994469610590284625832281)
    ·
      refine ⟨17995852207942713469374211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23994469610590284625832281 17995852207942713469374211)
      ·
        refine ⟨26993778311914070204061317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17995852207942713469374211 26993778311914070204061317)
        ·
          refine ⟨5061333433483888163261497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26993778311914070204061317 5061333433483888163261497)
          ·
            refine ⟨3796000075112916122446123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5061333433483888163261497 3796000075112916122446123)
            ·
              refine ⟨5694000112669374183669185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3796000075112916122446123 5694000112669374183669185)
              ·
                refine ⟨4270500084502030637751889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5694000112669374183669185 4270500084502030637751889)
                ·
                  refine ⟨3202875063376522978313917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4270500084502030637751889 3202875063376522978313917)
                  ·
                    refine ⟨1201078148766196116867719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3202875063376522978313917 1201078148766196116867719)
                    ·
                      rfl

theorem cell22_3508637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 1, 2, 2, 3].length) (baseStart_3508637 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3508637 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3508637 prefixEnd_3508637 := by exact prefixLift 3508637
  have htrace : WordTrace (prefixWord ++ tailWord_3508637) baseStart_3508637 baseEnd_3508637 := by
    simpa [prefixWord, tailWord_3508637, baseEnd_3508637] using wordTrace_append hprefix tailTrace_3508637
  have hstable : (prefixWord ++ tailWord_3508637).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3508637).length < 2 ^ (prefixWord ++ tailWord_3508637).sum := by decide
  have hdescent : baseEnd_3508637 < baseStart_3508637 := by decide
  rcases family_descends (prefixWord ++ tailWord_3508637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3508755 : List Nat := [1, 1, 1, 2, 1, 5, 4, 2, 2, 3]
def baseStart_3508755 : Nat := 118140960795 + 3508755 * 2 ^ 59
def prefixEnd_3508755 : Nat := 4983230072969 + 3 ^ 40 * 3508755 * 2
def baseEnd_3508755 : Nat := 1201118542577683142417357

theorem tailTrace_3508755 : CollatzResearch.WordTrace tailWord_3508755 prefixEnd_3508755 1201118542577683142417357 := by
  unfold tailWord_3508755
  simp only [CollatzResearch.WordTrace]
  refine ⟨127974808403387357490567719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85316538935591571660378479 127974808403387357490567719)
  ·
    refine ⟨191962212605081036235851579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127974808403387357490567719 191962212605081036235851579)
    ·
      refine ⟨287943318907621554353777369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191962212605081036235851579 287943318907621554353777369)
      ·
        refine ⟨215957489180716165765333027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 287943318907621554353777369 215957489180716165765333027)
        ·
          refine ⟨323936233771074248647999541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215957489180716165765333027 323936233771074248647999541)
          ·
            refine ⟨30369021916038210810749957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 323936233771074248647999541 30369021916038210810749957)
            ·
              refine ⟨5694191609257164527015617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30369021916038210810749957 5694191609257164527015617)
              ·
                refine ⟨4270643706942873395261713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5694191609257164527015617 4270643706942873395261713)
                ·
                  refine ⟨3202982780207155046446285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4270643706942873395261713 3202982780207155046446285)
                  ·
                    refine ⟨1201118542577683142417357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3202982780207155046446285 1201118542577683142417357)
                    ·
                      rfl

theorem cell22_3508755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 4, 2, 2, 3].length) (baseStart_3508755 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3508755 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3508755 prefixEnd_3508755 := by exact prefixLift 3508755
  have htrace : WordTrace (prefixWord ++ tailWord_3508755) baseStart_3508755 baseEnd_3508755 := by
    simpa [prefixWord, tailWord_3508755, baseEnd_3508755] using wordTrace_append hprefix tailTrace_3508755
  have hstable : (prefixWord ++ tailWord_3508755).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3508755).length < 2 ^ (prefixWord ++ tailWord_3508755).sum := by decide
  have hdescent : baseEnd_3508755 < baseStart_3508755 := by decide
  rcases family_descends (prefixWord ++ tailWord_3508755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3508772 : List Nat := [2, 3, 1, 5, 1, 1, 2, 1, 1, 5]
def baseStart_3508772 : Nat := 118140960795 + 3508772 * 2 ^ 59
def prefixEnd_3508772 : Nat := 4983230072969 + 3 ^ 40 * 3508772 * 2
def baseEnd_3508772 : Nat := 1201124362025100764742305

theorem tailTrace_3508772 : CollatzResearch.WordTrace tailWord_3508772 prefixEnd_3508772 1201124362025100764742305 := by
  unfold tailWord_3508772
  simp only [CollatzResearch.WordTrace]
  refine ⟨63987714222162884696968285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85316952296217179595957713 63987714222162884696968285)
  ·
    refine ⟨23995392833311081761363107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63987714222162884696968285 23995392833311081761363107)
    ·
      refine ⟨35993089249966622642044661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23995392833311081761363107 35993089249966622642044661)
      ·
        refine ⟨3374352117184370872691687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 35993089249966622642044661 3374352117184370872691687)
        ·
          refine ⟨5061528175776556309037531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3374352117184370872691687 5061528175776556309037531)
          ·
            refine ⟨7592292263664834463556297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5061528175776556309037531 7592292263664834463556297)
            ·
              refine ⟨5694219197748625847667223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7592292263664834463556297 5694219197748625847667223)
              ·
                refine ⟨8541328796622938771500835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5694219197748625847667223 8541328796622938771500835)
                ·
                  refine ⟨12811993194934408157251253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8541328796622938771500835 12811993194934408157251253)
                  ·
                    refine ⟨1201124362025100764742305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12811993194934408157251253 1201124362025100764742305)
                    ·
                      rfl

theorem cell22_3508772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 2, 1, 1, 5].length) (baseStart_3508772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3508772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3508772 prefixEnd_3508772 := by exact prefixLift 3508772
  have htrace : WordTrace (prefixWord ++ tailWord_3508772) baseStart_3508772 baseEnd_3508772 := by
    simpa [prefixWord, tailWord_3508772, baseEnd_3508772] using wordTrace_append hprefix tailTrace_3508772
  have hstable : (prefixWord ++ tailWord_3508772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3508772).length < 2 ^ (prefixWord ++ tailWord_3508772).sum := by decide
  have hdescent : baseEnd_3508772 < baseStart_3508772 := by decide
  rcases family_descends (prefixWord ++ tailWord_3508772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3508806 : List Nat := [6, 1, 1, 1, 2, 3, 1, 2, 2, 3]
def baseStart_3508806 : Nat := 118140960795 + 3508806 * 2 ^ 59
def prefixEnd_3508806 : Nat := 4983230072969 + 3 ^ 40 * 3508806 * 2
def baseEnd_3508806 : Nat := 1201136000919936009392201

theorem tailTrace_3508806 : CollatzResearch.WordTrace tailWord_3508806 prefixEnd_3508806 1201136000919936009392201 := by
  unfold tailWord_3508806
  simp only [CollatzResearch.WordTrace]
  refine ⟨3999270891443831037521071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 85317779017468395467116181 3999270891443831037521071)
  ·
    refine ⟨5998906337165746556281607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3999270891443831037521071 5998906337165746556281607)
    ·
      refine ⟨8998359505748619834422411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5998906337165746556281607 8998359505748619834422411)
      ·
        refine ⟨13497539258622929751633617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8998359505748619834422411 13497539258622929751633617)
        ·
          refine ⟨10123154443967197313725213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13497539258622929751633617 10123154443967197313725213)
          ·
            refine ⟨3796182916487698992646955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10123154443967197313725213 3796182916487698992646955)
            ·
              refine ⟨5694274374731548488970433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3796182916487698992646955 5694274374731548488970433)
              ·
                refine ⟨4270705781048661366727825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5694274374731548488970433 4270705781048661366727825)
                ·
                  refine ⟨3203029335786496025045869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4270705781048661366727825 3203029335786496025045869)
                  ·
                    refine ⟨1201136000919936009392201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3203029335786496025045869 1201136000919936009392201)
                    ·
                      rfl

theorem cell22_3508806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 1, 2, 2, 3].length) (baseStart_3508806 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3508806 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3508806 prefixEnd_3508806 := by exact prefixLift 3508806
  have htrace : WordTrace (prefixWord ++ tailWord_3508806) baseStart_3508806 baseEnd_3508806 := by
    simpa [prefixWord, tailWord_3508806, baseEnd_3508806] using wordTrace_append hprefix tailTrace_3508806
  have hstable : (prefixWord ++ tailWord_3508806).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3508806).length < 2 ^ (prefixWord ++ tailWord_3508806).sum := by decide
  have hdescent : baseEnd_3508806 < baseStart_3508806 := by decide
  rcases family_descends (prefixWord ++ tailWord_3508806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3508817 : List Nat := [1, 2, 2, 1, 3, 3, 2, 4, 1, 3]
def baseStart_3508817 : Nat := 118140960795 + 3508817 * 2 ^ 59
def prefixEnd_3508817 : Nat := 4983230072969 + 3 ^ 40 * 3508817 * 2
def baseEnd_3508817 : Nat := 1201139766444735647367167

theorem tailTrace_3508817 : CollatzResearch.WordTrace tailWord_3508817 prefixEnd_3508817 1201139766444735647367167 := by
  unfold tailWord_3508817
  simp only [CollatzResearch.WordTrace]
  refine ⟨127977069729162742079324705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85318046486108494719549803 127977069729162742079324705)
  ·
    refine ⟨95982802296872056559493529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127977069729162742079324705 95982802296872056559493529)
    ·
      refine ⟨71987101722654042419620147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95982802296872056559493529 71987101722654042419620147)
      ·
        refine ⟨107980652583981063629430221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71987101722654042419620147 107980652583981063629430221)
        ·
          refine ⟨40492744718992898861036333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107980652583981063629430221 40492744718992898861036333)
          ·
            refine ⟨15184779269622337072888625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40492744718992898861036333 15184779269622337072888625)
            ·
              refine ⟨11388584452216752804666469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15184779269622337072888625 11388584452216752804666469)
              ·
                refine ⟨2135359584790641150874963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11388584452216752804666469 2135359584790641150874963)
                ·
                  refine ⟨3203039377185961726312445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2135359584790641150874963 3203039377185961726312445)
                  ·
                    refine ⟨1201139766444735647367167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3203039377185961726312445 1201139766444735647367167)
                    ·
                      rfl

theorem cell22_3508817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 4, 1, 3].length) (baseStart_3508817 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3508817 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3508817 prefixEnd_3508817 := by exact prefixLift 3508817
  have htrace : WordTrace (prefixWord ++ tailWord_3508817) baseStart_3508817 baseEnd_3508817 := by
    simpa [prefixWord, tailWord_3508817, baseEnd_3508817] using wordTrace_append hprefix tailTrace_3508817
  have hstable : (prefixWord ++ tailWord_3508817).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3508817).length < 2 ^ (prefixWord ++ tailWord_3508817).sum := by decide
  have hdescent : baseEnd_3508817 < baseStart_3508817 := by decide
  rcases family_descends (prefixWord ++ tailWord_3508817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3508860 : List Nat := [2, 2, 2, 1, 1, 2, 4, 3, 1, 4]
def baseStart_3508860 : Nat := 118140960795 + 3508860 * 2 ^ 59
def prefixEnd_3508860 : Nat := 4983230072969 + 3 ^ 40 * 3508860 * 2
def baseEnd_3508860 : Nat := 1201154486223497868542035

theorem tailTrace_3508860 : CollatzResearch.WordTrace tailWord_3508860 prefixEnd_3508860 1201154486223497868542035 := by
  unfold tailWord_3508860
  simp only [CollatzResearch.WordTrace]
  refine ⟨63989319034003480211570017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85319092045337973615426689 63989319034003480211570017)
  ·
    refine ⟨47991989275502610158677513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63989319034003480211570017 47991989275502610158677513)
    ·
      refine ⟨35993991956626957619008135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47991989275502610158677513 35993991956626957619008135)
      ·
        refine ⟨53990987934940436428512203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35993991956626957619008135 53990987934940436428512203)
        ·
          refine ⟨80986481902410654642768305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53990987934940436428512203 80986481902410654642768305)
          ·
            refine ⟨60739861426807990982076229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80986481902410654642768305 60739861426807990982076229)
            ·
              refine ⟨11388724017526498309139293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60739861426807990982076229 11388724017526498309139293)
              ·
                refine ⟨4270771506572436865927235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11388724017526498309139293 4270771506572436865927235)
                ·
                  refine ⟨6406157259858655298890853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4270771506572436865927235 6406157259858655298890853)
                  ·
                    refine ⟨1201154486223497868542035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6406157259858655298890853 1201154486223497868542035)
                    ·
                      rfl

theorem cell22_3508860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 3, 1, 4].length) (baseStart_3508860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3508860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3508860 prefixEnd_3508860 := by exact prefixLift 3508860
  have htrace : WordTrace (prefixWord ++ tailWord_3508860) baseStart_3508860 baseEnd_3508860 := by
    simpa [prefixWord, tailWord_3508860, baseEnd_3508860] using wordTrace_append hprefix tailTrace_3508860
  have hstable : (prefixWord ++ tailWord_3508860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3508860).length < 2 ^ (prefixWord ++ tailWord_3508860).sum := by decide
  have hdescent : baseEnd_3508860 < baseStart_3508860 := by decide
  rcases family_descends (prefixWord ++ tailWord_3508860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3508952 : List Nat := [2, 1, 2, 2, 3, 3, 1, 2, 3, 3]
def baseStart_3508952 : Nat := 118140960795 + 3508952 * 2 ^ 59
def prefixEnd_3508952 : Nat := 4983230072969 + 3 ^ 40 * 3508952 * 2
def baseEnd_3508952 : Nat := 1201185979703640295241753

theorem tailTrace_3508952 : CollatzResearch.WordTrace tailWord_3508952 prefixEnd_3508952 1201185979703640295241753 := by
  unfold tailWord_3508952
  simp only [CollatzResearch.WordTrace]
  refine ⟨63990996791836830067744555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85321329055782440090326073 63990996791836830067744555)
  ·
    refine ⟨95986495187755245101616833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63990996791836830067744555 95986495187755245101616833)
    ·
      refine ⟨71989871390816433826212625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95986495187755245101616833 71989871390816433826212625)
      ·
        refine ⟨53992403543112325369659469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71989871390816433826212625 53992403543112325369659469)
        ·
          refine ⟨20247151328667122013622301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53992403543112325369659469 20247151328667122013622301)
          ·
            refine ⟨7592681748250170755108363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20247151328667122013622301 7592681748250170755108363)
            ·
              refine ⟨11389022622375256132662545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7592681748250170755108363 11389022622375256132662545)
              ·
                refine ⟨8541766966781442099496909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11389022622375256132662545 8541766966781442099496909)
                ·
                  refine ⟨3203162612543040787311341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8541766966781442099496909 3203162612543040787311341)
                  ·
                    refine ⟨1201185979703640295241753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3203162612543040787311341 1201185979703640295241753)
                    ·
                      rfl

theorem cell22_3508952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 2, 3, 3].length) (baseStart_3508952 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3508952 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3508952 prefixEnd_3508952 := by exact prefixLift 3508952
  have htrace : WordTrace (prefixWord ++ tailWord_3508952) baseStart_3508952 baseEnd_3508952 := by
    simpa [prefixWord, tailWord_3508952, baseEnd_3508952] using wordTrace_append hprefix tailTrace_3508952
  have hstable : (prefixWord ++ tailWord_3508952).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3508952).length < 2 ^ (prefixWord ++ tailWord_3508952).sum := by decide
  have hdescent : baseEnd_3508952 < baseStart_3508952 := by decide
  rcases family_descends (prefixWord ++ tailWord_3508952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3508999 : List Nat := [1, 1, 4, 4, 1, 2, 3, 1, 5]
def baseStart_3508999 : Nat := 118140960795 + 3508999 * 2 ^ 59
def prefixEnd_3508999 : Nat := 4983230072969 + 3 ^ 40 * 3508999 * 2
def baseEnd_3508999 : Nat := 400400689588049279772203

theorem tailTrace_3508999 : CollatzResearch.WordTrace tailWord_3508999 prefixEnd_3508999 400400689588049279772203 := by
  unfold tailWord_3508999
  simp only [CollatzResearch.WordTrace]
  refine ⟨127983707814503387162450051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85322471876335591441633367 127983707814503387162450051)
  ·
    refine ⟨191975561721755080743675077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127983707814503387162450051 191975561721755080743675077)
    ·
      refine ⟨35995417822829077639439077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 191975561721755080743675077 35995417822829077639439077)
      ·
        refine ⟨6749140841780452057394827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35995417822829077639439077 6749140841780452057394827)
        ·
          refine ⟨10123711262670678086092241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6749140841780452057394827 10123711262670678086092241)
          ·
            refine ⟨7592783447003008564569181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10123711262670678086092241 7592783447003008564569181)
            ·
              refine ⟨2847293792626128211713443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7592783447003008564569181 2847293792626128211713443)
              ·
                refine ⟨4270940688939192317570165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2847293792626128211713443 4270940688939192317570165)
                ·
                  refine ⟨400400689588049279772203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4270940688939192317570165 400400689588049279772203)
                  ·
                    rfl

theorem cell22_3508999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 3, 1, 5].length) (baseStart_3508999 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3508999 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3508999 prefixEnd_3508999 := by exact prefixLift 3508999
  have htrace : WordTrace (prefixWord ++ tailWord_3508999) baseStart_3508999 baseEnd_3508999 := by
    simpa [prefixWord, tailWord_3508999, baseEnd_3508999] using wordTrace_append hprefix tailTrace_3508999
  have hstable : (prefixWord ++ tailWord_3508999).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3508999).length < 2 ^ (prefixWord ++ tailWord_3508999).sum := by decide
  have hdescent : baseEnd_3508999 < baseStart_3508999 := by decide
  rcases family_descends (prefixWord ++ tailWord_3508999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3509025 : List Nat := [1, 2, 3, 2, 1, 2, 2, 1, 3, 5]
def baseStart_3509025 : Nat := 118140960795 + 3509025 * 2 ^ 59
def prefixEnd_3509025 : Nat := 4983230072969 + 3 ^ 40 * 3509025 * 2
def baseEnd_3509025 : Nat := 1201210969095492438166529

theorem tailTrace_3509025 : CollatzResearch.WordTrace tailWord_3509025 prefixEnd_3509025 1201210969095492438166529 := by
  unfold tailWord_3509025
  simp only [CollatzResearch.WordTrace]
  refine ⟨127984656112409193602896529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85323104074939462401931019 127984656112409193602896529)
  ·
    refine ⟨95988492084306895202172397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127984656112409193602896529 95988492084306895202172397)
    ·
      refine ⟨35995684531615085700814649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95988492084306895202172397 35995684531615085700814649)
      ·
        refine ⟨26996763398711314275610987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35995684531615085700814649 26996763398711314275610987)
        ·
          refine ⟨40495145098066971413416481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26996763398711314275610987 40495145098066971413416481)
          ·
            refine ⟨30371358823550228560062361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40495145098066971413416481 30371358823550228560062361)
            ·
              refine ⟨22778519117662671420046771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30371358823550228560062361 22778519117662671420046771)
              ·
                refine ⟨34167778676494007130070157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22778519117662671420046771 34167778676494007130070157)
                ·
                  refine ⟨12812917003685252673776309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34167778676494007130070157 12812917003685252673776309)
                  ·
                    refine ⟨1201210969095492438166529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12812917003685252673776309 1201210969095492438166529)
                    ·
                      rfl

theorem cell22_3509025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 1, 3, 5].length) (baseStart_3509025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3509025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3509025 prefixEnd_3509025 := by exact prefixLift 3509025
  have htrace : WordTrace (prefixWord ++ tailWord_3509025) baseStart_3509025 baseEnd_3509025 := by
    simpa [prefixWord, tailWord_3509025, baseEnd_3509025] using wordTrace_append hprefix tailTrace_3509025
  have hstable : (prefixWord ++ tailWord_3509025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3509025).length < 2 ^ (prefixWord ++ tailWord_3509025).sum := by decide
  have hdescent : baseEnd_3509025 < baseStart_3509025 := by decide
  rcases family_descends (prefixWord ++ tailWord_3509025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3509042 : List Nat := [3, 2, 1, 1, 3, 1, 1, 3, 4, 3]
def baseStart_3509042 : Nat := 118140960795 + 3509042 * 2 ^ 59
def prefixEnd_3509042 : Nat := 4983230072969 + 3 ^ 40 * 3509042 * 2
def baseEnd_3509042 : Nat := 1201216788542910060491477

theorem tailTrace_3509042 : CollatzResearch.WordTrace tailWord_3509042 prefixEnd_3509042 1201216788542910060491477 := by
  unfold tailWord_3509042
  simp only [CollatzResearch.WordTrace]
  refine ⟨31996319038336901376566345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85323517435565070337510253 31996319038336901376566345)
  ·
    refine ⟨23997239278752676032424759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31996319038336901376566345 23997239278752676032424759)
    ·
      refine ⟨35995858918129014048637139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23997239278752676032424759 35995858918129014048637139)
      ·
        refine ⟨53993788377193521072955709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35995858918129014048637139 53993788377193521072955709)
        ·
          refine ⟨20247670641447570402358391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53993788377193521072955709 20247670641447570402358391)
          ·
            refine ⟨30371505962171355603537587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20247670641447570402358391 30371505962171355603537587)
            ·
              refine ⟨45557258943257033405306381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30371505962171355603537587 45557258943257033405306381)
              ·
                refine ⟨17083972103721387526989893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45557258943257033405306381 17083972103721387526989893)
                ·
                  refine ⟨3203244769447760161310605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17083972103721387526989893 3203244769447760161310605)
                  ·
                    refine ⟨1201216788542910060491477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3203244769447760161310605 1201216788542910060491477)
                    ·
                      rfl

theorem cell22_3509042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 3, 4, 3].length) (baseStart_3509042 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3509042 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3509042 prefixEnd_3509042 := by exact prefixLift 3509042
  have htrace : WordTrace (prefixWord ++ tailWord_3509042) baseStart_3509042 baseEnd_3509042 := by
    simpa [prefixWord, tailWord_3509042, baseEnd_3509042] using wordTrace_append hprefix tailTrace_3509042
  have hstable : (prefixWord ++ tailWord_3509042).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3509042).length < 2 ^ (prefixWord ++ tailWord_3509042).sum := by decide
  have hdescent : baseEnd_3509042 < baseStart_3509042 := by decide
  rcases family_descends (prefixWord ++ tailWord_3509042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3509055 : List Nat := [1, 1, 2, 2, 5, 1, 1, 9]
def baseStart_3509055 : Nat := 118140960795 + 3509055 * 2 ^ 59
def prefixEnd_3509055 : Nat := 4983230072969 + 3 ^ 40 * 3509055 * 2
def baseEnd_3509055 : Nat := 133469026523175817768493

theorem tailTrace_3509055 : CollatzResearch.WordTrace tailWord_3509055 prefixEnd_3509055 133469026523175817768493 := by
  unfold tailWord_3509055
  simp only [CollatzResearch.WordTrace]
  refine ⟨127985750302300508726488619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85323833534867005817659079 127985750302300508726488619)
  ·
    refine ⟨191978625453450763089732929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127985750302300508726488619 191978625453450763089732929)
    ·
      refine ⟨143983969090088072317299697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191978625453450763089732929 143983969090088072317299697)
      ·
        refine ⟨107987976817566054237974773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143983969090088072317299697 107987976817566054237974773)
        ·
          refine ⟨10123872826646817584810135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 107987976817566054237974773 10123872826646817584810135)
          ·
            refine ⟨15185809239970226377215203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10123872826646817584810135 15185809239970226377215203)
            ·
              refine ⟨22778713859955339565822805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15185809239970226377215203 22778713859955339565822805)
              ·
                refine ⟨133469026523175817768493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 22778713859955339565822805 133469026523175817768493)
                ·
                  rfl

theorem cell22_3509055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 9].length) (baseStart_3509055 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3509055 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3509055 prefixEnd_3509055 := by exact prefixLift 3509055
  have htrace : WordTrace (prefixWord ++ tailWord_3509055) baseStart_3509055 baseEnd_3509055 := by
    simpa [prefixWord, tailWord_3509055, baseEnd_3509055] using wordTrace_append hprefix tailTrace_3509055
  have hstable : (prefixWord ++ tailWord_3509055).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3509055).length < 2 ^ (prefixWord ++ tailWord_3509055).sum := by decide
  have hdescent : baseEnd_3509055 < baseStart_3509055 := by decide
  rcases family_descends (prefixWord ++ tailWord_3509055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3509070 : List Nat := [4, 1, 1, 1, 1, 1, 1, 3, 2, 7]
def baseStart_3509070 : Nat := 118140960795 + 3509070 * 2 ^ 59
def prefixEnd_3509070 : Nat := 4983230072969 + 3 ^ 40 * 3509070 * 2
def baseEnd_3509070 : Nat := 1201226373515127320791391

theorem tailTrace_3509070 : CollatzResearch.WordTrace tailWord_3509070 prefixEnd_3509070 1201226373515127320791391 := by
  unfold tailWord_3509070
  simp only [CollatzResearch.WordTrace]
  refine ⟨15998287174655770786035583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85324198264830777525523109 15998287174655770786035583)
  ·
    refine ⟨23997430761983656179053375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15998287174655770786035583 23997430761983656179053375)
    ·
      refine ⟨35996146142975484268580063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23997430761983656179053375 35996146142975484268580063)
      ·
        refine ⟨53994219214463226402870095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35996146142975484268580063 53994219214463226402870095)
        ·
          refine ⟨80991328821694839604305143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53994219214463226402870095 80991328821694839604305143)
          ·
            refine ⟨121486993232542259406457715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80991328821694839604305143 121486993232542259406457715)
            ·
              refine ⟨182230489848813389109686573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121486993232542259406457715 182230489848813389109686573)
              ·
                refine ⟨68336433693305020916132465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 182230489848813389109686573 68336433693305020916132465)
                ·
                  refine ⟨51252325269978765687099349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68336433693305020916132465 51252325269978765687099349)
                  ·
                    refine ⟨1201226373515127320791391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51252325269978765687099349 1201226373515127320791391)
                    ·
                      rfl

theorem cell22_3509070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 3, 2, 7].length) (baseStart_3509070 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3509070 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3509070 prefixEnd_3509070 := by exact prefixLift 3509070
  have htrace : WordTrace (prefixWord ++ tailWord_3509070) baseStart_3509070 baseEnd_3509070 := by
    simpa [prefixWord, tailWord_3509070, baseEnd_3509070] using wordTrace_append hprefix tailTrace_3509070
  have hstable : (prefixWord ++ tailWord_3509070).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3509070).length < 2 ^ (prefixWord ++ tailWord_3509070).sum := by decide
  have hdescent : baseEnd_3509070 < baseStart_3509070 := by decide
  rcases family_descends (prefixWord ++ tailWord_3509070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3509115 : List Nat := [1, 1, 1, 1, 1, 5, 3, 1, 1, 7]
def baseStart_3509115 : Nat := 118140960795 + 3509115 * 2 ^ 59
def prefixEnd_3509115 : Nat := 4983230072969 + 3 ^ 40 * 3509115 * 2
def baseEnd_3509115 : Nat := 1201241777934762203416253

theorem tailTrace_3509115 : CollatzResearch.WordTrace tailWord_3509115 prefixEnd_3509115 1201241777934762203416253 := by
  unfold tailWord_3509115
  simp only [CollatzResearch.WordTrace]
  refine ⟨127987938682083138973672799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85325292454722092649115199 127987938682083138973672799)
  ·
    refine ⟨191981908023124708460509199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127987938682083138973672799 191981908023124708460509199)
    ·
      refine ⟨287972862034687062690763799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191981908023124708460509199 287972862034687062690763799)
      ·
        refine ⟨431959293052030594036145699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287972862034687062690763799 431959293052030594036145699)
        ·
          refine ⟨647938939578045891054218549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 431959293052030594036145699 647938939578045891054218549)
          ·
            refine ⟨60744275585441802286332989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 647938939578045891054218549 60744275585441802286332989)
            ·
              refine ⟨22779103344540675857374871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60744275585441802286332989 22779103344540675857374871)
              ·
                refine ⟨34168655016811013786062307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22779103344540675857374871 34168655016811013786062307)
                ·
                  refine ⟨51252982525216520679093461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34168655016811013786062307 51252982525216520679093461)
                  ·
                    refine ⟨1201241777934762203416253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51252982525216520679093461 1201241777934762203416253)
                    ·
                      rfl

theorem cell22_3509115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 1, 1, 7].length) (baseStart_3509115 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3509115 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3509115 prefixEnd_3509115 := by exact prefixLift 3509115
  have htrace : WordTrace (prefixWord ++ tailWord_3509115) baseStart_3509115 baseEnd_3509115 := by
    simpa [prefixWord, tailWord_3509115, baseEnd_3509115] using wordTrace_append hprefix tailTrace_3509115
  have hstable : (prefixWord ++ tailWord_3509115).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3509115).length < 2 ^ (prefixWord ++ tailWord_3509115).sum := by decide
  have hdescent : baseEnd_3509115 < baseStart_3509115 := by decide
  rcases family_descends (prefixWord ++ tailWord_3509115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3509117 : List Nat := [1, 4, 1, 1, 2, 1, 4, 3, 5]
def baseStart_3509117 : Nat := 118140960795 + 3509117 * 2 ^ 59
def prefixEnd_3509117 : Nat := 4983230072969 + 3 ^ 40 * 3509117 * 2
def baseEnd_3509117 : Nat := 400414154191878288288749

theorem tailTrace_3509117 : CollatzResearch.WordTrace tailWord_3509117 prefixEnd_3509117 400414154191878288288749 := by
  unfold tailWord_3509117
  simp only [CollatzResearch.WordTrace]
  refine ⟨127988011628075893315245605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85325341085383928876830403 127988011628075893315245605)
  ·
    refine ⟨23997752180264229996608551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 127988011628075893315245605 23997752180264229996608551)
    ·
      refine ⟨35996628270396344994912827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23997752180264229996608551 35996628270396344994912827)
      ·
        refine ⟨53994942405594517492369241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35996628270396344994912827 53994942405594517492369241)
        ·
          refine ⟨40496206804195888119276931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53994942405594517492369241 40496206804195888119276931)
          ·
            refine ⟨60744310206293832178915397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40496206804195888119276931 60744310206293832178915397)
            ·
              refine ⟨11389558163680093533546637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60744310206293832178915397 11389558163680093533546637)
              ·
                refine ⟨4271084311380035075079989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11389558163680093533546637 4271084311380035075079989)
                ·
                  refine ⟨400414154191878288288749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4271084311380035075079989 400414154191878288288749)
                  ·
                    rfl

theorem cell22_3509117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 3, 5].length) (baseStart_3509117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3509117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3509117 prefixEnd_3509117 := by exact prefixLift 3509117
  have htrace : WordTrace (prefixWord ++ tailWord_3509117) baseStart_3509117 baseEnd_3509117 := by
    simpa [prefixWord, tailWord_3509117, baseEnd_3509117] using wordTrace_append hprefix tailTrace_3509117
  have hstable : (prefixWord ++ tailWord_3509117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3509117).length < 2 ^ (prefixWord ++ tailWord_3509117).sum := by decide
  have hdescent : baseEnd_3509117 < baseStart_3509117 := by decide
  rcases family_descends (prefixWord ++ tailWord_3509117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3509145 : List Nat := [1, 2, 1, 2, 1, 3, 1, 1, 10]
def baseStart_3509145 : Nat := 118140960795 + 3509145 * 2 ^ 59
def prefixEnd_3509145 : Nat := 4983230072969 + 3 ^ 40 * 3509145 * 2
def baseEnd_3509145 : Nat := 400417349182617375055387

theorem tailTrace_3509145 : CollatzResearch.WordTrace tailWord_3509145 prefixEnd_3509145 400417349182617375055387 := by
  unfold tailWord_3509145
  simp only [CollatzResearch.WordTrace]
  refine ⟨127989032871974454097264889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85326021914649636064843259 127989032871974454097264889)
  ·
    refine ⟨95991774653980840572948667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127989032871974454097264889 95991774653980840572948667)
    ·
      refine ⟨143987661980971260859423001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95991774653980840572948667 143987661980971260859423001)
      ·
        refine ⟨107990746485728445644567251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143987661980971260859423001 107990746485728445644567251)
        ·
          refine ⟨161986119728592668466850877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107990746485728445644567251 161986119728592668466850877)
          ·
            refine ⟨60744794898222250675069079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 161986119728592668466850877 60744794898222250675069079)
            ·
              refine ⟨91117192347333376012603619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60744794898222250675069079 91117192347333376012603619)
              ·
                refine ⟨136675788521000064018905429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91117192347333376012603619 136675788521000064018905429)
                ·
                  refine ⟨400417349182617375055387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 136675788521000064018905429 400417349182617375055387)
                  ·
                    rfl

theorem cell22_3509145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 1, 10].length) (baseStart_3509145 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3509145 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3509145 prefixEnd_3509145 := by exact prefixLift 3509145
  have htrace : WordTrace (prefixWord ++ tailWord_3509145) baseStart_3509145 baseEnd_3509145 := by
    simpa [prefixWord, tailWord_3509145, baseEnd_3509145] using wordTrace_append hprefix tailTrace_3509145
  have hstable : (prefixWord ++ tailWord_3509145).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3509145).length < 2 ^ (prefixWord ++ tailWord_3509145).sum := by decide
  have hdescent : baseEnd_3509145 < baseStart_3509145 := by decide
  rcases family_descends (prefixWord ++ tailWord_3509145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3509181 : List Nat := [1, 4, 1, 2, 4, 1, 2, 2, 1, 4]
def baseStart_3509181 : Nat := 118140960795 + 3509181 * 2 ^ 59
def prefixEnd_3509181 : Nat := 4983230072969 + 3 ^ 40 * 3509181 * 2
def baseEnd_3509181 : Nat := 1201264371083560031266051

theorem tailTrace_3509181 : CollatzResearch.WordTrace tailWord_3509181 prefixEnd_3509181 1201264371083560031266051 := by
  unfold tailWord_3509181
  simp only [CollatzResearch.WordTrace]
  refine ⟨127990345899844032245575397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85326897266562688163716931 127990345899844032245575397)
  ·
    refine ⟨23998189856220756046045387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 127990345899844032245575397 23998189856220756046045387)
    ·
      refine ⟨35997284784331134069068081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23998189856220756046045387 35997284784331134069068081)
      ·
        refine ⟨26997963588248350551801061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35997284784331134069068081 26997963588248350551801061)
        ·
          refine ⟨5062118172796565728462699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26997963588248350551801061 5062118172796565728462699)
          ·
            refine ⟨7593177259194848592694049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5062118172796565728462699 7593177259194848592694049)
            ·
              refine ⟨5694882944396136444520537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7593177259194848592694049 5694882944396136444520537)
              ·
                refine ⟨4271162208297102333390403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5694882944396136444520537 4271162208297102333390403)
                ·
                  refine ⟨6406743312445653500085605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4271162208297102333390403 6406743312445653500085605)
                  ·
                    refine ⟨1201264371083560031266051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6406743312445653500085605 1201264371083560031266051)
                    ·
                      rfl

theorem cell22_3509181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 2, 2, 1, 4].length) (baseStart_3509181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3509181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3509181 prefixEnd_3509181 := by exact prefixLift 3509181
  have htrace : WordTrace (prefixWord ++ tailWord_3509181) baseStart_3509181 baseEnd_3509181 := by
    simpa [prefixWord, tailWord_3509181, baseEnd_3509181] using wordTrace_append hprefix tailTrace_3509181
  have hstable : (prefixWord ++ tailWord_3509181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3509181).length < 2 ^ (prefixWord ++ tailWord_3509181).sum := by decide
  have hdescent : baseEnd_3509181 < baseStart_3509181 := by decide
  rcases family_descends (prefixWord ++ tailWord_3509181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3509209 : List Nat := [1, 2, 1, 2, 5, 2, 1, 2, 2, 4]
def baseStart_3509209 : Nat := 118140960795 + 3509209 * 2 ^ 59
def prefixEnd_3509209 : Nat := 4983230072969 + 3 ^ 40 * 3509209 * 2
def baseEnd_3509209 : Nat := 1201273956055777291565965

theorem tailTrace_3509209 : CollatzResearch.WordTrace tailWord_3509209 prefixEnd_3509209 1201273956055777291565965 := by
  unfold tailWord_3509209
  simp only [CollatzResearch.WordTrace]
  refine ⟨127991367143742593027594681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85327578095828395351729787 127991367143742593027594681)
  ·
    refine ⟨95993525357806944770696011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127991367143742593027594681 95993525357806944770696011)
    ·
      refine ⟨143990288036710417156044017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95993525357806944770696011 143990288036710417156044017)
      ·
        refine ⟨107992716027532812867033013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143990288036710417156044017 107992716027532812867033013)
        ·
          refine ⟨10124317127581201206284345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 107992716027532812867033013 10124317127581201206284345)
          ·
            refine ⟨7593237845685900904713259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10124317127581201206284345 7593237845685900904713259)
            ·
              refine ⟨11389856768528851357069889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7593237845685900904713259 11389856768528851357069889)
              ·
                refine ⟨8542392576396638517802417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11389856768528851357069889 8542392576396638517802417)
                ·
                  refine ⟨6406794432297478888351813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8542392576396638517802417 6406794432297478888351813)
                  ·
                    refine ⟨1201273956055777291565965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6406794432297478888351813 1201273956055777291565965)
                    ·
                      rfl

theorem cell22_3509209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 2, 2, 4].length) (baseStart_3509209 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3509209 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3509209 prefixEnd_3509209 := by exact prefixLift 3509209
  have htrace : WordTrace (prefixWord ++ tailWord_3509209) baseStart_3509209 baseEnd_3509209 := by
    simpa [prefixWord, tailWord_3509209, baseEnd_3509209] using wordTrace_append hprefix tailTrace_3509209
  have hstable : (prefixWord ++ tailWord_3509209).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3509209).length < 2 ^ (prefixWord ++ tailWord_3509209).sum := by decide
  have hdescent : baseEnd_3509209 < baseStart_3509209 := by decide
  rcases family_descends (prefixWord ++ tailWord_3509209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3509213 : List Nat := [1, 4, 3, 1, 2, 2, 3, 2, 4]
def baseStart_3509213 : Nat := 118140960795 + 3509213 * 2 ^ 59
def prefixEnd_3509213 : Nat := 4983230072969 + 3 ^ 40 * 3509213 * 2
def baseEnd_3509213 : Nat := 400425108445840871488651

theorem tailTrace_3509213 : CollatzResearch.WordTrace tailWord_3509213 prefixEnd_3509213 400425108445840871488651 := by
  unfold tailWord_3509213
  simp only [CollatzResearch.WordTrace]
  refine ⟨127991513035728101710740293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85327675357152067807160195 127991513035728101710740293)
  ·
    refine ⟨23998408694199019070763805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 127991513035728101710740293 23998408694199019070763805)
    ·
      refine ⟨8999403260324632151536427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23998408694199019070763805 8999403260324632151536427)
      ·
        refine ⟨13499104890486948227304641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8999403260324632151536427 13499104890486948227304641)
        ·
          refine ⟨10124328667865211170478481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13499104890486948227304641 10124328667865211170478481)
          ·
            refine ⟨7593246500898908377858861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10124328667865211170478481 7593246500898908377858861)
            ·
              refine ⟨2847467437837090641697073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7593246500898908377858861 2847467437837090641697073)
              ·
                refine ⟨2135600578377817981272805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2847467437837090641697073 2135600578377817981272805)
                ·
                  refine ⟨400425108445840871488651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2135600578377817981272805 400425108445840871488651)
                  ·
                    rfl

theorem cell22_3509213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 3, 2, 4].length) (baseStart_3509213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3509213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3509213 prefixEnd_3509213 := by exact prefixLift 3509213
  have htrace : WordTrace (prefixWord ++ tailWord_3509213) baseStart_3509213 baseEnd_3509213 := by
    simpa [prefixWord, tailWord_3509213, baseEnd_3509213] using wordTrace_append hprefix tailTrace_3509213
  have hstable : (prefixWord ++ tailWord_3509213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3509213).length < 2 ^ (prefixWord ++ tailWord_3509213).sum := by decide
  have hdescent : baseEnd_3509213 < baseStart_3509213 := by decide
  rcases family_descends (prefixWord ++ tailWord_3509213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3509267 : List Nat := [1, 1, 1, 2, 1, 4, 1, 4, 2, 5]
def baseStart_3509267 : Nat := 118140960795 + 3509267 * 2 ^ 59
def prefixEnd_3509267 : Nat := 4983230072969 + 3 ^ 40 * 3509267 * 2
def baseEnd_3509267 : Nat := 1201293810641084473615787

theorem tailTrace_3509267 : CollatzResearch.WordTrace tailWord_3509267 prefixEnd_3509267 1201293810641084473615787 := by
  unfold tailWord_3509267
  simp only [CollatzResearch.WordTrace]
  refine ⟨127993482577532468933206055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85328988385021645955470703 127993482577532468933206055)
  ·
    refine ⟨191990223866298703399809083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127993482577532468933206055 191990223866298703399809083)
    ·
      refine ⟨287985335799448055099713625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191990223866298703399809083 287985335799448055099713625)
      ·
        refine ⟨215989001849586041324785219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 287985335799448055099713625 215989001849586041324785219)
        ·
          refine ⟨323983502774379061987177829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215989001849586041324785219 323983502774379061987177829)
          ·
            refine ⟨60746906770196074122595843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 323983502774379061987177829 60746906770196074122595843)
            ·
              refine ⟨91120360155294111183893765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60746906770196074122595843 91120360155294111183893765)
              ·
                refine ⟨17085067529117645846980081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 91120360155294111183893765 17085067529117645846980081)
                ·
                  refine ⟨12813800646838234385235061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17085067529117645846980081 12813800646838234385235061)
                  ·
                    refine ⟨1201293810641084473615787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12813800646838234385235061 1201293810641084473615787)
                    ·
                      rfl

theorem cell22_3509267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 4, 2, 5].length) (baseStart_3509267 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3509267 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3509267 prefixEnd_3509267 := by exact prefixLift 3509267
  have htrace : WordTrace (prefixWord ++ tailWord_3509267) baseStart_3509267 baseEnd_3509267 := by
    simpa [prefixWord, tailWord_3509267, baseEnd_3509267] using wordTrace_append hprefix tailTrace_3509267
  have hstable : (prefixWord ++ tailWord_3509267).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3509267).length < 2 ^ (prefixWord ++ tailWord_3509267).sum := by decide
  have hdescent : baseEnd_3509267 < baseStart_3509267 := by decide
  rcases family_descends (prefixWord ++ tailWord_3509267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3509269 : List Nat := [1, 3, 2, 1, 4, 1, 1, 4, 5]
def baseStart_3509269 : Nat := 118140960795 + 3509269 * 2 ^ 59
def prefixEnd_3509269 : Nat := 4983230072969 + 3 ^ 40 * 3509269 * 2
def baseEnd_3509269 : Nat := 400431498427319045021927

theorem tailTrace_3509269 : CollatzResearch.WordTrace tailWord_3509269 prefixEnd_3509269 400431498427319045021927 := by
  unfold tailWord_3509269
  simp only [CollatzResearch.WordTrace]
  refine ⟨127993555523525223274778861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85329037015683482183185907 127993555523525223274778861)
  ·
    refine ⟨47997583321321958728042073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127993555523525223274778861 47997583321321958728042073)
    ·
      refine ⟨35998187490991469046031555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47997583321321958728042073 35998187490991469046031555)
      ·
        refine ⟨53997281236487203569047333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35998187490991469046031555 53997281236487203569047333)
        ·
          refine ⟨10124490231841350669196375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53997281236487203569047333 10124490231841350669196375)
          ·
            refine ⟨15186735347762026003794563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10124490231841350669196375 15186735347762026003794563)
            ·
              refine ⟨22780103021643039005691845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15186735347762026003794563 22780103021643039005691845)
              ·
                refine ⟨4271269316558069813567221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22780103021643039005691845 4271269316558069813567221)
                ·
                  refine ⟨400431498427319045021927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4271269316558069813567221 400431498427319045021927)
                  ·
                    rfl

theorem cell22_3509269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 4, 5].length) (baseStart_3509269 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3509269 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3509269 prefixEnd_3509269 := by exact prefixLift 3509269
  have htrace : WordTrace (prefixWord ++ tailWord_3509269) baseStart_3509269 baseEnd_3509269 := by
    simpa [prefixWord, tailWord_3509269, baseEnd_3509269] using wordTrace_append hprefix tailTrace_3509269
  have hstable : (prefixWord ++ tailWord_3509269).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3509269).length < 2 ^ (prefixWord ++ tailWord_3509269).sum := by decide
  have hdescent : baseEnd_3509269 < baseStart_3509269 := by decide
  rcases family_descends (prefixWord ++ tailWord_3509269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3509273 : List Nat := [1, 2, 1, 2, 1, 1, 8, 2, 1, 3]
def baseStart_3509273 : Nat := 118140960795 + 3509273 * 2 ^ 59
def prefixEnd_3509273 : Nat := 4983230072969 + 3 ^ 40 * 3509273 * 2
def baseEnd_3509273 : Nat := 1201295864563702457965769

theorem tailTrace_3509273 : CollatzResearch.WordTrace tailWord_3509273 prefixEnd_3509273 1201295864563702457965769 := by
  unfold tailWord_3509273
  simp only [CollatzResearch.WordTrace]
  refine ⟨127993701415510731957924473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85329134277007154638616315 127993701415510731957924473)
  ·
    refine ⟨95995276061633048968443355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127993701415510731957924473 95995276061633048968443355)
    ·
      refine ⟨143992914092449573452665033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95995276061633048968443355 143992914092449573452665033)
      ·
        refine ⟨107994685569337180089498775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143992914092449573452665033 107994685569337180089498775)
        ·
          refine ⟨161992028354005770134248163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107994685569337180089498775 161992028354005770134248163)
          ·
            refine ⟨242988042531008655201372245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161992028354005770134248163 242988042531008655201372245)
            ·
              refine ⟨2847516123410257678141081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 242988042531008655201372245 2847516123410257678141081)
              ·
                refine ⟨2135637092557693258605811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2847516123410257678141081 2135637092557693258605811)
                ·
                  refine ⟨3203455638836539887908717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2135637092557693258605811 3203455638836539887908717)
                  ·
                    refine ⟨1201295864563702457965769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3203455638836539887908717 1201295864563702457965769)
                    ·
                      rfl

theorem cell22_3509273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 8, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 8, 2, 1, 3].length) (baseStart_3509273 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3509273 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3509273 prefixEnd_3509273 := by exact prefixLift 3509273
  have htrace : WordTrace (prefixWord ++ tailWord_3509273) baseStart_3509273 baseEnd_3509273 := by
    simpa [prefixWord, tailWord_3509273, baseEnd_3509273] using wordTrace_append hprefix tailTrace_3509273
  have hstable : (prefixWord ++ tailWord_3509273).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3509273).length < 2 ^ (prefixWord ++ tailWord_3509273).sum := by decide
  have hdescent : baseEnd_3509273 < baseStart_3509273 := by decide
  rcases family_descends (prefixWord ++ tailWord_3509273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3509284 : List Nat := [2, 3, 1, 4, 1, 1, 1, 1, 1, 7]
def baseStart_3509284 : Nat := 118140960795 + 3509284 * 2 ^ 59
def prefixEnd_3509284 : Nat := 4983230072969 + 3 ^ 40 * 3509284 * 2
def baseEnd_3509284 : Nat := 1201299630088502095940735

theorem tailTrace_3509284 : CollatzResearch.WordTrace tailWord_3509284 prefixEnd_3509284 1201299630088502095940735 := by
  unfold tailWord_3509284
  simp only [CollatzResearch.WordTrace]
  refine ⟨63997051309235440418287453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85329401745647253891049937 63997051309235440418287453)
  ·
    refine ⟨23998894240963290156857795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63997051309235440418287453 23998894240963290156857795)
    ·
      refine ⟨35998341361444935235286693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23998894240963290156857795 35998341361444935235286693)
      ·
        refine ⟨6749689005270925356616255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35998341361444935235286693 6749689005270925356616255)
        ·
          refine ⟨10124533507906388034924383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6749689005270925356616255 10124533507906388034924383)
          ·
            refine ⟨15186800261859582052386575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10124533507906388034924383 15186800261859582052386575)
            ·
              refine ⟨22780200392789373078579863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15186800261859582052386575 22780200392789373078579863)
              ·
                refine ⟨34170300589184059617869795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22780200392789373078579863 34170300589184059617869795)
                ·
                  refine ⟨51255450883776089426804693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34170300589184059617869795 51255450883776089426804693)
                  ·
                    refine ⟨1201299630088502095940735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51255450883776089426804693 1201299630088502095940735)
                    ·
                      rfl

theorem cell22_3509284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 1, 1, 7].length) (baseStart_3509284 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3509284 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3509284 prefixEnd_3509284 := by exact prefixLift 3509284
  have htrace : WordTrace (prefixWord ++ tailWord_3509284) baseStart_3509284 baseEnd_3509284 := by
    simpa [prefixWord, tailWord_3509284, baseEnd_3509284] using wordTrace_append hprefix tailTrace_3509284
  have hstable : (prefixWord ++ tailWord_3509284).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3509284).length < 2 ^ (prefixWord ++ tailWord_3509284).sum := by decide
  have hdescent : baseEnd_3509284 < baseStart_3509284 := by decide
  rcases family_descends (prefixWord ++ tailWord_3509284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3509299 : List Nat := [1, 1, 1, 2, 4, 1, 1, 6, 1, 4]
def baseStart_3509299 : Nat := 118140960795 + 3509299 * 2 ^ 59
def prefixEnd_3509299 : Nat := 4983230072969 + 3 ^ 40 * 3509299 * 2
def baseEnd_3509299 : Nat := 1201304764895047056815689

theorem tailTrace_3509299 : CollatzResearch.WordTrace tailWord_3509299 prefixEnd_3509299 1201304764895047056815689 := by
  unfold tailWord_3509299
  simp only [CollatzResearch.WordTrace]
  refine ⟨127994649713416538398370951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85329766475611025598913967 127994649713416538398370951)
  ·
    refine ⟨191991974570124807597556427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127994649713416538398370951 191991974570124807597556427)
    ·
      refine ⟨287987961855187211396334641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191991974570124807597556427 287987961855187211396334641)
      ·
        refine ⟨215990971391390408547250981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 287987961855187211396334641 215990971391390408547250981)
        ·
          refine ⟨40498307135885701602609559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 215990971391390408547250981 40498307135885701602609559)
          ·
            refine ⟨60747460703828552403914339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40498307135885701602609559 60747460703828552403914339)
            ·
              refine ⟨91121191055742828605871509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60747460703828552403914339 91121191055742828605871509)
              ·
                refine ⟨4271305830737945090900227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 91121191055742828605871509 4271305830737945090900227)
                ·
                  refine ⟨6406958746106917636350341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4271305830737945090900227 6406958746106917636350341)
                  ·
                    refine ⟨1201304764895047056815689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6406958746106917636350341 1201304764895047056815689)
                    ·
                      rfl

theorem cell22_3509299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 6, 1, 4].length) (baseStart_3509299 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3509299 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3509299 prefixEnd_3509299 := by exact prefixLift 3509299
  have htrace : WordTrace (prefixWord ++ tailWord_3509299) baseStart_3509299 baseEnd_3509299 := by
    simpa [prefixWord, tailWord_3509299, baseEnd_3509299] using wordTrace_append hprefix tailTrace_3509299
  have hstable : (prefixWord ++ tailWord_3509299).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3509299).length < 2 ^ (prefixWord ++ tailWord_3509299).sum := by decide
  have hdescent : baseEnd_3509299 < baseStart_3509299 := by decide
  rcases family_descends (prefixWord ++ tailWord_3509299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3509327 : List Nat := [1, 1, 2, 1, 1, 2, 2, 1, 5, 6]
def baseStart_3509327 : Nat := 118140960795 + 3509327 * 2 ^ 59
def prefixEnd_3509327 : Nat := 4983230072969 + 3 ^ 40 * 3509327 * 2
def baseEnd_3509327 : Nat := 1201314349867264317115603

theorem tailTrace_3509327 : CollatzResearch.WordTrace tailWord_3509327 prefixEnd_3509327 1201314349867264317115603 := by
  unfold tailWord_3509327
  simp only [CollatzResearch.WordTrace]
  refine ⟨127995670957315099180390235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85330447304876732786926823 127995670957315099180390235)
  ·
    refine ⟨191993506435972648770585353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127995670957315099180390235 191993506435972648770585353)
    ·
      refine ⟨143995129826979486577939015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191993506435972648770585353 143995129826979486577939015)
      ·
        refine ⟨215992694740469229866908523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143995129826979486577939015 215992694740469229866908523)
        ·
          refine ⟨323989042110703844800362785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215992694740469229866908523 323989042110703844800362785)
          ·
            refine ⟨242991781583027883600272089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 323989042110703844800362785 242991781583027883600272089)
            ·
              refine ⟨182243836187270912700204067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 242991781583027883600272089 182243836187270912700204067)
              ·
                refine ⟨273365754280906369050306101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 182243836187270912700204067 273365754280906369050306101)
                ·
                  refine ⟨25628039463834972098466197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 273365754280906369050306101 25628039463834972098466197)
                  ·
                    refine ⟨1201314349867264317115603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25628039463834972098466197 1201314349867264317115603)
                    ·
                      rfl

theorem cell22_3509327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 5, 6].length) (baseStart_3509327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3509327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3509327 prefixEnd_3509327 := by exact prefixLift 3509327
  have htrace : WordTrace (prefixWord ++ tailWord_3509327) baseStart_3509327 baseEnd_3509327 := by
    simpa [prefixWord, tailWord_3509327, baseEnd_3509327] using wordTrace_append hprefix tailTrace_3509327
  have hstable : (prefixWord ++ tailWord_3509327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3509327).length < 2 ^ (prefixWord ++ tailWord_3509327).sum := by decide
  have hdescent : baseEnd_3509327 < baseStart_3509327 := by decide
  rcases family_descends (prefixWord ++ tailWord_3509327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3509438 : List Nat := [4, 2, 1, 1, 3, 2, 2, 2, 5]
def baseStart_3509438 : Nat := 118140960795 + 3509438 * 2 ^ 59
def prefixEnd_3509438 : Nat := 4983230072969 + 3 ^ 40 * 3509438 * 2
def baseEnd_3509438 : Nat := 400450782478565675863421

theorem tailTrace_3509438 : CollatzResearch.WordTrace tailWord_3509438 prefixEnd_3509438 400450782478565675863421 := by
  unfold tailWord_3509438
  simp only [CollatzResearch.WordTrace]
  refine ⟨15999964932489120642210121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85333146306608643425120645 15999964932489120642210121)
  ·
    refine ⟨11999973699366840481657591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15999964932489120642210121 11999973699366840481657591)
    ·
      refine ⟨17999960549050260722486387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11999973699366840481657591 17999960549050260722486387)
      ·
        refine ⟨26999940823575391083729581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17999960549050260722486387 26999940823575391083729581)
        ·
          refine ⟨10124977808840771656398593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26999940823575391083729581 10124977808840771656398593)
          ·
            refine ⟨7593733356630578742298945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10124977808840771656398593 7593733356630578742298945)
            ·
              refine ⟨5695300017472934056724209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7593733356630578742298945 5695300017472934056724209)
              ·
                refine ⟨4271475013104700542543157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5695300017472934056724209 4271475013104700542543157)
                ·
                  refine ⟨400450782478565675863421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4271475013104700542543157 400450782478565675863421)
                  ·
                    rfl

theorem cell22_3509438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 2, 2, 5].length) (baseStart_3509438 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3509438 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3509438 prefixEnd_3509438 := by exact prefixLift 3509438
  have htrace : WordTrace (prefixWord ++ tailWord_3509438) baseStart_3509438 baseEnd_3509438 := by
    simpa [prefixWord, tailWord_3509438, baseEnd_3509438] using wordTrace_append hprefix tailTrace_3509438
  have hstable : (prefixWord ++ tailWord_3509438).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3509438).length < 2 ^ (prefixWord ++ tailWord_3509438).sum := by decide
  have hdescent : baseEnd_3509438 < baseStart_3509438 := by decide
  rcases family_descends (prefixWord ++ tailWord_3509438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3509483 : List Nat := [1, 1, 1, 1, 2, 7, 2, 3, 4]
def baseStart_3509483 : Nat := 118140960795 + 3509483 * 2 ^ 59
def prefixEnd_3509483 : Nat := 4983230072969 + 3 ^ 40 * 3509483 * 2
def baseEnd_3509483 : Nat := 400455917285110636738375

theorem tailTrace_3509483 : CollatzResearch.WordTrace tailWord_3509483 prefixEnd_3509483 400455917285110636738375 := by
  unfold tailWord_3509483
  simp only [CollatzResearch.WordTrace]
  refine ⟨128001360744749937823069103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85334240496499958548712735 128001360744749937823069103)
  ·
    refine ⟨192002041117124906734603655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128001360744749937823069103 192002041117124906734603655)
    ·
      refine ⟨288003061675687360101905483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192002041117124906734603655 288003061675687360101905483)
      ·
        refine ⟨432004592513531040152858225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 288003061675687360101905483 432004592513531040152858225)
        ·
          refine ⟨324003444385148280114643669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 432004592513531040152858225 324003444385148280114643669)
          ·
            refine ⟨7593830727776912815186961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 324003444385148280114643669 7593830727776912815186961)
            ·
              refine ⟨5695373045832684611390221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7593830727776912815186961 5695373045832684611390221)
              ·
                refine ⟨2135764892187256729271333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5695373045832684611390221 2135764892187256729271333)
                ·
                  refine ⟨400455917285110636738375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2135764892187256729271333 400455917285110636738375)
                  ·
                    rfl

theorem cell22_3509483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 2, 3, 4].length) (baseStart_3509483 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3509483 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3509483 prefixEnd_3509483 := by exact prefixLift 3509483
  have htrace : WordTrace (prefixWord ++ tailWord_3509483) baseStart_3509483 baseEnd_3509483 := by
    simpa [prefixWord, tailWord_3509483, baseEnd_3509483] using wordTrace_append hprefix tailTrace_3509483
  have hstable : (prefixWord ++ tailWord_3509483).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3509483).length < 2 ^ (prefixWord ++ tailWord_3509483).sum := by decide
  have hdescent : baseEnd_3509483 < baseStart_3509483 := by decide
  rcases family_descends (prefixWord ++ tailWord_3509483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3509485 : List Nat := [1, 5, 1, 2, 2, 1, 4, 1, 1, 4]
def baseStart_3509485 : Nat := 118140960795 + 3509485 * 2 ^ 59
def prefixEnd_3509485 : Nat := 4983230072969 + 3 ^ 40 * 3509485 * 2
def baseEnd_3509485 : Nat := 1201368436496204571665119

theorem tailTrace_3509485 : CollatzResearch.WordTrace tailWord_3509485 prefixEnd_3509485 1201368436496204571665119 := by
  unfold tailWord_3509485
  simp only [CollatzResearch.WordTrace]
  refine ⟨128001433690742692164641909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85334289127161794776427939 128001433690742692164641909)
  ·
    refine ⟨12000134408507127390435179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 128001433690742692164641909 12000134408507127390435179)
    ·
      refine ⟨18000201612760691085652769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12000134408507127390435179 18000201612760691085652769)
      ·
        refine ⟨13500151209570518314239577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18000201612760691085652769 13500151209570518314239577)
        ·
          refine ⟨10125113407177888735679683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13500151209570518314239577 10125113407177888735679683)
          ·
            refine ⟨15187670110766833103519525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10125113407177888735679683 15187670110766833103519525)
            ·
              refine ⟨2847688145768781206909911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15187670110766833103519525 2847688145768781206909911)
              ·
                refine ⟨4271532218653171810364867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2847688145768781206909911 4271532218653171810364867)
                ·
                  refine ⟨6407298327979757715547301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4271532218653171810364867 6407298327979757715547301)
                  ·
                    refine ⟨1201368436496204571665119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6407298327979757715547301 1201368436496204571665119)
                    ·
                      rfl

theorem cell22_3509485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 4, 1, 1, 4].length) (baseStart_3509485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3509485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3509485 prefixEnd_3509485 := by exact prefixLift 3509485
  have htrace : WordTrace (prefixWord ++ tailWord_3509485) baseStart_3509485 baseEnd_3509485 := by
    simpa [prefixWord, tailWord_3509485, baseEnd_3509485] using wordTrace_append hprefix tailTrace_3509485
  have hstable : (prefixWord ++ tailWord_3509485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3509485).length < 2 ^ (prefixWord ++ tailWord_3509485).sum := by decide
  have hdescent : baseEnd_3509485 < baseStart_3509485 := by decide
  rcases family_descends (prefixWord ++ tailWord_3509485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3509515 : List Nat := [1, 1, 1, 1, 5, 4, 3, 1, 2, 3]
def baseStart_3509515 : Nat := 118140960795 + 3509515 * 2 ^ 59
def prefixEnd_3509515 : Nat := 4983230072969 + 3 ^ 40 * 3509515 * 2
def baseEnd_3509515 : Nat := 1201378706109294493415027

theorem tailTrace_3509515 : CollatzResearch.WordTrace tailWord_3509515 prefixEnd_3509515 1201378706109294493415027 := by
  unfold tailWord_3509515
  simp only [CollatzResearch.WordTrace]
  refine ⟨128002527880634007288233999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85335018587089338192155999 128002527880634007288233999)
  ·
    refine ⟨192003791820951010932350999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128002527880634007288233999 192003791820951010932350999)
    ·
      refine ⟨288005687731426516398526499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192003791820951010932350999 288005687731426516398526499)
      ·
        refine ⟨432008531597139774597789749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 288005687731426516398526499 432008531597139774597789749)
        ·
          refine ⟨40500799837231853868542789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 432008531597139774597789749 40500799837231853868542789)
          ·
            refine ⟨7593899969480972600351773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40500799837231853868542789 7593899969480972600351773)
            ·
              refine ⟨2847712488555364725131915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7593899969480972600351773 2847712488555364725131915)
              ·
                refine ⟨4271568732833047087697873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2847712488555364725131915 4271568732833047087697873)
                ·
                  refine ⟨3203676549624785315773405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4271568732833047087697873 3203676549624785315773405)
                  ·
                    refine ⟨1201378706109294493415027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3203676549624785315773405 1201378706109294493415027)
                    ·
                      rfl

theorem cell22_3509515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 3, 1, 2, 3].length) (baseStart_3509515 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3509515 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3509515 prefixEnd_3509515 := by exact prefixLift 3509515
  have htrace : WordTrace (prefixWord ++ tailWord_3509515) baseStart_3509515 baseEnd_3509515 := by
    simpa [prefixWord, tailWord_3509515, baseEnd_3509515] using wordTrace_append hprefix tailTrace_3509515
  have hstable : (prefixWord ++ tailWord_3509515).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3509515).length < 2 ^ (prefixWord ++ tailWord_3509515).sum := by decide
  have hdescent : baseEnd_3509515 < baseStart_3509515 := by decide
  rcases family_descends (prefixWord ++ tailWord_3509515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3509528 : List Nat := [2, 1, 2, 3, 1, 5, 2, 6]
def baseStart_3509528 : Nat := 118140960795 + 3509528 * 2 ^ 59
def prefixEnd_3509528 : Nat := 4983230072969 + 3 ^ 40 * 3509528 * 2
def baseEnd_3509528 : Nat := 133487017363885199204443

theorem tailTrace_3509528 : CollatzResearch.WordTrace tailWord_3509528 prefixEnd_3509528 133487017363885199204443 := by
  unfold tailWord_3509528
  simp only [CollatzResearch.WordTrace]
  refine ⟨64001501014793455254228619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85335334686391273672304825 64001501014793455254228619)
  ·
    refine ⟨96002251522190182881342929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64001501014793455254228619 96002251522190182881342929)
    ·
      refine ⟨72001688641642637161007197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96002251522190182881342929 72001688641642637161007197)
      ·
        refine ⟨27000633240615988935377699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72001688641642637161007197 27000633240615988935377699)
        ·
          refine ⟨40500949860923983403066549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27000633240615988935377699 40500949860923983403066549)
          ·
            refine ⟨3796964049461623444037489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 40500949860923983403066549 3796964049461623444037489)
            ·
              refine ⟨2847723037096217583028117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3796964049461623444037489 2847723037096217583028117)
              ·
                refine ⟨133487017363885199204443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2847723037096217583028117 133487017363885199204443)
                ·
                  rfl

theorem cell22_3509528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 2, 6].length) (baseStart_3509528 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3509528 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3509528 prefixEnd_3509528 := by exact prefixLift 3509528
  have htrace : WordTrace (prefixWord ++ tailWord_3509528) baseStart_3509528 baseEnd_3509528 := by
    simpa [prefixWord, tailWord_3509528, baseEnd_3509528] using wordTrace_append hprefix tailTrace_3509528
  have hstable : (prefixWord ++ tailWord_3509528).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3509528).length < 2 ^ (prefixWord ++ tailWord_3509528).sum := by decide
  have hdescent : baseEnd_3509528 < baseStart_3509528 := by decide
  rcases family_descends (prefixWord ++ tailWord_3509528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3509534 : List Nat := [4, 3, 2, 1, 2, 2, 1, 3, 4]
def baseStart_3509534 : Nat := 118140960795 + 3509534 * 2 ^ 59
def prefixEnd_3509534 : Nat := 4983230072969 + 3 ^ 40 * 3509534 * 2
def baseEnd_3509534 : Nat := 400461736732528259063323

theorem tailTrace_3509534 : CollatzResearch.WordTrace tailWord_3509534 prefixEnd_3509534 400461736732528259063323 := by
  unfold tailWord_3509534
  simp only [CollatzResearch.WordTrace]
  refine ⟨16000402608445646691646957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85335480578376782355450437 16000402608445646691646957)
  ·
    refine ⟨6000150978167117509367609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16000402608445646691646957 6000150978167117509367609)
    ·
      refine ⟨4500113233625338132025707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6000150978167117509367609 4500113233625338132025707)
      ·
        refine ⟨6750169850438007198038561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4500113233625338132025707 6750169850438007198038561)
        ·
          refine ⟨5062627387828505398528921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6750169850438007198038561 5062627387828505398528921)
          ·
            refine ⟨3796970540871379048896691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5062627387828505398528921 3796970540871379048896691)
            ·
              refine ⟨5695455811307068573345037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3796970540871379048896691 5695455811307068573345037)
              ·
                refine ⟨2135795929240150715004389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5695455811307068573345037 2135795929240150715004389)
                ·
                  refine ⟨400461736732528259063323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2135795929240150715004389 400461736732528259063323)
                  ·
                    rfl

theorem cell22_3509534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 1, 3, 4].length) (baseStart_3509534 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3509534 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3509534 prefixEnd_3509534 := by exact prefixLift 3509534
  have htrace : WordTrace (prefixWord ++ tailWord_3509534) baseStart_3509534 baseEnd_3509534 := by
    simpa [prefixWord, tailWord_3509534, baseEnd_3509534] using wordTrace_append hprefix tailTrace_3509534
  have hstable : (prefixWord ++ tailWord_3509534).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3509534).length < 2 ^ (prefixWord ++ tailWord_3509534).sum := by decide
  have hdescent : baseEnd_3509534 < baseStart_3509534 := by decide
  rcases family_descends (prefixWord ++ tailWord_3509534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3509616 : List Nat := [2, 1, 1, 1, 4, 2, 1, 2, 3, 5]
def baseStart_3509616 : Nat := 118140960795 + 3509616 * 2 ^ 59
def prefixEnd_3509616 : Nat := 4983230072969 + 3 ^ 40 * 3509616 * 2
def baseEnd_3509616 : Nat := 1201413280473363896639717

theorem tailTrace_3509616 : CollatzResearch.WordTrace tailWord_3509616 prefixEnd_3509616 1201413280473363896639717 := by
  unfold tailWord_3509616
  simp only [CollatzResearch.WordTrace]
  refine ⟨64003105826634050768830351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85337474435512067691773801 64003105826634050768830351)
  ·
    refine ⟨96004658739951076153245527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64003105826634050768830351 96004658739951076153245527)
    ·
      refine ⟨144006988109926614229868291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96004658739951076153245527 144006988109926614229868291)
      ·
        refine ⟨216010482164889921344802437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144006988109926614229868291 216010482164889921344802437)
        ·
          refine ⟨40501965405916860252150457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 216010482164889921344802437 40501965405916860252150457)
          ·
            refine ⟨30376474054437645189112843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40501965405916860252150457 30376474054437645189112843)
            ·
              refine ⟨45564711081656467783669265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30376474054437645189112843 45564711081656467783669265)
              ·
                refine ⟨34173533311242350837751949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45564711081656467783669265 34173533311242350837751949)
                ·
                  refine ⟨12815074991715881564156981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34173533311242350837751949 12815074991715881564156981)
                  ·
                    refine ⟨1201413280473363896639717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12815074991715881564156981 1201413280473363896639717)
                    ·
                      rfl

theorem cell22_3509616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 2, 3, 5].length) (baseStart_3509616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3509616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3509616 prefixEnd_3509616 := by exact prefixLift 3509616
  have htrace : WordTrace (prefixWord ++ tailWord_3509616) baseStart_3509616 baseEnd_3509616 := by
    simpa [prefixWord, tailWord_3509616, baseEnd_3509616] using wordTrace_append hprefix tailTrace_3509616
  have hstable : (prefixWord ++ tailWord_3509616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3509616).length < 2 ^ (prefixWord ++ tailWord_3509616).sum := by decide
  have hdescent : baseEnd_3509616 < baseStart_3509616 := by decide
  rcases family_descends (prefixWord ++ tailWord_3509616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3509652 : List Nat := [2, 4, 2, 1, 2, 2, 2, 3, 4]
def baseStart_3509652 : Nat := 118140960795 + 3509652 * 2 ^ 59
def prefixEnd_3509652 : Nat := 4983230072969 + 3 ^ 40 * 3509652 * 2
def baseEnd_3509652 : Nat := 400475201336357267579869

theorem tailTrace_3509652 : CollatzResearch.WordTrace tailWord_3509652 prefixEnd_3509652 400475201336357267579869 := by
  unfold tailWord_3509652
  simp only [CollatzResearch.WordTrace]
  refine ⟨64003762340568839842985605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85338349787425119790647473 64003762340568839842985605)
  ·
    refine ⟨12000705438856657470559801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64003762340568839842985605 12000705438856657470559801)
    ·
      refine ⟨9000529079142493102919851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12000705438856657470559801 9000529079142493102919851)
      ·
        refine ⟨13500793618713739654379777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9000529079142493102919851 13500793618713739654379777)
        ·
          refine ⟨10125595214035304740784833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13500793618713739654379777 10125595214035304740784833)
          ·
            refine ⟨7594196410526478555588625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10125595214035304740784833 7594196410526478555588625)
            ·
              refine ⟨5695647307894858916691469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7594196410526478555588625 5695647307894858916691469)
              ·
                refine ⟨2135867740460572093759301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5695647307894858916691469 2135867740460572093759301)
                ·
                  refine ⟨400475201336357267579869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2135867740460572093759301 400475201336357267579869)
                  ·
                    rfl

theorem cell22_3509652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 2, 3, 4].length) (baseStart_3509652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3509652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3509652 prefixEnd_3509652 := by exact prefixLift 3509652
  have htrace : WordTrace (prefixWord ++ tailWord_3509652) baseStart_3509652 baseEnd_3509652 := by
    simpa [prefixWord, tailWord_3509652, baseEnd_3509652] using wordTrace_append hprefix tailTrace_3509652
  have hstable : (prefixWord ++ tailWord_3509652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3509652).length < 2 ^ (prefixWord ++ tailWord_3509652).sum := by decide
  have hdescent : baseEnd_3509652 < baseStart_3509652 := by decide
  rcases family_descends (prefixWord ++ tailWord_3509652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3509676 : List Nat := [2, 2, 1, 1, 1, 1, 4, 1, 1, 8]
def baseStart_3509676 : Nat := 118140960795 + 3509676 * 2 ^ 59
def prefixEnd_3509676 : Nat := 4983230072969 + 3 ^ 40 * 3509676 * 2
def baseEnd_3509676 : Nat := 1201433819699543740139533

theorem tailTrace_3509676 : CollatzResearch.WordTrace tailWord_3509676 prefixEnd_3509676 1201433819699543740139533 := by
  unfold tailWord_3509676
  simp only [CollatzResearch.WordTrace]
  refine ⟨64004200016525365892422441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85338933355367154523229921 64004200016525365892422441)
  ·
    refine ⟨48003150012394024419316831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64004200016525365892422441 48003150012394024419316831)
    ·
      refine ⟨72004725018591036628975247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48003150012394024419316831 72004725018591036628975247)
      ·
        refine ⟨108007087527886554943462871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72004725018591036628975247 108007087527886554943462871)
        ·
          refine ⟨162010631291829832415194307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108007087527886554943462871 162010631291829832415194307)
          ·
            refine ⟨243015946937744748622791461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162010631291829832415194307 243015946937744748622791461)
            ·
              refine ⟨45565490050827140366773399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 243015946937744748622791461 45565490050827140366773399)
              ·
                refine ⟨68348235076240710550160099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45565490050827140366773399 68348235076240710550160099)
                ·
                  refine ⟨102522352614361065825240149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68348235076240710550160099 102522352614361065825240149)
                  ·
                    refine ⟨1201433819699543740139533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 102522352614361065825240149 1201433819699543740139533)
                    ·
                      rfl

theorem cell22_3509676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 8].length) (baseStart_3509676 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3509676 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3509676 prefixEnd_3509676 := by exact prefixLift 3509676
  have htrace : WordTrace (prefixWord ++ tailWord_3509676) baseStart_3509676 baseEnd_3509676 := by
    simpa [prefixWord, tailWord_3509676, baseEnd_3509676] using wordTrace_append hprefix tailTrace_3509676
  have hstable : (prefixWord ++ tailWord_3509676).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3509676).length < 2 ^ (prefixWord ++ tailWord_3509676).sum := by decide
  have hdescent : baseEnd_3509676 < baseStart_3509676 := by decide
  rcases family_descends (prefixWord ++ tailWord_3509676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3509708 : List Nat := [2, 2, 1, 4, 2, 1, 1, 2, 7]
def baseStart_3509708 : Nat := 118140960795 + 3509708 * 2 ^ 59
def prefixEnd_3509708 : Nat := 4983230072969 + 3 ^ 40 * 3509708 * 2
def baseEnd_3509708 : Nat := 400481591317835441113145

theorem tailTrace_3509708 : CollatzResearch.WordTrace tailWord_3509708 prefixEnd_3509708 400481591317835441113145 := by
  unfold tailWord_3509708
  simp only [CollatzResearch.WordTrace]
  refine ⟨64004783584467400625004889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85339711445956534166673185 64004783584467400625004889)
  ·
    refine ⟨48003587688350550468753667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64004783584467400625004889 48003587688350550468753667)
    ·
      refine ⟨72005381532525825703130501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48003587688350550468753667 72005381532525825703130501)
      ·
        refine ⟨13501009037348592319336969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72005381532525825703130501 13501009037348592319336969)
        ·
          refine ⟨10125756778011444239502727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13501009037348592319336969 10125756778011444239502727)
          ·
            refine ⟨15188635167017166359254091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10125756778011444239502727 15188635167017166359254091)
            ·
              refine ⟨22782952750525749538881137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15188635167017166359254091 22782952750525749538881137)
              ·
                refine ⟨17087214562894312154160853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22782952750525749538881137 17087214562894312154160853)
                ·
                  refine ⟨400481591317835441113145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17087214562894312154160853 400481591317835441113145)
                  ·
                    rfl

theorem cell22_3509708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 2, 7].length) (baseStart_3509708 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3509708 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3509708 prefixEnd_3509708 := by exact prefixLift 3509708
  have htrace : WordTrace (prefixWord ++ tailWord_3509708) baseStart_3509708 baseEnd_3509708 := by
    simpa [prefixWord, tailWord_3509708, baseEnd_3509708] using wordTrace_append hprefix tailTrace_3509708
  have hstable : (prefixWord ++ tailWord_3509708).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3509708).length < 2 ^ (prefixWord ++ tailWord_3509708).sum := by decide
  have hdescent : baseEnd_3509708 < baseStart_3509708 := by decide
  rcases family_descends (prefixWord ++ tailWord_3509708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3509729 : List Nat := [1, 2, 3, 1, 2, 4, 3, 2, 1, 3]
def baseStart_3509729 : Nat := 118140960795 + 3509729 * 2 ^ 59
def prefixEnd_3509729 : Nat := 4983230072969 + 3 ^ 40 * 3509729 * 2
def baseEnd_3509729 : Nat := 1201451962682669268564371

theorem tailTrace_3509729 : CollatzResearch.WordTrace tailWord_3509729 prefixEnd_3509729 1201451962682669268564371 := by
  unfold tailWord_3509729
  simp only [CollatzResearch.WordTrace]
  refine ⟨128010333101858721836524241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85340222067905814557682827 128010333101858721836524241)
  ·
    refine ⟨96007749826394041377393181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128010333101858721836524241 96007749826394041377393181)
    ·
      refine ⟨36002906184897765516522443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96007749826394041377393181 36002906184897765516522443)
      ·
        refine ⟨54004359277346648274783665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36002906184897765516522443 54004359277346648274783665)
        ·
          refine ⟨40503269458009986206087749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54004359277346648274783665 40503269458009986206087749)
          ·
            refine ⟨7594363023376872413641453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40503269458009986206087749 7594363023376872413641453)
            ·
              refine ⟨2847886133766327155115545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7594363023376872413641453 2847886133766327155115545)
              ·
                refine ⟨2135914600324745366336659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2847886133766327155115545 2135914600324745366336659)
                ·
                  refine ⟨3203871900487118049504989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2135914600324745366336659 3203871900487118049504989)
                  ·
                    refine ⟨1201451962682669268564371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3203871900487118049504989 1201451962682669268564371)
                    ·
                      rfl

theorem cell22_3509729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 3, 2, 1, 3].length) (baseStart_3509729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3509729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3509729 prefixEnd_3509729 := by exact prefixLift 3509729
  have htrace : WordTrace (prefixWord ++ tailWord_3509729) baseStart_3509729 baseEnd_3509729 := by
    simpa [prefixWord, tailWord_3509729, baseEnd_3509729] using wordTrace_append hprefix tailTrace_3509729
  have hstable : (prefixWord ++ tailWord_3509729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3509729).length < 2 ^ (prefixWord ++ tailWord_3509729).sum := by decide
  have hdescent : baseEnd_3509729 < baseStart_3509729 := by decide
  rcases family_descends (prefixWord ++ tailWord_3509729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3509768 : List Nat := [2, 1, 3, 2, 1, 1, 3, 1, 3, 5]
def baseStart_3509768 : Nat := 118140960795 + 3509768 * 2 ^ 59
def prefixEnd_3509768 : Nat := 4983230072969 + 3 ^ 40 * 3509768 * 2
def baseEnd_3509768 : Nat := 1201465313179686166839251

theorem tailTrace_3509768 : CollatzResearch.WordTrace tailWord_3509768 prefixEnd_3509768 1201465313179686166839251 := by
  unfold tailWord_3509768
  simp only [CollatzResearch.WordTrace]
  refine ⟨64005877774358715748596979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85341170365811620998129305 64005877774358715748596979)
  ·
    refine ⟨96008816661538073622895469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64005877774358715748596979 96008816661538073622895469)
    ·
      refine ⟨36003306248076777608585801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96008816661538073622895469 36003306248076777608585801)
      ·
        refine ⟨27002479686057583206439351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36003306248076777608585801 27002479686057583206439351)
        ·
          refine ⟨40503719529086374809659027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27002479686057583206439351 40503719529086374809659027)
          ·
            refine ⟨60755579293629562214488541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40503719529086374809659027 60755579293629562214488541)
            ·
              refine ⟨22783342235111085830433203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60755579293629562214488541 22783342235111085830433203)
              ·
                refine ⟨34175013352666628745649805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22783342235111085830433203 34175013352666628745649805)
                ·
                  refine ⟨12815630007249985779618677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34175013352666628745649805 12815630007249985779618677)
                  ·
                    refine ⟨1201465313179686166839251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12815630007249985779618677 1201465313179686166839251)
                    ·
                      rfl

theorem cell22_3509768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 1, 3, 5].length) (baseStart_3509768 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3509768 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3509768 prefixEnd_3509768 := by exact prefixLift 3509768
  have htrace : WordTrace (prefixWord ++ tailWord_3509768) baseStart_3509768 baseEnd_3509768 := by
    simpa [prefixWord, tailWord_3509768, baseEnd_3509768] using wordTrace_append hprefix tailTrace_3509768
  have hstable : (prefixWord ++ tailWord_3509768).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3509768).length < 2 ^ (prefixWord ++ tailWord_3509768).sum := by decide
  have hdescent : baseEnd_3509768 < baseStart_3509768 := by decide
  rcases family_descends (prefixWord ++ tailWord_3509768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3509780 : List Nat := [2, 4, 3, 1, 3, 1, 2, 2, 1, 3]
def baseStart_3509780 : Nat := 118140960795 + 3509780 * 2 ^ 59
def prefixEnd_3509780 : Nat := 4983230072969 + 3 ^ 40 * 3509780 * 2
def baseEnd_3509780 : Nat := 1201469421024922135539215

theorem tailTrace_3509780 : CollatzResearch.WordTrace tailWord_3509780 prefixEnd_3509780 1201469421024922135539215 := by
  unfold tailWord_3509780
  simp only [CollatzResearch.WordTrace]
  refine ⟨64006096612336978773315397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85341462149782638364420529 64006096612336978773315397)
  ·
    refine ⟨12001143114813183519996637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64006096612336978773315397 12001143114813183519996637)
    ·
      refine ⟨4500428668054943819998739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12001143114813183519996637 4500428668054943819998739)
      ·
        refine ⟨6750643002082415729998109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4500428668054943819998739 6750643002082415729998109)
        ·
          refine ⟨2531491125780905898749291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6750643002082415729998109 2531491125780905898749291)
          ·
            refine ⟨3797236688671358848123937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2531491125780905898749291 3797236688671358848123937)
            ·
              refine ⟨2847927516503519136092953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3797236688671358848123937 2847927516503519136092953)
              ·
                refine ⟨2135945637377639352069715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2847927516503519136092953 2135945637377639352069715)
                ·
                  refine ⟨3203918456066459028104573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2135945637377639352069715 3203918456066459028104573)
                  ·
                    refine ⟨1201469421024922135539215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3203918456066459028104573 1201469421024922135539215)
                    ·
                      rfl

theorem cell22_3509780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 2, 2, 1, 3].length) (baseStart_3509780 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3509780 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3509780 prefixEnd_3509780 := by exact prefixLift 3509780
  have htrace : WordTrace (prefixWord ++ tailWord_3509780) baseStart_3509780 baseEnd_3509780 := by
    simpa [prefixWord, tailWord_3509780, baseEnd_3509780] using wordTrace_append hprefix tailTrace_3509780
  have hstable : (prefixWord ++ tailWord_3509780).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3509780).length < 2 ^ (prefixWord ++ tailWord_3509780).sum := by decide
  have hdescent : baseEnd_3509780 < baseStart_3509780 := by decide
  rcases family_descends (prefixWord ++ tailWord_3509780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3509802 : List Nat := [3, 1, 4, 1, 1, 1, 1, 5, 2, 3]
def baseStart_3509802 : Nat := 118140960795 + 3509802 * 2 ^ 59
def prefixEnd_3509802 : Nat := 4983230072969 + 3 ^ 40 * 3509802 * 2
def baseEnd_3509802 : Nat := 1201476952074521411489147

theorem tailTrace_3509802 : CollatzResearch.WordTrace tailWord_3509802 prefixEnd_3509802 1201476952074521411489147 := by
  unfold tailWord_3509802
  simp only [CollatzResearch.WordTrace]
  refine ⟨32003248907648563825982915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85341997087062836869287773 32003248907648563825982915)
  ·
    refine ⟨48004873361472845738974373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32003248907648563825982915 48004873361472845738974373)
    ·
      refine ⟨9000913755276158576057695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48004873361472845738974373 9000913755276158576057695)
      ·
        refine ⟨13501370632914237864086543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9000913755276158576057695 13501370632914237864086543)
        ·
          refine ⟨20252055949371356796129815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13501370632914237864086543 20252055949371356796129815)
          ·
            refine ⟨30378083924057035194194723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20252055949371356796129815 30378083924057035194194723)
            ·
              refine ⟨45567125886085552791292085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30378083924057035194194723 45567125886085552791292085)
              ·
                refine ⟨4271918051820520574183633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45567125886085552791292085 4271918051820520574183633)
                ·
                  refine ⟨3203938538865390430637725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4271918051820520574183633 3203938538865390430637725)
                  ·
                    refine ⟨1201476952074521411489147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3203938538865390430637725 1201476952074521411489147)
                    ·
                      rfl

theorem cell22_3509802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 5, 2, 3].length) (baseStart_3509802 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3509802 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3509802 prefixEnd_3509802 := by exact prefixLift 3509802
  have htrace : WordTrace (prefixWord ++ tailWord_3509802) baseStart_3509802 baseEnd_3509802 := by
    simpa [prefixWord, tailWord_3509802, baseEnd_3509802] using wordTrace_append hprefix tailTrace_3509802
  have hstable : (prefixWord ++ tailWord_3509802).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3509802).length < 2 ^ (prefixWord ++ tailWord_3509802).sum := by decide
  have hdescent : baseEnd_3509802 < baseStart_3509802 := by decide
  rcases family_descends (prefixWord ++ tailWord_3509802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3509815 : List Nat := [1, 1, 3, 1, 2, 5, 3, 6]
def baseStart_3509815 : Nat := 118140960795 + 3509815 * 2 ^ 59
def prefixEnd_3509815 : Nat := 4983230072969 + 3 ^ 40 * 3509815 * 2
def baseEnd_3509815 : Nat := 133497933582243745657123

theorem tailTrace_3509815 : CollatzResearch.WordTrace tailWord_3509815 prefixEnd_3509815 133497933582243745657123 := by
  unfold tailWord_3509815
  simp only [CollatzResearch.WordTrace]
  refine ⟨128013469779547158524154899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85342313186364772349436599 128013469779547158524154899)
  ·
    refine ⟨192020204669320737786232349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128013469779547158524154899 192020204669320737786232349)
    ·
      refine ⟨72007576750995276669837131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 192020204669320737786232349 72007576750995276669837131)
      ·
        refine ⟨108011365126492915004755697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72007576750995276669837131 108011365126492915004755697)
        ·
          refine ⟨81008523844869686253566773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108011365126492915004755697 81008523844869686253566773)
          ·
            refine ⟨7594549110456533086271885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 81008523844869686253566773 7594549110456533086271885)
            ·
              refine ⟨2847955916421199907351957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7594549110456533086271885 2847955916421199907351957)
              ·
                refine ⟨133497933582243745657123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2847955916421199907351957 133497933582243745657123)
                ·
                  rfl

theorem cell22_3509815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 3, 6].length) (baseStart_3509815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3509815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3509815 prefixEnd_3509815 := by exact prefixLift 3509815
  have htrace : WordTrace (prefixWord ++ tailWord_3509815) baseStart_3509815 baseEnd_3509815 := by
    simpa [prefixWord, tailWord_3509815, baseEnd_3509815] using wordTrace_append hprefix tailTrace_3509815
  have hstable : (prefixWord ++ tailWord_3509815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3509815).length < 2 ^ (prefixWord ++ tailWord_3509815).sum := by decide
  have hdescent : baseEnd_3509815 < baseStart_3509815 := by decide
  rcases family_descends (prefixWord ++ tailWord_3509815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3509817 : List Nat := [1, 2, 1, 5, 1, 4, 1, 1, 2, 4]
def baseStart_3509817 : Nat := 118140960795 + 3509817 * 2 ^ 59
def prefixEnd_3509817 : Nat := 4983230072969 + 3 ^ 40 * 3509817 * 2
def baseEnd_3509817 : Nat := 1201482086881066372364101

theorem tailTrace_3509817 : CollatzResearch.WordTrace tailWord_3509817 prefixEnd_3509817 1201482086881066372364101 := by
  unfold tailWord_3509817
  simp only [CollatzResearch.WordTrace]
  refine ⟨128013542725539912865727705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85342361817026608577151803 128013542725539912865727705)
  ·
    refine ⟨96010157044154934649295779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128013542725539912865727705 96010157044154934649295779)
    ·
      refine ⟨144015235566232401973943669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96010157044154934649295779 144015235566232401973943669)
      ·
        refine ⟨13501428334334287685057219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 144015235566232401973943669 13501428334334287685057219)
        ·
          refine ⟨20252142501501431527585829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13501428334334287685057219 20252142501501431527585829)
          ·
            refine ⟨3797276719031518411422343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20252142501501431527585829 3797276719031518411422343)
            ·
              refine ⟨5695915078547277617133515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3797276719031518411422343 5695915078547277617133515)
              ·
                refine ⟨8543872617820916425700273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5695915078547277617133515 8543872617820916425700273)
                ·
                  refine ⟨6407904463365687319275205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8543872617820916425700273 6407904463365687319275205)
                  ·
                    refine ⟨1201482086881066372364101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6407904463365687319275205 1201482086881066372364101)
                    ·
                      rfl

theorem cell22_3509817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 1, 1, 2, 4].length) (baseStart_3509817 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3509817 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3509817 prefixEnd_3509817 := by exact prefixLift 3509817
  have htrace : WordTrace (prefixWord ++ tailWord_3509817) baseStart_3509817 baseEnd_3509817 := by
    simpa [prefixWord, tailWord_3509817, baseEnd_3509817] using wordTrace_append hprefix tailTrace_3509817
  have hstable : (prefixWord ++ tailWord_3509817).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3509817).length < 2 ^ (prefixWord ++ tailWord_3509817).sum := by decide
  have hdescent : baseEnd_3509817 < baseStart_3509817 := by decide
  rcases family_descends (prefixWord ++ tailWord_3509817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3509847 : List Nat := [1, 1, 3, 2, 2, 4, 2, 1, 3, 3]
def baseStart_3509847 : Nat := 118140960795 + 3509847 * 2 ^ 59
def prefixEnd_3509847 : Nat := 4983230072969 + 3 ^ 40 * 3509847 * 2
def baseEnd_3509847 : Nat := 1201492356494156294114009

theorem tailTrace_3509847 : CollatzResearch.WordTrace tailWord_3509847 prefixEnd_3509847 1201492356494156294114009 := by
  unfold tailWord_3509847
  simp only [CollatzResearch.WordTrace]
  refine ⟨128014636915431227989319795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85343091276954151992879863 128014636915431227989319795)
  ·
    refine ⟨192021955373146841983979693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128014636915431227989319795 192021955373146841983979693)
    ·
      refine ⟨72008233264930065743992385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 192021955373146841983979693 72008233264930065743992385)
      ·
        refine ⟨54006174948697549307994289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72008233264930065743992385 54006174948697549307994289)
        ·
          refine ⟨40504631211523161980995717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54006174948697549307994289 40504631211523161980995717)
          ·
            refine ⟨7594618352160592871436697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40504631211523161980995717 7594618352160592871436697)
            ·
              refine ⟨5695963764120444653577523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7594618352160592871436697 5695963764120444653577523)
              ·
                refine ⟨8543945646180666980366285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5695963764120444653577523 8543945646180666980366285)
                ·
                  refine ⟨3203979617317750117637357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8543945646180666980366285 3203979617317750117637357)
                  ·
                    refine ⟨1201492356494156294114009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3203979617317750117637357 1201492356494156294114009)
                    ·
                      rfl

theorem cell22_3509847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 2, 1, 3, 3].length) (baseStart_3509847 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3509847 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3509847 prefixEnd_3509847 := by exact prefixLift 3509847
  have htrace : WordTrace (prefixWord ++ tailWord_3509847) baseStart_3509847 baseEnd_3509847 := by
    simpa [prefixWord, tailWord_3509847, baseEnd_3509847] using wordTrace_append hprefix tailTrace_3509847
  have hstable : (prefixWord ++ tailWord_3509847).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3509847).length < 2 ^ (prefixWord ++ tailWord_3509847).sum := by decide
  have hdescent : baseEnd_3509847 < baseStart_3509847 := by decide
  rcases family_descends (prefixWord ++ tailWord_3509847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3509853 : List Nat := [1, 4, 4, 2, 1, 1, 3, 1, 2, 3]
def baseStart_3509853 : Nat := 118140960795 + 3509853 * 2 ^ 59
def prefixEnd_3509853 : Nat := 4983230072969 + 3 ^ 40 * 3509853 * 2
def baseEnd_3509853 : Nat := 1201494410416774278463991

theorem tailTrace_3509853 : CollatzResearch.WordTrace tailWord_3509853 prefixEnd_3509853 1201494410416774278463991 := by
  unfold tailWord_3509853
  simp only [CollatzResearch.WordTrace]
  refine ⟨128014855753409491014038213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85343237168939660676025475 128014855753409491014038213)
  ·
    refine ⟨24002785453764279565132165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 128014855753409491014038213 24002785453764279565132165)
    ·
      refine ⟨4500522272580802418462281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24002785453764279565132165 4500522272580802418462281)
      ·
        refine ⟨3375391704435601813846711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4500522272580802418462281 3375391704435601813846711)
        ·
          refine ⟨5063087556653402720770067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3375391704435601813846711 5063087556653402720770067)
          ·
            refine ⟨7594631334980104081155101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5063087556653402720770067 7594631334980104081155101)
            ·
              refine ⟨2847986750617539030433163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7594631334980104081155101 2847986750617539030433163)
              ·
                refine ⟨4271980125926308545649745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2847986750617539030433163 4271980125926308545649745)
                ·
                  refine ⟨3203985094444731409237309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4271980125926308545649745 3203985094444731409237309)
                  ·
                    refine ⟨1201494410416774278463991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3203985094444731409237309 1201494410416774278463991)
                    ·
                      rfl

theorem cell22_3509853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 3, 1, 2, 3].length) (baseStart_3509853 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3509853 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3509853 prefixEnd_3509853 := by exact prefixLift 3509853
  have htrace : WordTrace (prefixWord ++ tailWord_3509853) baseStart_3509853 baseEnd_3509853 := by
    simpa [prefixWord, tailWord_3509853, baseEnd_3509853] using wordTrace_append hprefix tailTrace_3509853
  have hstable : (prefixWord ++ tailWord_3509853).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3509853).length < 2 ^ (prefixWord ++ tailWord_3509853).sum := by decide
  have hdescent : baseEnd_3509853 < baseStart_3509853 := by decide
  rcases family_descends (prefixWord ++ tailWord_3509853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3509873 : List Nat := [1, 2, 2, 2, 1, 1, 1, 2, 2, 8]
def baseStart_3509873 : Nat := 118140960795 + 3509873 * 2 ^ 59
def prefixEnd_3509873 : Nat := 4983230072969 + 3 ^ 40 * 3509873 * 2
def baseEnd_3509873 : Nat := 1201501256825500892963929

theorem tailTrace_3509873 : CollatzResearch.WordTrace tailWord_3509873 prefixEnd_3509873 1201501256825500892963929 := by
  unfold tailWord_3509873
  simp only [CollatzResearch.WordTrace]
  refine ⟨128015585213337034429766273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85343723475558022953177515 128015585213337034429766273)
  ·
    refine ⟨96011688910002775822324705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128015585213337034429766273 96011688910002775822324705)
    ·
      refine ⟨72008766682502081866743529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96011688910002775822324705 72008766682502081866743529)
      ·
        refine ⟨54006575011876561400057647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72008766682502081866743529 54006575011876561400057647)
        ·
          refine ⟨81009862517814842100086471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54006575011876561400057647 81009862517814842100086471)
          ·
            refine ⟨121514793776722263150129707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81009862517814842100086471 121514793776722263150129707)
            ·
              refine ⟨182272190665083394725194561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121514793776722263150129707 182272190665083394725194561)
              ·
                refine ⟨136704142998812546043895921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 182272190665083394725194561 136704142998812546043895921)
                ·
                  refine ⟨102528107249109409532921941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 136704142998812546043895921 102528107249109409532921941)
                  ·
                    refine ⟨1201501256825500892963929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 102528107249109409532921941 1201501256825500892963929)
                    ·
                      rfl

theorem cell22_3509873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 2, 8].length) (baseStart_3509873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3509873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3509873 prefixEnd_3509873 := by exact prefixLift 3509873
  have htrace : WordTrace (prefixWord ++ tailWord_3509873) baseStart_3509873 baseEnd_3509873 := by
    simpa [prefixWord, tailWord_3509873, baseEnd_3509873] using wordTrace_append hprefix tailTrace_3509873
  have hstable : (prefixWord ++ tailWord_3509873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3509873).length < 2 ^ (prefixWord ++ tailWord_3509873).sum := by decide
  have hdescent : baseEnd_3509873 < baseStart_3509873 := by decide
  rcases family_descends (prefixWord ++ tailWord_3509873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3509903 : List Nat := [1, 1, 2, 1, 1, 1, 1, 3, 2, 9]
def baseStart_3509903 : Nat := 118140960795 + 3509903 * 2 ^ 59
def prefixEnd_3509903 : Nat := 4983230072969 + 3 ^ 40 * 3509903 * 2
def baseEnd_3509903 : Nat := 1201511526438590814713837

theorem tailTrace_3509903 : CollatzResearch.WordTrace tailWord_3509903 prefixEnd_3509903 1201511526438590814713837 := by
  unfold tailWord_3509903
  simp only [CollatzResearch.WordTrace]
  refine ⟨128016679403228349553358363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85344452935485566368905575 128016679403228349553358363)
  ·
    refine ⟨192025019104842524330037545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128016679403228349553358363 192025019104842524330037545)
    ·
      refine ⟨144018764328631893247528159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192025019104842524330037545 144018764328631893247528159)
      ·
        refine ⟨216028146492947839871292239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144018764328631893247528159 216028146492947839871292239)
        ·
          refine ⟨324042219739421759806938359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216028146492947839871292239 324042219739421759806938359)
          ·
            refine ⟨486063329609132639710407539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 324042219739421759806938359 486063329609132639710407539)
            ·
              refine ⟨729094994413698959565611309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 486063329609132639710407539 729094994413698959565611309)
              ·
                refine ⟨273410622905137109837104241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 729094994413698959565611309 273410622905137109837104241)
                ·
                  refine ⟨205057967178852832377828181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 273410622905137109837104241 205057967178852832377828181)
                  ·
                    refine ⟨1201511526438590814713837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 205057967178852832377828181 1201511526438590814713837)
                    ·
                      rfl

theorem cell22_3509903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 2, 9].length) (baseStart_3509903 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3509903 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3509903 prefixEnd_3509903 := by exact prefixLift 3509903
  have htrace : WordTrace (prefixWord ++ tailWord_3509903) baseStart_3509903 baseEnd_3509903 := by
    simpa [prefixWord, tailWord_3509903, baseEnd_3509903] using wordTrace_append hprefix tailTrace_3509903
  have hstable : (prefixWord ++ tailWord_3509903).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3509903).length < 2 ^ (prefixWord ++ tailWord_3509903).sum := by decide
  have hdescent : baseEnd_3509903 < baseStart_3509903 := by decide
  rcases family_descends (prefixWord ++ tailWord_3509903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3509924 : List Nat := [2, 3, 1, 2, 2, 4, 1, 2, 1, 4]
def baseStart_3509924 : Nat := 118140960795 + 3509924 * 2 ^ 59
def prefixEnd_3509924 : Nat := 4983230072969 + 3 ^ 40 * 3509924 * 2
def baseEnd_3509924 : Nat := 1201518715167753759938773

theorem tailTrace_3509924 : CollatzResearch.WordTrace tailWord_3509924 prefixEnd_3509924 1201518715167753759938773 := by
  unfold tailWord_3509924
  simp only [CollatzResearch.WordTrace]
  refine ⟨64008722668076135069936413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85344963557434846759915217 64008722668076135069936413)
  ·
    refine ⟨24003271000528550651226155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64008722668076135069936413 24003271000528550651226155)
    ·
      refine ⟨36004906500792825976839233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24003271000528550651226155 36004906500792825976839233)
      ·
        refine ⟨27003679875594619482629425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36004906500792825976839233 27003679875594619482629425)
        ·
          refine ⟨20252759906695964611972069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27003679875594619482629425 20252759906695964611972069)
          ·
            refine ⟨3797392482505493364744763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20252759906695964611972069 3797392482505493364744763)
            ·
              refine ⟨5696088723758240047117145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3797392482505493364744763 5696088723758240047117145)
              ·
                refine ⟨4272066542818680035337859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5696088723758240047117145 4272066542818680035337859)
                ·
                  refine ⟨6408099814228020053006789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4272066542818680035337859 6408099814228020053006789)
                  ·
                    refine ⟨1201518715167753759938773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6408099814228020053006789 1201518715167753759938773)
                    ·
                      rfl

theorem cell22_3509924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 1, 2, 1, 4].length) (baseStart_3509924 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3509924 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3509924 prefixEnd_3509924 := by exact prefixLift 3509924
  have htrace : WordTrace (prefixWord ++ tailWord_3509924) baseStart_3509924 baseEnd_3509924 := by
    simpa [prefixWord, tailWord_3509924, baseEnd_3509924] using wordTrace_append hprefix tailTrace_3509924
  have hstable : (prefixWord ++ tailWord_3509924).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3509924).length < 2 ^ (prefixWord ++ tailWord_3509924).sum := by decide
  have hdescent : baseEnd_3509924 < baseStart_3509924 := by decide
  rcases family_descends (prefixWord ++ tailWord_3509924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3509941 : List Nat := [1, 3, 3, 3, 2, 1, 3, 1, 1, 4]
def baseStart_3509941 : Nat := 118140960795 + 3509941 * 2 ^ 59
def prefixEnd_3509941 : Nat := 4983230072969 + 3 ^ 40 * 3509941 * 2
def baseEnd_3509941 : Nat := 1201524534615171382263721

theorem tailTrace_3509941 : CollatzResearch.WordTrace tailWord_3509941 prefixEnd_3509941 1201524534615171382263721 := by
  unfold tailWord_3509941
  simp only [CollatzResearch.WordTrace]
  refine ⟨128018065377090682043241677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85345376918060454695494451 128018065377090682043241677)
  ·
    refine ⟨48006774516409005766215629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128018065377090682043241677 48006774516409005766215629)
    ·
      refine ⟨18002540443653377162330861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48006774516409005766215629 18002540443653377162330861)
      ·
        refine ⟨6750952666370016435874073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18002540443653377162330861 6750952666370016435874073)
        ·
          refine ⟨5063214499777512326905555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6750952666370016435874073 5063214499777512326905555)
          ·
            refine ⟨7594821749666268490358333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5063214499777512326905555 7594821749666268490358333)
            ·
              refine ⟨2848058156124850683884375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7594821749666268490358333 2848058156124850683884375)
              ·
                refine ⟨4272087234187276025826563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2848058156124850683884375 4272087234187276025826563)
                ·
                  refine ⟨6408130851280914038739845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4272087234187276025826563 6408130851280914038739845)
                  ·
                    refine ⟨1201524534615171382263721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6408130851280914038739845 1201524534615171382263721)
                    ·
                      rfl

theorem cell22_3509941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 3, 1, 1, 4].length) (baseStart_3509941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3509941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3509941 prefixEnd_3509941 := by exact prefixLift 3509941
  have htrace : WordTrace (prefixWord ++ tailWord_3509941) baseStart_3509941 baseEnd_3509941 := by
    simpa [prefixWord, tailWord_3509941, baseEnd_3509941] using wordTrace_append hprefix tailTrace_3509941
  have hstable : (prefixWord ++ tailWord_3509941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3509941).length < 2 ^ (prefixWord ++ tailWord_3509941).sum := by decide
  have hdescent : baseEnd_3509941 < baseStart_3509941 := by decide
  rcases family_descends (prefixWord ++ tailWord_3509941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3509950 : List Nat := [4, 2, 1, 1, 2, 12]
def baseStart_3509950 : Nat := 118140960795 + 3509950 * 2 ^ 59
def prefixEnd_3509950 : Nat := 4983230072969 + 3 ^ 40 * 3509950 * 2
def baseEnd_3509950 : Nat := 14833674265420967392453

theorem tailTrace_3509950 : CollatzResearch.WordTrace tailWord_3509950 prefixEnd_3509950 14833674265420967392453 := by
  unfold tailWord_3509950
  simp only [CollatzResearch.WordTrace]
  refine ⟨16002299204257259572539913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85345595756038717720212869 16002299204257259572539913)
  ·
    refine ⟨12001724403192944679404935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16002299204257259572539913 12001724403192944679404935)
    ·
      refine ⟨18002586604789417019107403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12001724403192944679404935 18002586604789417019107403)
      ·
        refine ⟨27003879907184125528661105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18002586604789417019107403 27003879907184125528661105)
        ·
          refine ⟨20252909930388094146495829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27003879907184125528661105 20252909930388094146495829)
          ·
            refine ⟨14833674265420967392453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 20252909930388094146495829 14833674265420967392453)
            ·
              rfl

theorem cell22_3509950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 12].length) (baseStart_3509950 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3509950 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3509950 prefixEnd_3509950 := by exact prefixLift 3509950
  have htrace : WordTrace (prefixWord ++ tailWord_3509950) baseStart_3509950 baseEnd_3509950 := by
    simpa [prefixWord, tailWord_3509950, baseEnd_3509950] using wordTrace_append hprefix tailTrace_3509950
  have hstable : (prefixWord ++ tailWord_3509950).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3509950).length < 2 ^ (prefixWord ++ tailWord_3509950).sum := by decide
  have hdescent : baseEnd_3509950 < baseStart_3509950 := by decide
  rcases family_descends (prefixWord ++ tailWord_3509950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3510022 : List Nat := [6, 2, 2, 1, 1, 2, 1, 1, 1, 5]
def baseStart_3510022 : Nat := 118140960795 + 3510022 * 2 ^ 59
def prefixEnd_3510022 : Nat := 4983230072969 + 3 ^ 40 * 3510022 * 2
def baseEnd_3510022 : Nat := 1201552262570514170988473

theorem tailTrace_3510022 : CollatzResearch.WordTrace tailWord_3510022 prefixEnd_3510022 1201552262570514170988473 := by
  unfold tailWord_3510022
  simp only [CollatzResearch.WordTrace]
  refine ⟨4000656865306163527404385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 85347346459864821917960213 4000656865306163527404385)
  ·
    refine ⟨3000492648979622645553289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4000656865306163527404385 3000492648979622645553289)
    ·
      refine ⟨2250369486734716984164967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3000492648979622645553289 2250369486734716984164967)
      ·
        refine ⟨3375554230102075476247451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2250369486734716984164967 3375554230102075476247451)
        ·
          refine ⟨5063331345153113214371177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3375554230102075476247451 5063331345153113214371177)
          ·
            refine ⟨3797498508864834910778383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5063331345153113214371177 3797498508864834910778383)
            ·
              refine ⟨5696247763297252366167575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3797498508864834910778383 5696247763297252366167575)
              ·
                refine ⟨8544371644945878549251363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5696247763297252366167575 8544371644945878549251363)
                ·
                  refine ⟨12816557467418817823877045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8544371644945878549251363 12816557467418817823877045)
                  ·
                    refine ⟨1201552262570514170988473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12816557467418817823877045 1201552262570514170988473)
                    ·
                      rfl

theorem cell22_3510022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_3510022 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3510022 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3510022 prefixEnd_3510022 := by exact prefixLift 3510022
  have htrace : WordTrace (prefixWord ++ tailWord_3510022) baseStart_3510022 baseEnd_3510022 := by
    simpa [prefixWord, tailWord_3510022, baseEnd_3510022] using wordTrace_append hprefix tailTrace_3510022
  have hstable : (prefixWord ++ tailWord_3510022).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3510022).length < 2 ^ (prefixWord ++ tailWord_3510022).sum := by decide
  have hdescent : baseEnd_3510022 < baseStart_3510022 := by decide
  rcases family_descends (prefixWord ++ tailWord_3510022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3510074 : List Nat := [3, 1, 1, 1, 5, 3, 1, 1, 6]
def baseStart_3510074 : Nat := 118140960795 + 3510074 * 2 ^ 59
def prefixEnd_3510074 : Nat := 4983230072969 + 3 ^ 40 * 3510074 * 2
def baseEnd_3510074 : Nat := 400523354411067789562771

theorem tailTrace_3510074 : CollatzResearch.WordTrace tailWord_3510074 prefixEnd_3510074 400523354411067789562771 := by
  unfold tailWord_3510074
  simp only [CollatzResearch.WordTrace]
  refine ⟨32005729071402211439458319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85348610857072563838555517 32005729071402211439458319)
  ·
    refine ⟨48008593607103317159187479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32005729071402211439458319 48008593607103317159187479)
    ·
      refine ⟨72012890410654975738781219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48008593607103317159187479 72012890410654975738781219)
      ·
        refine ⟨108019335615982463608171829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72012890410654975738781219 108019335615982463608171829)
        ·
          refine ⟨10126812713998355963266109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 108019335615982463608171829 10126812713998355963266109)
          ·
            refine ⟨3797554767749383486224791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10126812713998355963266109 3797554767749383486224791)
            ·
              refine ⟨5696332151624075229337187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3797554767749383486224791 5696332151624075229337187)
              ·
                refine ⟨8544498227436112844005781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5696332151624075229337187 8544498227436112844005781)
                ·
                  refine ⟨400523354411067789562771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8544498227436112844005781 400523354411067789562771)
                  ·
                    rfl

theorem cell22_3510074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 1, 1, 6].length) (baseStart_3510074 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3510074 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3510074 prefixEnd_3510074 := by exact prefixLift 3510074
  have htrace : WordTrace (prefixWord ++ tailWord_3510074) baseStart_3510074 baseEnd_3510074 := by
    simpa [prefixWord, tailWord_3510074, baseEnd_3510074] using wordTrace_append hprefix tailTrace_3510074
  have hstable : (prefixWord ++ tailWord_3510074).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3510074).length < 2 ^ (prefixWord ++ tailWord_3510074).sum := by decide
  have hdescent : baseEnd_3510074 < baseStart_3510074 := by decide
  rcases family_descends (prefixWord ++ tailWord_3510074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3510089 : List Nat := [1, 2, 1, 1, 2, 4, 3, 3, 2, 3]
def baseStart_3510089 : Nat := 118140960795 + 3510089 * 2 ^ 59
def prefixEnd_3510089 : Nat := 4983230072969 + 3 ^ 40 * 3510089 * 2
def baseEnd_3510089 : Nat := 1201575198039748329563267

theorem tailTrace_3510089 : CollatzResearch.WordTrace tailWord_3510089 prefixEnd_3510089 1201575198039748329563267 := by
  unfold tailWord_3510089
  simp only [CollatzResearch.WordTrace]
  refine ⟨128023463380554503319629321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85348975587036335546419547 128023463380554503319629321)
  ·
    refine ⟨96017597535415877489721991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128023463380554503319629321 96017597535415877489721991)
    ·
      refine ⟨144026396303123816234582987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96017597535415877489721991 144026396303123816234582987)
      ·
        refine ⟨216039594454685724351874481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144026396303123816234582987 216039594454685724351874481)
        ·
          refine ⟨162029695841014293263905861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 216039594454685724351874481 162029695841014293263905861)
          ·
            refine ⟨30380567970190179986982349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 162029695841014293263905861 30380567970190179986982349)
            ·
              refine ⟨11392712988821317495118381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30380567970190179986982349 11392712988821317495118381)
              ·
                refine ⟨4272267370807994060669393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11392712988821317495118381 4272267370807994060669393)
                ·
                  refine ⟨3204200528105995545502045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4272267370807994060669393 3204200528105995545502045)
                  ·
                    refine ⟨1201575198039748329563267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3204200528105995545502045 1201575198039748329563267)
                    ·
                      rfl

theorem cell22_3510089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 3, 2, 3].length) (baseStart_3510089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3510089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3510089 prefixEnd_3510089 := by exact prefixLift 3510089
  have htrace : WordTrace (prefixWord ++ tailWord_3510089) baseStart_3510089 baseEnd_3510089 := by
    simpa [prefixWord, tailWord_3510089, baseEnd_3510089] using wordTrace_append hprefix tailTrace_3510089
  have hstable : (prefixWord ++ tailWord_3510089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3510089).length < 2 ^ (prefixWord ++ tailWord_3510089).sum := by decide
  have hdescent : baseEnd_3510089 < baseStart_3510089 := by decide
  rcases family_descends (prefixWord ++ tailWord_3510089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3510093 : List Nat := [1, 6, 1, 2, 1, 3, 1, 2, 1, 4]
def baseStart_3510093 : Nat := 118140960795 + 3510093 * 2 ^ 59
def prefixEnd_3510093 : Nat := 4983230072969 + 3 ^ 40 * 3510093 * 2
def baseEnd_3510093 : Nat := 1201576567321493652463255

theorem tailTrace_3510093 : CollatzResearch.WordTrace tailWord_3510093 prefixEnd_3510093 1201576567321493652463255 := by
  unfold tailWord_3510093
  simp only [CollatzResearch.WordTrace]
  refine ⟨128023609272540012002774933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85349072848360008001849955 128023609272540012002774933)
  ·
    refine ⟨6001106684650313062630075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 128023609272540012002774933 6001106684650313062630075)
    ·
      refine ⟨9001660026975469593945113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6001106684650313062630075 9001660026975469593945113)
      ·
        refine ⟨6751245020231602195458835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9001660026975469593945113 6751245020231602195458835)
        ·
          refine ⟨10126867530347403293188253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6751245020231602195458835 10126867530347403293188253)
          ·
            refine ⟨3797575323880276234945595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10126867530347403293188253 3797575323880276234945595)
            ·
              refine ⟨5696362985820414352418393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3797575323880276234945595 5696362985820414352418393)
              ·
                refine ⟨4272272239365310764313795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5696362985820414352418393 4272272239365310764313795)
                ·
                  refine ⟨6408408359047966146470693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4272272239365310764313795 6408408359047966146470693)
                  ·
                    refine ⟨1201576567321493652463255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6408408359047966146470693 1201576567321493652463255)
                    ·
                      rfl

theorem cell22_3510093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 1, 2, 1, 4].length) (baseStart_3510093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3510093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3510093 prefixEnd_3510093 := by exact prefixLift 3510093
  have htrace : WordTrace (prefixWord ++ tailWord_3510093) baseStart_3510093 baseEnd_3510093 := by
    simpa [prefixWord, tailWord_3510093, baseEnd_3510093] using wordTrace_append hprefix tailTrace_3510093
  have hstable : (prefixWord ++ tailWord_3510093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3510093).length < 2 ^ (prefixWord ++ tailWord_3510093).sum := by decide
  have hdescent : baseEnd_3510093 < baseStart_3510093 := by decide
  rcases family_descends (prefixWord ++ tailWord_3510093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3510151 : List Nat := [1, 1, 4, 2, 4, 1, 1, 2, 3, 3]
def baseStart_3510151 : Nat := 118140960795 + 3510151 * 2 ^ 59
def prefixEnd_3510151 : Nat := 4983230072969 + 3 ^ 40 * 3510151 * 2
def baseEnd_3510151 : Nat := 1201596421906800834513077

theorem tailTrace_3510151 : CollatzResearch.WordTrace tailWord_3510151 prefixEnd_3510151 1201596421906800834513077 := by
  unfold tailWord_3510151
  simp only [CollatzResearch.WordTrace]
  refine ⟨128025724706329887908386307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85350483137553258605590871 128025724706329887908386307)
  ·
    refine ⟨192038587059494831862579461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128025724706329887908386307 192038587059494831862579461)
    ·
      refine ⟨36007235073655280974233649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 192038587059494831862579461 36007235073655280974233649)
      ·
        refine ⟨27005426305241460730675237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36007235073655280974233649 27005426305241460730675237)
        ·
          refine ⟨5063517432232773887001607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27005426305241460730675237 5063517432232773887001607)
          ·
            refine ⟨7595276148349160830502411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5063517432232773887001607 7595276148349160830502411)
            ·
              refine ⟨11392914222523741245753617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7595276148349160830502411 11392914222523741245753617)
              ·
                refine ⟨8544685666892805934315213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11392914222523741245753617 8544685666892805934315213)
                ·
                  refine ⟨3204257125084802225368205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8544685666892805934315213 3204257125084802225368205)
                  ·
                    refine ⟨1201596421906800834513077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3204257125084802225368205 1201596421906800834513077)
                    ·
                      rfl

theorem cell22_3510151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 2, 3, 3].length) (baseStart_3510151 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3510151 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3510151 prefixEnd_3510151 := by exact prefixLift 3510151
  have htrace : WordTrace (prefixWord ++ tailWord_3510151) baseStart_3510151 baseEnd_3510151 := by
    simpa [prefixWord, tailWord_3510151, baseEnd_3510151] using wordTrace_append hprefix tailTrace_3510151
  have hstable : (prefixWord ++ tailWord_3510151).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3510151).length < 2 ^ (prefixWord ++ tailWord_3510151).sum := by decide
  have hdescent : baseEnd_3510151 < baseStart_3510151 := by decide
  rcases family_descends (prefixWord ++ tailWord_3510151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3510224 : List Nat := [2, 1, 1, 1, 1, 2, 5, 2, 4, 3]
def baseStart_3510224 : Nat := 118140960795 + 3510224 * 2 ^ 59
def prefixEnd_3510224 : Nat := 4983230072969 + 3 ^ 40 * 3510224 * 2
def baseEnd_3510224 : Nat := 1201621411298652977437853

theorem tailTrace_3510224 : CollatzResearch.WordTrace tailWord_3510224 prefixEnd_3510224 1201621411298652977437853 := by
  unfold tailWord_3510224
  simp only [CollatzResearch.WordTrace]
  refine ⟨64014193617532710687896863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85352258156710280917195817 64014193617532710687896863)
  ·
    refine ⟨96021290426299066031845295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64014193617532710687896863 96021290426299066031845295)
    ·
      refine ⟨144031935639448599047767943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96021290426299066031845295 144031935639448599047767943)
      ·
        refine ⟨216047903459172898571651915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144031935639448599047767943 216047903459172898571651915)
        ·
          refine ⟨324071855188759347857477873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216047903459172898571651915 324071855188759347857477873)
          ·
            refine ⟨243053891391569510893108405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 324071855188759347857477873 243053891391569510893108405)
            ·
              refine ⟨22786302317959641646228913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 243053891391569510893108405 22786302317959641646228913)
              ·
                refine ⟨17089726738469731234671685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22786302317959641646228913 17089726738469731234671685)
                ·
                  refine ⟨3204323763463074606500941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17089726738469731234671685 3204323763463074606500941)
                  ·
                    refine ⟨1201621411298652977437853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3204323763463074606500941 1201621411298652977437853)
                    ·
                      rfl

theorem cell22_3510224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 2, 4, 3].length) (baseStart_3510224 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3510224 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3510224 prefixEnd_3510224 := by exact prefixLift 3510224
  have htrace : WordTrace (prefixWord ++ tailWord_3510224) baseStart_3510224 baseEnd_3510224 := by
    simpa [prefixWord, tailWord_3510224, baseEnd_3510224] using wordTrace_append hprefix tailTrace_3510224
  have hstable : (prefixWord ++ tailWord_3510224).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3510224).length < 2 ^ (prefixWord ++ tailWord_3510224).sum := by decide
  have hdescent : baseEnd_3510224 < baseStart_3510224 := by decide
  rcases family_descends (prefixWord ++ tailWord_3510224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3510239 : List Nat := [1, 1, 2, 3, 4, 1, 1, 1, 4, 4]
def baseStart_3510239 : Nat := 118140960795 + 3510239 * 2 ^ 59
def prefixEnd_3510239 : Nat := 4983230072969 + 3 ^ 40 * 3510239 * 2
def baseEnd_3510239 : Nat := 1201626546105197938312807

theorem tailTrace_3510239 : CollatzResearch.WordTrace tailWord_3510239 prefixEnd_3510239 1201626546105197938312807 := by
  unfold tailWord_3510239
  simp only [CollatzResearch.WordTrace]
  refine ⟨128028934330011078937589771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85352622886674052625059847 128028934330011078937589771)
  ·
    refine ⟨192043401495016618406384657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128028934330011078937589771 192043401495016618406384657)
    ·
      refine ⟨144032551121262463804788493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192043401495016618406384657 144032551121262463804788493)
      ·
        refine ⟨54012206670473423926795685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144032551121262463804788493 54012206670473423926795685)
        ·
          refine ⟨10127288750713766986274191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54012206670473423926795685 10127288750713766986274191)
          ·
            refine ⟨15190933126070650479411287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10127288750713766986274191 15190933126070650479411287)
            ·
              refine ⟨22786399689105975719116931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15190933126070650479411287 22786399689105975719116931)
              ·
                refine ⟨34179599533658963578675397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22786399689105975719116931 34179599533658963578675397)
                ·
                  refine ⟨6408674912561055671001637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34179599533658963578675397 6408674912561055671001637)
                  ·
                    refine ⟨1201626546105197938312807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6408674912561055671001637 1201626546105197938312807)
                    ·
                      rfl

theorem cell22_3510239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 1, 4, 4].length) (baseStart_3510239 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3510239 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3510239 prefixEnd_3510239 := by exact prefixLift 3510239
  have htrace : WordTrace (prefixWord ++ tailWord_3510239) baseStart_3510239 baseEnd_3510239 := by
    simpa [prefixWord, tailWord_3510239, baseEnd_3510239] using wordTrace_append hprefix tailTrace_3510239
  have hstable : (prefixWord ++ tailWord_3510239).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3510239).length < 2 ^ (prefixWord ++ tailWord_3510239).sum := by decide
  have hdescent : baseEnd_3510239 < baseStart_3510239 := by decide
  rcases family_descends (prefixWord ++ tailWord_3510239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3510243 : List Nat := [1, 1, 1, 6, 1, 3, 3, 2, 4]
def baseStart_3510243 : Nat := 118140960795 + 3510243 * 2 ^ 59
def prefixEnd_3510243 : Nat := 4983230072969 + 3 ^ 40 * 3510243 * 2
def baseEnd_3510243 : Nat := 400542638462314420404265

theorem tailTrace_3510243 : CollatzResearch.WordTrace tailWord_3510243 prefixEnd_3510243 400542638462314420404265 := by
  unfold tailWord_3510243
  simp only [CollatzResearch.WordTrace]
  refine ⟨128029080221996587620735383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85352720147997725080490255 128029080221996587620735383)
  ·
    refine ⟨192043620332994881431103075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128029080221996587620735383 192043620332994881431103075)
    ·
      refine ⟨288065430499492322146654613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192043620332994881431103075 288065430499492322146654613)
      ·
        refine ⟨13503067054663702600624435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 288065430499492322146654613 13503067054663702600624435)
        ·
          refine ⟨20254600581995553900936653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13503067054663702600624435 20254600581995553900936653)
          ·
            refine ⟨7595475218248332712851245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20254600581995553900936653 7595475218248332712851245)
            ·
              refine ⟨2848303206843124767319217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7595475218248332712851245 2848303206843124767319217)
              ·
                refine ⟨2136227405132343575489413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2848303206843124767319217 2136227405132343575489413)
                ·
                  refine ⟨400542638462314420404265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2136227405132343575489413 400542638462314420404265)
                  ·
                    rfl

theorem cell22_3510243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 3, 2, 4].length) (baseStart_3510243 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3510243 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3510243 prefixEnd_3510243 := by exact prefixLift 3510243
  have htrace : WordTrace (prefixWord ++ tailWord_3510243) baseStart_3510243 baseEnd_3510243 := by
    simpa [prefixWord, tailWord_3510243, baseEnd_3510243] using wordTrace_append hprefix tailTrace_3510243
  have hstable : (prefixWord ++ tailWord_3510243).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3510243).length < 2 ^ (prefixWord ++ tailWord_3510243).sum := by decide
  have hdescent : baseEnd_3510243 < baseStart_3510243 := by decide
  rcases family_descends (prefixWord ++ tailWord_3510243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3510254 : List Nat := [4, 1, 2, 1, 3, 1, 1, 9]
def baseStart_3510254 : Nat := 118140960795 + 3510254 * 2 ^ 59
def prefixEnd_3510254 : Nat := 4983230072969 + 3 ^ 40 * 3510254 * 2
def baseEnd_3510254 : Nat := 133514631212415877687529

theorem tailTrace_3510254 : CollatzResearch.WordTrace tailWord_3510254 prefixEnd_3510254 133514631212415877687529 := by
  unfold tailWord_3510254
  simp only [CollatzResearch.WordTrace]
  refine ⟨16003685178119592062423227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85352987616637824332923877 16003685178119592062423227)
  ·
    refine ⟨24005527767179388093634841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16003685178119592062423227 24005527767179388093634841)
    ·
      refine ⟨18004145825384541070226131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24005527767179388093634841 18004145825384541070226131)
      ·
        refine ⟨27006218738076811605339197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18004145825384541070226131 27006218738076811605339197)
        ·
          refine ⟨10127332026778804352002199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27006218738076811605339197 10127332026778804352002199)
          ·
            refine ⟨15190998040168206528003299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10127332026778804352002199 15190998040168206528003299)
            ·
              refine ⟨22786497060252309792004949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15190998040168206528003299 22786497060252309792004949)
              ·
                refine ⟨133514631212415877687529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 22786497060252309792004949 133514631212415877687529)
                ·
                  rfl

theorem cell22_3510254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 9].length) (baseStart_3510254 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3510254 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3510254 prefixEnd_3510254 := by exact prefixLift 3510254
  have htrace : WordTrace (prefixWord ++ tailWord_3510254) baseStart_3510254 baseEnd_3510254 := by
    simpa [prefixWord, tailWord_3510254, baseEnd_3510254] using wordTrace_append hprefix tailTrace_3510254
  have hstable : (prefixWord ++ tailWord_3510254).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3510254).length < 2 ^ (prefixWord ++ tailWord_3510254).sum := by decide
  have hdescent : baseEnd_3510254 < baseStart_3510254 := by decide
  rcases family_descends (prefixWord ++ tailWord_3510254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3510292 : List Nat := [2, 4, 3, 2, 1, 1, 2, 2, 2, 3]
def baseStart_3510292 : Nat := 118140960795 + 3510292 * 2 ^ 59
def prefixEnd_3510292 : Nat := 4983230072969 + 3 ^ 40 * 3510292 * 2
def baseEnd_3510292 : Nat := 1201644689088323466737645

theorem tailTrace_3510292 : CollatzResearch.WordTrace tailWord_3510292 prefixEnd_3510292 1201644689088323466737645 := by
  unfold tailWord_3510292
  simp only [CollatzResearch.WordTrace]
  refine ⟨64015433699409534494634565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85353911599212712659512753 64015433699409534494634565)
  ·
    refine ⟨12002893818639287717743981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64015433699409534494634565 12002893818639287717743981)
    ·
      refine ⟨4501085181989732894153993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12002893818639287717743981 4501085181989732894153993)
      ·
        refine ⟨3375813886492299670615495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4501085181989732894153993 3375813886492299670615495)
        ·
          refine ⟨5063720829738449505923243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3375813886492299670615495 5063720829738449505923243)
          ·
            refine ⟨7595581244607674258884865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5063720829738449505923243 7595581244607674258884865)
            ·
              refine ⟨5696685933455755694163649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7595581244607674258884865 5696685933455755694163649)
              ·
                refine ⟨4272514450091816770622737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5696685933455755694163649 4272514450091816770622737)
                ·
                  refine ⟨3204385837568862577967053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4272514450091816770622737 3204385837568862577967053)
                  ·
                    refine ⟨1201644689088323466737645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3204385837568862577967053 1201644689088323466737645)
                    ·
                      rfl

theorem cell22_3510292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 2, 2, 2, 3].length) (baseStart_3510292 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3510292 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3510292 prefixEnd_3510292 := by exact prefixLift 3510292
  have htrace : WordTrace (prefixWord ++ tailWord_3510292) baseStart_3510292 baseEnd_3510292 := by
    simpa [prefixWord, tailWord_3510292, baseEnd_3510292] using wordTrace_append hprefix tailTrace_3510292
  have hstable : (prefixWord ++ tailWord_3510292).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3510292).length < 2 ^ (prefixWord ++ tailWord_3510292).sum := by decide
  have hdescent : baseEnd_3510292 < baseStart_3510292 := by decide
  rcases family_descends (prefixWord ++ tailWord_3510292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3510303 : List Nat := [1, 1, 2, 4, 1, 2, 3, 4, 1, 3]
def baseStart_3510303 : Nat := 118140960795 + 3510303 * 2 ^ 59
def prefixEnd_3510303 : Nat := 4983230072969 + 3 ^ 40 * 3510303 * 2
def baseEnd_3510303 : Nat := 1201648454613123104712611

theorem tailTrace_3510303 : CollatzResearch.WordTrace tailWord_3510303 prefixEnd_3510303 1201648454613123104712611 := by
  unfold tailWord_3510303
  simp only [CollatzResearch.WordTrace]
  refine ⟨128031268601779217867919563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85354179067852811911946375 128031268601779217867919563)
  ·
    refine ⟨192046902902668826801879345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128031268601779217867919563 192046902902668826801879345)
    ·
      refine ⟨144035177177001620101409509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192046902902668826801879345 144035177177001620101409509)
      ·
        refine ⟨27006595720687803769014283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 144035177177001620101409509 27006595720687803769014283)
        ·
          refine ⟨40509893581031705653521425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27006595720687803769014283 40509893581031705653521425)
          ·
            refine ⟨30382420185773779240141069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40509893581031705653521425 30382420185773779240141069)
            ·
              refine ⟨11393407569665167215052901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30382420185773779240141069 11393407569665167215052901)
              ·
                refine ⟨2136263919312218852822419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11393407569665167215052901 2136263919312218852822419)
                ·
                  refine ⟨3204395878968328279233629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2136263919312218852822419 3204395878968328279233629)
                  ·
                    refine ⟨1201648454613123104712611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3204395878968328279233629 1201648454613123104712611)
                    ·
                      rfl

theorem cell22_3510303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 4, 1, 3].length) (baseStart_3510303 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3510303 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3510303 prefixEnd_3510303 := by exact prefixLift 3510303
  have htrace : WordTrace (prefixWord ++ tailWord_3510303) baseStart_3510303 baseEnd_3510303 := by
    simpa [prefixWord, tailWord_3510303, baseEnd_3510303] using wordTrace_append hprefix tailTrace_3510303
  have hstable : (prefixWord ++ tailWord_3510303).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3510303).length < 2 ^ (prefixWord ++ tailWord_3510303).sum := by decide
  have hdescent : baseEnd_3510303 < baseStart_3510303 := by decide
  rcases family_descends (prefixWord ++ tailWord_3510303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3510359 : List Nat := [1, 1, 3, 2, 2, 1, 2, 2, 3, 5]
def baseStart_3510359 : Nat := 118140960795 + 3510359 * 2 ^ 59
def prefixEnd_3510359 : Nat := 4983230072969 + 3 ^ 40 * 3510359 * 2
def baseEnd_3510359 : Nat := 1201667624557557625312439

theorem tailTrace_3510359 : CollatzResearch.WordTrace tailWord_3510359 prefixEnd_3510359 1201667624557557625312439 := by
  unfold tailWord_3510359
  simp only [CollatzResearch.WordTrace]
  refine ⟨128033311089576339431958131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85355540726384226287972087 128033311089576339431958131)
  ·
    refine ⟨192049966634364509147937197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128033311089576339431958131 192049966634364509147937197)
    ·
      refine ⟨72018737487886690930476449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 192049966634364509147937197 72018737487886690930476449)
      ·
        refine ⟨54014053115915018197857337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72018737487886690930476449 54014053115915018197857337)
        ·
          refine ⟨40510539836936263648393003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54014053115915018197857337 40510539836936263648393003)
          ·
            refine ⟨60765809755404395472589505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40510539836936263648393003 60765809755404395472589505)
            ·
              refine ⟨45574357316553296604442129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60765809755404395472589505 45574357316553296604442129)
              ·
                refine ⟨34180767987414972453331597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45574357316553296604442129 34180767987414972453331597)
                ·
                  refine ⟨12817787995280614669999349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34180767987414972453331597 12817787995280614669999349)
                  ·
                    refine ⟨1201667624557557625312439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12817787995280614669999349 1201667624557557625312439)
                    ·
                      rfl

theorem cell22_3510359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 2, 3, 5].length) (baseStart_3510359 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3510359 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3510359 prefixEnd_3510359 := by exact prefixLift 3510359
  have htrace : WordTrace (prefixWord ++ tailWord_3510359) baseStart_3510359 baseEnd_3510359 := by
    simpa [prefixWord, tailWord_3510359, baseEnd_3510359] using wordTrace_append hprefix tailTrace_3510359
  have hstable : (prefixWord ++ tailWord_3510359).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3510359).length < 2 ^ (prefixWord ++ tailWord_3510359).sum := by decide
  have hdescent : baseEnd_3510359 < baseStart_3510359 := by decide
  rcases family_descends (prefixWord ++ tailWord_3510359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3510361 : List Nat := [1, 2, 1, 2, 2, 1, 3, 6, 4]
def baseStart_3510361 : Nat := 118140960795 + 3510361 * 2 ^ 59
def prefixEnd_3510361 : Nat := 4983230072969 + 3 ^ 40 * 3510361 * 2
def baseEnd_3510361 : Nat := 400556103066143428920811

theorem tailTrace_3510361 : CollatzResearch.WordTrace tailWord_3510361 prefixEnd_3510361 400556103066143428920811 := by
  unfold tailWord_3510361
  simp only [CollatzResearch.WordTrace]
  refine ⟨128033384035569093773530937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85355589357046062515687291 128033384035569093773530937)
  ·
    refine ⟨96025038026676820330148203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128033384035569093773530937 96025038026676820330148203)
    ·
      refine ⟨144037557040015230495222305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96025038026676820330148203 144037557040015230495222305)
      ·
        refine ⟨108028167780011422871416729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144037557040015230495222305 108028167780011422871416729)
        ·
          refine ⟨81021125835008567153562547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108028167780011422871416729 81021125835008567153562547)
          ·
            refine ⟨121531688752512850730343821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81021125835008567153562547 121531688752512850730343821)
            ·
              refine ⟨45574383282192319023878933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 121531688752512850730343821 45574383282192319023878933)
              ·
                refine ⟨2136299216352764954244325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 45574383282192319023878933 2136299216352764954244325)
                ·
                  refine ⟨400556103066143428920811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2136299216352764954244325 400556103066143428920811)
                  ·
                    rfl

theorem cell22_3510361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 6, 4].length) (baseStart_3510361 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3510361 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3510361 prefixEnd_3510361 := by exact prefixLift 3510361
  have htrace : WordTrace (prefixWord ++ tailWord_3510361) baseStart_3510361 baseEnd_3510361 := by
    simpa [prefixWord, tailWord_3510361, baseEnd_3510361] using wordTrace_append hprefix tailTrace_3510361
  have hstable : (prefixWord ++ tailWord_3510361).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3510361).length < 2 ^ (prefixWord ++ tailWord_3510361).sum := by decide
  have hdescent : baseEnd_3510361 < baseStart_3510361 := by decide
  rcases family_descends (prefixWord ++ tailWord_3510361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3510408 : List Nat := [2, 1, 3, 4, 1, 2, 1, 2, 2, 4]
def baseStart_3510408 : Nat := 118140960795 + 3510408 * 2 ^ 59
def prefixEnd_3510408 : Nat := 4983230072969 + 3 ^ 40 * 3510408 * 2
def baseEnd_3510408 : Nat := 1201684398258937830837289

theorem tailTrace_3510408 : CollatzResearch.WordTrace tailWord_3510408 prefixEnd_3510408 1201684398258937830837289 := by
  unfold tailWord_3510408
  simp only [CollatzResearch.WordTrace]
  refine ⟨64017549133199410400245939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85356732177599213866994585 64017549133199410400245939)
  ·
    refine ⟨96026323699799115600368909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64017549133199410400245939 96026323699799115600368909)
    ·
      refine ⟨36009871387424668350138341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96026323699799115600368909 36009871387424668350138341)
      ·
        refine ⟨6751850885142125315650939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36009871387424668350138341 6751850885142125315650939)
        ·
          refine ⟨10127776327713187973476409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6751850885142125315650939 10127776327713187973476409)
          ·
            refine ⟨7595832245784890980107307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10127776327713187973476409 7595832245784890980107307)
            ·
              refine ⟨11393748368677336470160961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7595832245784890980107307 11393748368677336470160961)
              ·
                refine ⟨8545311276508002352620721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11393748368677336470160961 8545311276508002352620721)
                ·
                  refine ⟨6408983457381001764465541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8545311276508002352620721 6408983457381001764465541)
                  ·
                    refine ⟨1201684398258937830837289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6408983457381001764465541 1201684398258937830837289)
                    ·
                      rfl

theorem cell22_3510408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 2, 2, 4].length) (baseStart_3510408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3510408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3510408 prefixEnd_3510408 := by exact prefixLift 3510408
  have htrace : WordTrace (prefixWord ++ tailWord_3510408) baseStart_3510408 baseEnd_3510408 := by
    simpa [prefixWord, tailWord_3510408, baseEnd_3510408] using wordTrace_append hprefix tailTrace_3510408
  have hstable : (prefixWord ++ tailWord_3510408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3510408).length < 2 ^ (prefixWord ++ tailWord_3510408).sum := by decide
  have hdescent : baseEnd_3510408 < baseStart_3510408 := by decide
  rcases family_descends (prefixWord ++ tailWord_3510408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3510419 : List Nat := [1, 1, 1, 2, 1, 2, 3, 3, 2, 6]
def baseStart_3510419 : Nat := 118140960795 + 3510419 * 2 ^ 59
def prefixEnd_3510419 : Nat := 4983230072969 + 3 ^ 40 * 3510419 * 2
def baseEnd_3510419 : Nat := 1201688163783737468812255

theorem tailTrace_3510419 : CollatzResearch.WordTrace tailWord_3510419 prefixEnd_3510419 1201688163783737468812255 := by
  unfold tailWord_3510419
  simp only [CollatzResearch.WordTrace]
  refine ⟨128035499469358969679142311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85356999646239313119428207 128035499469358969679142311)
  ·
    refine ⟨192053249204038454518713467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128035499469358969679142311 192053249204038454518713467)
    ·
      refine ⟨288079873806057681778070201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192053249204038454518713467 288079873806057681778070201)
      ·
        refine ⟨216059905354543261333552651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 288079873806057681778070201 216059905354543261333552651)
        ·
          refine ⟨324089858031814892000328977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216059905354543261333552651 324089858031814892000328977)
          ·
            refine ⟨243067393523861169000246733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 324089858031814892000328977 243067393523861169000246733)
            ·
              refine ⟨91150272571447938375092525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 243067393523861169000246733 91150272571447938375092525)
              ·
                refine ⟨34181352214292976890659697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91150272571447938375092525 34181352214292976890659697)
                ·
                  refine ⟨25636014160719732667994773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34181352214292976890659697 25636014160719732667994773)
                  ·
                    refine ⟨1201688163783737468812255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25636014160719732667994773 1201688163783737468812255)
                    ·
                      rfl

theorem cell22_3510419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 3, 2, 6].length) (baseStart_3510419 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3510419 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3510419 prefixEnd_3510419 := by exact prefixLift 3510419
  have htrace : WordTrace (prefixWord ++ tailWord_3510419) baseStart_3510419 baseEnd_3510419 := by
    simpa [prefixWord, tailWord_3510419, baseEnd_3510419] using wordTrace_append hprefix tailTrace_3510419
  have hstable : (prefixWord ++ tailWord_3510419).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3510419).length < 2 ^ (prefixWord ++ tailWord_3510419).sum := by decide
  have hdescent : baseEnd_3510419 < baseStart_3510419 := by decide
  rcases family_descends (prefixWord ++ tailWord_3510419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3510468 : List Nat := [2, 3, 3, 1, 2, 1, 1, 4, 5]
def baseStart_3510468 : Nat := 118140960795 + 3510468 * 2 ^ 59
def prefixEnd_3510468 : Nat := 4983230072969 + 3 ^ 40 * 3510468 * 2
def baseEnd_3510468 : Nat := 400568312495039224779035

theorem tailTrace_3510468 : CollatzResearch.WordTrace tailWord_3510468 prefixEnd_3510468 400568312495039224779035 := by
  unfold tailWord_3510468
  simp only [CollatzResearch.WordTrace]
  refine ⟨64018643323090725523838029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85358191097454300698450705 64018643323090725523838029)
  ·
    refine ⟨24006991246159022071439261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64018643323090725523838029 24006991246159022071439261)
    ·
      refine ⟨9002621717309633276789723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24006991246159022071439261 9002621717309633276789723)
      ·
        refine ⟨13503932575964449915184585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9002621717309633276789723 13503932575964449915184585)
        ·
          refine ⟨10127949431973337436388439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13503932575964449915184585 10127949431973337436388439)
          ·
            refine ⟨15191924147960006154582659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10127949431973337436388439 15191924147960006154582659)
            ·
              refine ⟨22787886221940009231873989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15191924147960006154582659 22787886221940009231873989)
              ·
                refine ⟨4272728666613751730976373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22787886221940009231873989 4272728666613751730976373)
                ·
                  refine ⟨400568312495039224779035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4272728666613751730976373 400568312495039224779035)
                  ·
                    rfl

theorem cell22_3510468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 4, 5].length) (baseStart_3510468 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3510468 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3510468 prefixEnd_3510468 := by exact prefixLift 3510468
  have htrace : WordTrace (prefixWord ++ tailWord_3510468) baseStart_3510468 baseEnd_3510468 := by
    simpa [prefixWord, tailWord_3510468, baseEnd_3510468] using wordTrace_append hprefix tailTrace_3510468
  have hstable : (prefixWord ++ tailWord_3510468).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3510468).length < 2 ^ (prefixWord ++ tailWord_3510468).sum := by decide
  have hdescent : baseEnd_3510468 < baseStart_3510468 := by decide
  rcases family_descends (prefixWord ++ tailWord_3510468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3510481 : List Nat := [1, 2, 2, 1, 2, 2, 3, 2, 3, 4]
def baseStart_3510481 : Nat := 118140960795 + 3510481 * 2 ^ 59
def prefixEnd_3510481 : Nat := 4983230072969 + 3 ^ 40 * 3510481 * 2
def baseEnd_3510481 : Nat := 1201709387650789973762065

theorem tailTrace_3510481 : CollatzResearch.WordTrace tailWord_3510481 prefixEnd_3510481 1201709387650789973762065 := by
  unfold tailWord_3510481
  simp only [CollatzResearch.WordTrace]
  refine ⟨128037760795134354267899297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85358507196756236178599531 128037760795134354267899297)
  ·
    refine ⟨96028320596350765700924473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128037760795134354267899297 96028320596350765700924473)
    ·
      refine ⟨72021240447263074275693355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96028320596350765700924473 72021240447263074275693355)
      ·
        refine ⟨108031860670894611413540033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72021240447263074275693355 108031860670894611413540033)
        ·
          refine ⟨81023895503170958560155025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108031860670894611413540033 81023895503170958560155025)
          ·
            refine ⟨60767921627378218920116269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81023895503170958560155025 60767921627378218920116269)
            ·
              refine ⟨22787970610266832095043601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60767921627378218920116269 22787970610266832095043601)
              ·
                refine ⟨17090977957700124071282701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22787970610266832095043601 17090977957700124071282701)
                ·
                  refine ⟨6409116734137546526731013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17090977957700124071282701 6409116734137546526731013)
                  ·
                    refine ⟨1201709387650789973762065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6409116734137546526731013 1201709387650789973762065)
                    ·
                      rfl

theorem cell22_3510481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 2, 3, 4].length) (baseStart_3510481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3510481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3510481 prefixEnd_3510481 := by exact prefixLift 3510481
  have htrace : WordTrace (prefixWord ++ tailWord_3510481) baseStart_3510481 baseEnd_3510481 := by
    simpa [prefixWord, tailWord_3510481, baseEnd_3510481] using wordTrace_append hprefix tailTrace_3510481
  have hstable : (prefixWord ++ tailWord_3510481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3510481).length < 2 ^ (prefixWord ++ tailWord_3510481).sum := by decide
  have hdescent : baseEnd_3510481 < baseStart_3510481 := by decide
  rcases family_descends (prefixWord ++ tailWord_3510481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3510496 : List Nat := [2, 1, 1, 3, 1, 3, 3, 2, 6]
def baseStart_3510496 : Nat := 118140960795 + 3510496 * 2 ^ 59
def prefixEnd_3510496 : Nat := 4983230072969 + 3 ^ 40 * 3510496 * 2
def baseEnd_3510496 : Nat := 400571507485778311545673

theorem tailTrace_3510496 : CollatzResearch.WordTrace tailWord_3510496 prefixEnd_3510496 400571507485778311545673 := by
  unfold tailWord_3510496
  simp only [CollatzResearch.WordTrace]
  refine ⟨64019153945040005914847671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85358871926720007886463561 64019153945040005914847671)
  ·
    refine ⟨96028730917560008872271507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64019153945040005914847671 96028730917560008872271507)
    ·
      refine ⟨144043096376340013308407261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96028730917560008872271507 144043096376340013308407261)
      ·
        refine ⟨54016161141127504990652723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144043096376340013308407261 54016161141127504990652723)
        ·
          refine ⟨81024241711691257485979085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54016161141127504990652723 81024241711691257485979085)
          ·
            refine ⟨30384090641884221557242157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81024241711691257485979085 30384090641884221557242157)
            ·
              refine ⟨11394033990706583083965809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30384090641884221557242157 11394033990706583083965809)
              ·
                refine ⟨8545525493029937312974357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11394033990706583083965809 8545525493029937312974357)
                ·
                  refine ⟨400571507485778311545673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8545525493029937312974357 400571507485778311545673)
                  ·
                    rfl

theorem cell22_3510496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 2, 6].length) (baseStart_3510496 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3510496 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3510496 prefixEnd_3510496 := by exact prefixLift 3510496
  have htrace : WordTrace (prefixWord ++ tailWord_3510496) baseStart_3510496 baseEnd_3510496 := by
    simpa [prefixWord, tailWord_3510496, baseEnd_3510496] using wordTrace_append hprefix tailTrace_3510496
  have hstable : (prefixWord ++ tailWord_3510496).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3510496).length < 2 ^ (prefixWord ++ tailWord_3510496).sum := by decide
  have hdescent : baseEnd_3510496 < baseStart_3510496 := by decide
  rcases family_descends (prefixWord ++ tailWord_3510496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3510513 : List Nat := [1, 2, 2, 2, 2, 1, 3, 5, 4]
def baseStart_3510513 : Nat := 118140960795 + 3510513 * 2 ^ 59
def prefixEnd_3510513 : Nat := 4983230072969 + 3 ^ 40 * 3510513 * 2
def baseEnd_3510513 : Nat := 400573447301584185653989

theorem tailTrace_3510513 : CollatzResearch.WordTrace tailWord_3510513 prefixEnd_3510513 400573447301584185653989 := by
  unfold tailWord_3510513
  simp only [CollatzResearch.WordTrace]
  refine ⟨128038927931018423733064193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85359285287345615822042795 128038927931018423733064193)
  ·
    refine ⟨96029195948263817799798145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128038927931018423733064193 96029195948263817799798145)
    ·
      refine ⟨72021896961197863349848609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96029195948263817799798145 72021896961197863349848609)
      ·
        refine ⟨54016422720898397512386457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72021896961197863349848609 54016422720898397512386457)
        ·
          refine ⟨40512317040673798134289843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54016422720898397512386457 40512317040673798134289843)
          ·
            refine ⟨60768475561010697201434765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40512317040673798134289843 60768475561010697201434765)
            ·
              refine ⟨22788178335379011450538037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60768475561010697201434765 22788178335379011450538037)
              ·
                refine ⟨2136391718941782323487941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22788178335379011450538037 2136391718941782323487941)
                ·
                  refine ⟨400573447301584185653989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2136391718941782323487941 400573447301584185653989)
                  ·
                    rfl

theorem cell22_3510513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 5, 4].length) (baseStart_3510513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3510513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3510513 prefixEnd_3510513 := by exact prefixLift 3510513
  have htrace : WordTrace (prefixWord ++ tailWord_3510513) baseStart_3510513 baseEnd_3510513 := by
    simpa [prefixWord, tailWord_3510513, baseEnd_3510513] using wordTrace_append hprefix tailTrace_3510513
  have hstable : (prefixWord ++ tailWord_3510513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3510513).length < 2 ^ (prefixWord ++ tailWord_3510513).sum := by decide
  have hdescent : baseEnd_3510513 < baseStart_3510513 := by decide
  rcases family_descends (prefixWord ++ tailWord_3510513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3510530 : List Nat := [3, 4, 1, 1, 2, 2, 2, 1, 6]
def baseStart_3510530 : Nat := 118140960795 + 3510530 * 2 ^ 59
def prefixEnd_3510530 : Nat := 4983230072969 + 3 ^ 40 * 3510530 * 2
def baseEnd_3510530 : Nat := 400575387117390059762305

theorem tailTrace_3510530 : CollatzResearch.WordTrace tailWord_3510530 prefixEnd_3510530 400575387117390059762305 := by
  unfold tailWord_3510530
  simp only [CollatzResearch.WordTrace]
  refine ⟨32009886992989208909108261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85359698647971223757622029 32009886992989208909108261)
  ·
    refine ⟨6001853811185476670457799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32009886992989208909108261 6001853811185476670457799)
    ·
      refine ⟨9002780716778215005686699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6001853811185476670457799 9002780716778215005686699)
      ·
        refine ⟨13504171075167322508530049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9002780716778215005686699 13504171075167322508530049)
        ·
          refine ⟨10128128306375491881397537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13504171075167322508530049 10128128306375491881397537)
          ·
            refine ⟨7596096229781618911048153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10128128306375491881397537 7596096229781618911048153)
            ·
              refine ⟨5697072172336214183286115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7596096229781618911048153 5697072172336214183286115)
              ·
                refine ⟨8545608258504321274929173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5697072172336214183286115 8545608258504321274929173)
                ·
                  refine ⟨400575387117390059762305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8545608258504321274929173 400575387117390059762305)
                  ·
                    rfl

theorem cell22_3510530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 2, 1, 6].length) (baseStart_3510530 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3510530 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3510530 prefixEnd_3510530 := by exact prefixLift 3510530
  have htrace : WordTrace (prefixWord ++ tailWord_3510530) baseStart_3510530 baseEnd_3510530 := by
    simpa [prefixWord, tailWord_3510530, baseEnd_3510530] using wordTrace_append hprefix tailTrace_3510530
  have hstable : (prefixWord ++ tailWord_3510530).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3510530).length < 2 ^ (prefixWord ++ tailWord_3510530).sum := by decide
  have hdescent : baseEnd_3510530 < baseStart_3510530 := by decide
  rcases family_descends (prefixWord ++ tailWord_3510530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3510556 : List Nat := [2, 2, 3, 1, 1, 1, 1, 1, 1, 9]
def baseStart_3510556 : Nat := 118140960795 + 3510556 * 2 ^ 59
def prefixEnd_3510556 : Nat := 4983230072969 + 3 ^ 40 * 3510556 * 2
def baseEnd_3510556 : Nat := 1201735061683514778136835

theorem tailTrace_3510556 : CollatzResearch.WordTrace tailWord_3510556 prefixEnd_3510556 1201735061683514778136835 := by
  unfold tailWord_3510556
  simp only [CollatzResearch.WordTrace]
  refine ⟨64020248134931321038439761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85360330846575094717919681 64020248134931321038439761)
  ·
    refine ⟨48015186101198490778829821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64020248134931321038439761 48015186101198490778829821)
    ·
      refine ⟨18005694787949434042061183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48015186101198490778829821 18005694787949434042061183)
      ·
        refine ⟨27008542181924151063091775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18005694787949434042061183 27008542181924151063091775)
        ·
          refine ⟨40512813272886226594637663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27008542181924151063091775 40512813272886226594637663)
          ·
            refine ⟨60769219909329339891956495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40512813272886226594637663 60769219909329339891956495)
            ·
              refine ⟨91153829863994009837934743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60769219909329339891956495 91153829863994009837934743)
              ·
                refine ⟨136730744795991014756902115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91153829863994009837934743 136730744795991014756902115)
                ·
                  refine ⟨205096117193986522135353173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 136730744795991014756902115 205096117193986522135353173)
                  ·
                    refine ⟨1201735061683514778136835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 205096117193986522135353173 1201735061683514778136835)
                    ·
                      rfl

theorem cell22_3510556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 1, 1, 9].length) (baseStart_3510556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3510556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3510556 prefixEnd_3510556 := by exact prefixLift 3510556
  have htrace : WordTrace (prefixWord ++ tailWord_3510556) baseStart_3510556 baseEnd_3510556 := by
    simpa [prefixWord, tailWord_3510556, baseEnd_3510556] using wordTrace_append hprefix tailTrace_3510556
  have hstable : (prefixWord ++ tailWord_3510556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3510556).length < 2 ^ (prefixWord ++ tailWord_3510556).sum := by decide
  have hdescent : baseEnd_3510556 < baseStart_3510556 := by decide
  rcases family_descends (prefixWord ++ tailWord_3510556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3510596 : List Nat := [2, 3, 4, 1, 2, 2, 2, 1, 2, 3]
def baseStart_3510596 : Nat := 118140960795 + 3510596 * 2 ^ 59
def prefixEnd_3510596 : Nat := 4983230072969 + 3 ^ 40 * 3510596 * 2
def baseEnd_3510596 : Nat := 1201748754500968007136713

theorem tailTrace_3510596 : CollatzResearch.WordTrace tailWord_3510596 prefixEnd_3510596 1201748754500968007136713 := by
  unfold tailWord_3510596
  simp only [CollatzResearch.WordTrace]
  refine ⟨64020977594858864454167821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85361303459811819272223761 64020977594858864454167821)
  ·
    refine ⟨24007866598072074170312933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64020977594858864454167821 24007866598072074170312933)
    ·
      refine ⟨4501474987138513906933675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24007866598072074170312933 4501474987138513906933675)
      ·
        refine ⟨6752212480707770860400513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4501474987138513906933675 6752212480707770860400513)
        ·
          refine ⟨5064159360530828145300385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6752212480707770860400513 5064159360530828145300385)
          ·
            refine ⟨3798119520398121108975289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5064159360530828145300385 3798119520398121108975289)
            ·
              refine ⟨2848589640298590831731467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3798119520398121108975289 2848589640298590831731467)
              ·
                refine ⟨4272884460447886247597201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2848589640298590831731467 4272884460447886247597201)
                ·
                  refine ⟨3204663345335914685697901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4272884460447886247597201 3204663345335914685697901)
                  ·
                    refine ⟨1201748754500968007136713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3204663345335914685697901 1201748754500968007136713)
                    ·
                      rfl

theorem cell22_3510596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 2, 1, 2, 3].length) (baseStart_3510596 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3510596 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3510596 prefixEnd_3510596 := by exact prefixLift 3510596
  have htrace : WordTrace (prefixWord ++ tailWord_3510596) baseStart_3510596 baseEnd_3510596 := by
    simpa [prefixWord, tailWord_3510596, baseEnd_3510596] using wordTrace_append hprefix tailTrace_3510596
  have hstable : (prefixWord ++ tailWord_3510596).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3510596).length < 2 ^ (prefixWord ++ tailWord_3510596).sum := by decide
  have hdescent : baseEnd_3510596 < baseStart_3510596 := by decide
  rcases family_descends (prefixWord ++ tailWord_3510596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3510601 : List Nat := [1, 2, 1, 1, 2, 3, 1, 3, 1, 7]
def baseStart_3510601 : Nat := 118140960795 + 3510601 * 2 ^ 59
def prefixEnd_3510601 : Nat := 4983230072969 + 3 ^ 40 * 3510601 * 2
def baseEnd_3510601 : Nat := 1201750466103149660761697

theorem tailTrace_3510601 : CollatzResearch.WordTrace tailWord_3510601 prefixEnd_3510601 1201750466103149660761697 := by
  unfold tailWord_3510601
  simp only [CollatzResearch.WordTrace]
  refine ⟨128042137554699614762267657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85361425036466409841511771 128042137554699614762267657)
  ·
    refine ⟨96031603166024711071700743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128042137554699614762267657 96031603166024711071700743)
    ·
      refine ⟨144047404749037066607551115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96031603166024711071700743 144047404749037066607551115)
      ·
        refine ⟨216071107123555599911326673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144047404749037066607551115 216071107123555599911326673)
        ·
          refine ⟨162053330342666699933495005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 216071107123555599911326673 162053330342666699933495005)
          ·
            refine ⟨60769998878500012475060627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 162053330342666699933495005 60769998878500012475060627)
            ·
              refine ⟨91154998317750018712590941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60769998878500012475060627 91154998317750018712590941)
              ·
                refine ⟨34183124369156257017221603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91154998317750018712590941 34183124369156257017221603)
                ·
                  refine ⟨51274686553734385525832405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34183124369156257017221603 51274686553734385525832405)
                  ·
                    refine ⟨1201750466103149660761697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51274686553734385525832405 1201750466103149660761697)
                    ·
                      rfl

theorem cell22_3510601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 3, 1, 7].length) (baseStart_3510601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3510601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3510601 prefixEnd_3510601 := by exact prefixLift 3510601
  have htrace : WordTrace (prefixWord ++ tailWord_3510601) baseStart_3510601 baseEnd_3510601 := by
    simpa [prefixWord, tailWord_3510601, baseEnd_3510601] using wordTrace_append hprefix tailTrace_3510601
  have hstable : (prefixWord ++ tailWord_3510601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3510601).length < 2 ^ (prefixWord ++ tailWord_3510601).sum := by decide
  have hdescent : baseEnd_3510601 < baseStart_3510601 := by decide
  rcases family_descends (prefixWord ++ tailWord_3510601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3510680 : List Nat := [2, 1, 2, 5, 1, 1, 2, 2, 1, 5]
def baseStart_3510680 : Nat := 118140960795 + 3510680 * 2 ^ 59
def prefixEnd_3510680 : Nat := 4983230072969 + 3 ^ 40 * 3510680 * 2
def baseEnd_3510680 : Nat := 1201777509417619788036455

theorem tailTrace_3510680 : CollatzResearch.WordTrace tailWord_3510680 prefixEnd_3510680 1201777509417619788036455 := by
  unfold tailWord_3510680
  simp only [CollatzResearch.WordTrace]
  refine ⟨64022509460706705627196747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85363345947608940836262329 64022509460706705627196747)
  ·
    refine ⟨96033764191060058440795121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64022509460706705627196747 96033764191060058440795121)
    ·
      refine ⟨72025323143295043830596341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96033764191060058440795121 72025323143295043830596341)
      ·
        refine ⟨6752374044683910359118407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 72025323143295043830596341 6752374044683910359118407)
        ·
          refine ⟨10128561067025865538677611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6752374044683910359118407 10128561067025865538677611)
          ·
            refine ⟨15192841600538798308016417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10128561067025865538677611 15192841600538798308016417)
            ·
              refine ⟨11394631200404098731012313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15192841600538798308016417 11394631200404098731012313)
              ·
                refine ⟨8545973400303074048259235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11394631200404098731012313 8545973400303074048259235)
                ·
                  refine ⟨12818960100454611072388853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8545973400303074048259235 12818960100454611072388853)
                  ·
                    refine ⟨1201777509417619788036455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12818960100454611072388853 1201777509417619788036455)
                    ·
                      rfl

theorem cell22_3510680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 2, 1, 5].length) (baseStart_3510680 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3510680 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3510680 prefixEnd_3510680 := by exact prefixLift 3510680
  have htrace : WordTrace (prefixWord ++ tailWord_3510680) baseStart_3510680 baseEnd_3510680 := by
    simpa [prefixWord, tailWord_3510680, baseEnd_3510680] using wordTrace_append hprefix tailTrace_3510680
  have hstable : (prefixWord ++ tailWord_3510680).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3510680).length < 2 ^ (prefixWord ++ tailWord_3510680).sum := by decide
  have hdescent : baseEnd_3510680 < baseStart_3510680 := by decide
  rcases family_descends (prefixWord ++ tailWord_3510680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3510682 : List Nat := [3, 1, 1, 4, 1, 3, 2, 3, 4]
def baseStart_3510682 : Nat := 118140960795 + 3510682 * 2 ^ 59
def prefixEnd_3510682 : Nat := 4983230072969 + 3 ^ 40 * 3510682 * 2
def baseEnd_3510682 : Nat := 400592731352830816495483

theorem tailTrace_3510682 : CollatzResearch.WordTrace tailWord_3510682 prefixEnd_3510682 400592731352830816495483 := by
  unfold tailWord_3510682
  simp only [CollatzResearch.WordTrace]
  refine ⟨32011272966851541398991575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85363394578270777063977533 32011272966851541398991575)
  ·
    refine ⟨48016909450277312098487363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32011272966851541398991575 48016909450277312098487363)
    ·
      refine ⟨72025364175415968147731045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48016909450277312098487363 72025364175415968147731045)
      ·
        refine ⟨13504755782890494027699571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72025364175415968147731045 13504755782890494027699571)
        ·
          refine ⟨20257133674335741041549357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13504755782890494027699571 20257133674335741041549357)
          ·
            refine ⟨7596425127875902890581009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20257133674335741041549357 7596425127875902890581009)
            ·
              refine ⟨5697318845906927167935757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7596425127875902890581009 5697318845906927167935757)
              ·
                refine ⟨2136494567215097687975909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5697318845906927167935757 2136494567215097687975909)
                ·
                  refine ⟨400592731352830816495483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2136494567215097687975909 400592731352830816495483)
                  ·
                    rfl

theorem cell22_3510682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 2, 3, 4].length) (baseStart_3510682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3510682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3510682 prefixEnd_3510682 := by exact prefixLift 3510682
  have htrace : WordTrace (prefixWord ++ tailWord_3510682) baseStart_3510682 baseEnd_3510682 := by
    simpa [prefixWord, tailWord_3510682, baseEnd_3510682] using wordTrace_append hprefix tailTrace_3510682
  have hstable : (prefixWord ++ tailWord_3510682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3510682).length < 2 ^ (prefixWord ++ tailWord_3510682).sum := by decide
  have hdescent : baseEnd_3510682 < baseStart_3510682 := by decide
  rcases family_descends (prefixWord ++ tailWord_3510682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3510783 : List Nat := [1, 1, 2, 2, 1, 2, 4, 1, 8]
def baseStart_3510783 : Nat := 118140960795 + 3510783 * 2 ^ 59
def prefixEnd_3510783 : Nat := 4983230072969 + 3 ^ 40 * 3510783 * 2
def baseEnd_3510783 : Nat := 400604256140853950903713

theorem tailTrace_3510783 : CollatzResearch.WordTrace tailWord_3510783 prefixEnd_3510783 400604256140853950903713 := by
  unfold tailWord_3510783
  simp only [CollatzResearch.WordTrace]
  refine ⟨128048775640040259845393003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85365850426693506563595335 128048775640040259845393003)
  ·
    refine ⟨192073163460060389768089505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128048775640040259845393003 192073163460060389768089505)
    ·
      refine ⟨144054872595045292326067129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192073163460060389768089505 144054872595045292326067129)
      ·
        refine ⟨108041154446283969244550347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144054872595045292326067129 108041154446283969244550347)
        ·
          refine ⟨162061731669425953866825521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108041154446283969244550347 162061731669425953866825521)
          ·
            refine ⟨121546298752069465400119141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162061731669425953866825521 121546298752069465400119141)
            ·
              refine ⟨22789931016013024762522339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 121546298752069465400119141 22789931016013024762522339)
              ·
                refine ⟨34184896524019537143783509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22789931016013024762522339 34184896524019537143783509)
                ·
                  refine ⟨400604256140853950903713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34184896524019537143783509 400604256140853950903713)
                  ·
                    rfl

theorem cell22_3510783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 1, 8].length) (baseStart_3510783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3510783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3510783 prefixEnd_3510783 := by exact prefixLift 3510783
  have htrace : WordTrace (prefixWord ++ tailWord_3510783) baseStart_3510783 baseEnd_3510783 := by
    simpa [prefixWord, tailWord_3510783, baseEnd_3510783] using wordTrace_append hprefix tailTrace_3510783
  have hstable : (prefixWord ++ tailWord_3510783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3510783).length < 2 ^ (prefixWord ++ tailWord_3510783).sum := by decide
  have hdescent : baseEnd_3510783 < baseStart_3510783 := by decide
  rcases family_descends (prefixWord ++ tailWord_3510783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3510817 : List Nat := [1, 2, 3, 2, 2, 1, 3, 4, 4]
def baseStart_3510817 : Nat := 118140960795 + 3510817 * 2 ^ 59
def prefixEnd_3510817 : Nat := 4983230072969 + 3 ^ 40 * 3510817 * 2
def baseEnd_3510817 : Nat := 400608135772465699120345

theorem tailTrace_3510817 : CollatzResearch.WordTrace tailWord_3510817 prefixEnd_3510817 400608135772465699120345 := by
  unfold tailWord_3510817
  simp only [CollatzResearch.WordTrace]
  refine ⟨128050015721917083652130705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85366677147944722434753803 128050015721917083652130705)
  ·
    refine ⟨96037511791437812739098029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128050015721917083652130705 96037511791437812739098029)
    ·
      refine ⟨36014066921789179777161761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96037511791437812739098029 36014066921789179777161761)
      ·
        refine ⟨27010550191341884832871321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36014066921789179777161761 27010550191341884832871321)
        ·
          refine ⟨20257912643506413624653491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27010550191341884832871321 20257912643506413624653491)
          ·
            refine ⟨30386868965259620436980237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20257912643506413624653491 30386868965259620436980237)
            ·
              refine ⟨11395075861972357663867589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30386868965259620436980237 11395075861972357663867589)
              ·
                refine ⟨2136576724119817061975173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11395075861972357663867589 2136576724119817061975173)
                ·
                  refine ⟨400608135772465699120345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2136576724119817061975173 400608135772465699120345)
                  ·
                    rfl

theorem cell22_3510817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 4, 4].length) (baseStart_3510817 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3510817 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3510817 prefixEnd_3510817 := by exact prefixLift 3510817
  have htrace : WordTrace (prefixWord ++ tailWord_3510817) baseStart_3510817 baseEnd_3510817 := by
    simpa [prefixWord, tailWord_3510817, baseEnd_3510817] using wordTrace_append hprefix tailTrace_3510817
  have hstable : (prefixWord ++ tailWord_3510817).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3510817).length < 2 ^ (prefixWord ++ tailWord_3510817).sum := by decide
  have hdescent : baseEnd_3510817 < baseStart_3510817 := by decide
  rcases family_descends (prefixWord ++ tailWord_3510817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3510832 : List Nat := [2, 1, 1, 1, 2, 3, 4, 3, 2, 3]
def baseStart_3510832 : Nat := 118140960795 + 3510832 * 2 ^ 59
def prefixEnd_3510832 : Nat := 4983230072969 + 3 ^ 40 * 3510832 * 2
def baseEnd_3510832 : Nat := 1201829542123942058235989

theorem tailTrace_3510832 : CollatzResearch.WordTrace tailWord_3510832 prefixEnd_3510832 1201829542123942058235989 := by
  unfold tailWord_3510832
  simp only [CollatzResearch.WordTrace]
  refine ⟨64025281408431370606963375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85367041877908494142617833 64025281408431370606963375)
  ·
    refine ⟨96037922112647055910445063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64025281408431370606963375 96037922112647055910445063)
    ·
      refine ⟨144056883168970583865667595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96037922112647055910445063 144056883168970583865667595)
      ·
        refine ⟨216085324753455875798501393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144056883168970583865667595 216085324753455875798501393)
        ·
          refine ⟨162063993565091906848876045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 216085324753455875798501393 162063993565091906848876045)
          ·
            refine ⟨60773997586909465068328517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 162063993565091906848876045 60773997586909465068328517)
            ·
              refine ⟨11395124547545524700311597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60773997586909465068328517 11395124547545524700311597)
              ·
                refine ⟨4273171705329571762616849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11395124547545524700311597 4273171705329571762616849)
                ·
                  refine ⟨3204878778997178821962637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4273171705329571762616849 3204878778997178821962637)
                  ·
                    refine ⟨1201829542123942058235989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3204878778997178821962637 1201829542123942058235989)
                    ·
                      rfl

theorem cell22_3510832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 3, 2, 3].length) (baseStart_3510832 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3510832 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3510832 prefixEnd_3510832 := by exact prefixLift 3510832
  have htrace : WordTrace (prefixWord ++ tailWord_3510832) baseStart_3510832 baseEnd_3510832 := by
    simpa [prefixWord, tailWord_3510832, baseEnd_3510832] using wordTrace_append hprefix tailTrace_3510832
  have hstable : (prefixWord ++ tailWord_3510832).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3510832).length < 2 ^ (prefixWord ++ tailWord_3510832).sum := by decide
  have hdescent : baseEnd_3510832 < baseStart_3510832 := by decide
  rcases family_descends (prefixWord ++ tailWord_3510832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3510894 : List Nat := [4, 1, 2, 2, 2, 1, 2, 2, 3, 3]
def baseStart_3510894 : Nat := 118140960795 + 3510894 * 2 ^ 59
def prefixEnd_3510894 : Nat := 4983230072969 + 3 ^ 40 * 3510894 * 2
def baseEnd_3510894 : Nat := 1201850765990994563185799

theorem tailTrace_3510894 : CollatzResearch.WordTrace tailWord_3510894 prefixEnd_3510894 1201850765990994563185799 := by
  unfold tailWord_3510894
  simp only [CollatzResearch.WordTrace]
  refine ⟨16006603017829765725335467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85368549428425417201789157 16006603017829765725335467)
  ·
    refine ⟨24009904526744648588003201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16006603017829765725335467 24009904526744648588003201)
    ·
      refine ⟨18007428395058486441002401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24009904526744648588003201 18007428395058486441002401)
      ·
        refine ⟨13505571296293864830751801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18007428395058486441002401 13505571296293864830751801)
        ·
          refine ⟨10129178472220398623063851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13505571296293864830751801 10129178472220398623063851)
          ·
            refine ⟨15193767708330597934595777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10129178472220398623063851 15193767708330597934595777)
            ·
              refine ⟨11395325781247948450946833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15193767708330597934595777 11395325781247948450946833)
              ·
                refine ⟨8546494335935961338210125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11395325781247948450946833 8546494335935961338210125)
                ·
                  refine ⟨3204935375975985501828797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8546494335935961338210125 3204935375975985501828797)
                  ·
                    refine ⟨1201850765990994563185799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3204935375975985501828797 1201850765990994563185799)
                    ·
                      rfl

theorem cell22_3510894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 2, 3, 3].length) (baseStart_3510894 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3510894 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3510894 prefixEnd_3510894 := by exact prefixLift 3510894
  have htrace : WordTrace (prefixWord ++ tailWord_3510894) baseStart_3510894 baseEnd_3510894 := by
    simpa [prefixWord, tailWord_3510894, baseEnd_3510894] using wordTrace_append hprefix tailTrace_3510894
  have hstable : (prefixWord ++ tailWord_3510894).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3510894).length < 2 ^ (prefixWord ++ tailWord_3510894).sum := by decide
  have hdescent : baseEnd_3510894 < baseStart_3510894 := by decide
  rcases family_descends (prefixWord ++ tailWord_3510894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3510984 : List Nat := [2, 1, 3, 1, 2, 3, 1, 4, 2, 3]
def baseStart_3510984 : Nat := 118140960795 + 3510984 * 2 ^ 59
def prefixEnd_3510984 : Nat := 4983230072969 + 3 ^ 40 * 3510984 * 2
def baseEnd_3510984 : Nat := 1201881574830264328435523

theorem tailTrace_3510984 : CollatzResearch.WordTrace tailWord_3510984 prefixEnd_3510984 1201881574830264328435523 := by
  unfold tailWord_3510984
  simp only [CollatzResearch.WordTrace]
  refine ⟨64028053356156035586730003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85370737808208047448973337 64028053356156035586730003)
  ·
    refine ⟨96042080034234053380095005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64028053356156035586730003 96042080034234053380095005)
    ·
      refine ⟨36015780012837770017535627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96042080034234053380095005 36015780012837770017535627)
      ·
        refine ⟨54023670019256655026303441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36015780012837770017535627 54023670019256655026303441)
        ·
          refine ⟨40517752514442491269727581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54023670019256655026303441 40517752514442491269727581)
          ·
            refine ⟨15194157192915934226147843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40517752514442491269727581 15194157192915934226147843)
            ·
              refine ⟨22791235789373901339221765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15194157192915934226147843 22791235789373901339221765)
              ·
                refine ⟨4273356710507606501104081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22791235789373901339221765 4273356710507606501104081)
                ·
                  refine ⟨3205017532880704875828061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4273356710507606501104081 3205017532880704875828061)
                  ·
                    refine ⟨1201881574830264328435523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3205017532880704875828061 1201881574830264328435523)
                    ·
                      rfl

theorem cell22_3510984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 4, 2, 3].length) (baseStart_3510984 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3510984 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3510984 prefixEnd_3510984 := by exact prefixLift 3510984
  have htrace : WordTrace (prefixWord ++ tailWord_3510984) baseStart_3510984 baseEnd_3510984 := by
    simpa [prefixWord, tailWord_3510984, baseEnd_3510984] using wordTrace_append hprefix tailTrace_3510984
  have hstable : (prefixWord ++ tailWord_3510984).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3510984).length < 2 ^ (prefixWord ++ tailWord_3510984).sum := by decide
  have hdescent : baseEnd_3510984 < baseStart_3510984 := by decide
  rcases family_descends (prefixWord ++ tailWord_3510984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3510986 : List Nat := [3, 1, 2, 1, 4, 1, 4, 2, 4]
def baseStart_3510986 : Nat := 118140960795 + 3510986 * 2 ^ 59
def prefixEnd_3510986 : Nat := 4983230072969 + 3 ^ 40 * 3510986 * 2
def baseEnd_3510986 : Nat := 400627419823712329961839

theorem tailTrace_3510986 : CollatzResearch.WordTrace tailWord_3510986 prefixEnd_3510986 400627419823712329961839 := by
  unfold tailWord_3510986
  simp only [CollatzResearch.WordTrace]
  refine ⟨32014044914576206378758203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85370786438869883676688541 32014044914576206378758203)
  ·
    refine ⟨48021067371864309568137305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32014044914576206378758203 48021067371864309568137305)
    ·
      refine ⟨36015800528898232176102979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48021067371864309568137305 36015800528898232176102979)
      ·
        refine ⟨54023700793347348264154469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36015800528898232176102979 54023700793347348264154469)
        ·
          refine ⟨10129443898752627799528963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54023700793347348264154469 10129443898752627799528963)
          ·
            refine ⟨15194165848128941699293445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10129443898752627799528963 15194165848128941699293445)
            ·
              refine ⟨2848906096524176568617521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15194165848128941699293445 2848906096524176568617521)
              ·
                refine ⟨2136679572393132426463141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2848906096524176568617521 2136679572393132426463141)
                ·
                  refine ⟨400627419823712329961839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2136679572393132426463141 400627419823712329961839)
                  ·
                    rfl

theorem cell22_3510986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 4, 2, 4].length) (baseStart_3510986 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3510986 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3510986 prefixEnd_3510986 := by exact prefixLift 3510986
  have htrace : WordTrace (prefixWord ++ tailWord_3510986) baseStart_3510986 baseEnd_3510986 := by
    simpa [prefixWord, tailWord_3510986, baseEnd_3510986] using wordTrace_append hprefix tailTrace_3510986
  have hstable : (prefixWord ++ tailWord_3510986).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3510986).length < 2 ^ (prefixWord ++ tailWord_3510986).sum := by decide
  have hdescent : baseEnd_3510986 < baseStart_3510986 := by decide
  rcases family_descends (prefixWord ++ tailWord_3510986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3511016 : List Nat := [2, 1, 4, 1, 4, 2, 1, 1, 2, 4]
def baseStart_3511016 : Nat := 118140960795 + 3511016 * 2 ^ 59
def prefixEnd_3511016 : Nat := 4983230072969 + 3 ^ 40 * 3511016 * 2
def baseEnd_3511016 : Nat := 1201892529084226911635425

theorem tailTrace_3511016 : CollatzResearch.WordTrace tailWord_3511016 prefixEnd_3511016 1201892529084226911635425 := by
  unfold tailWord_3511016
  simp only [CollatzResearch.WordTrace]
  refine ⟨64028636924098070319312451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85371515898797427092416601 64028636924098070319312451)
  ·
    refine ⟨96042955386147105478968677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64028636924098070319312451 96042955386147105478968677)
    ·
      refine ⟨18008054134902582277306627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 96042955386147105478968677 18008054134902582277306627)
      ·
        refine ⟨27012081202353873415959941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18008054134902582277306627 27012081202353873415959941)
        ·
          refine ⟨5064765225441351265492489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27012081202353873415959941 5064765225441351265492489)
          ·
            refine ⟨3798573919081013449119367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5064765225441351265492489 3798573919081013449119367)
            ·
              refine ⟨5697860878621520173679051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3798573919081013449119367 5697860878621520173679051)
              ·
                refine ⟨8546791317932280260518577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5697860878621520173679051 8546791317932280260518577)
                ·
                  refine ⟨6410093488449210195388933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8546791317932280260518577 6410093488449210195388933)
                  ·
                    refine ⟨1201892529084226911635425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6410093488449210195388933 1201892529084226911635425)
                    ·
                      rfl

theorem cell22_3511016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 1, 1, 2, 4].length) (baseStart_3511016 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3511016 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3511016 prefixEnd_3511016 := by exact prefixLift 3511016
  have htrace : WordTrace (prefixWord ++ tailWord_3511016) baseStart_3511016 baseEnd_3511016 := by
    simpa [prefixWord, tailWord_3511016, baseEnd_3511016] using wordTrace_append hprefix tailTrace_3511016
  have hstable : (prefixWord ++ tailWord_3511016).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3511016).length < 2 ^ (prefixWord ++ tailWord_3511016).sum := by decide
  have hdescent : baseEnd_3511016 < baseStart_3511016 := by decide
  rcases family_descends (prefixWord ++ tailWord_3511016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3511057 : List Nat := [1, 2, 2, 1, 1, 3, 4, 1, 2, 5]
def baseStart_3511057 : Nat := 118140960795 + 3511057 * 2 ^ 59
def prefixEnd_3511057 : Nat := 4983230072969 + 3 ^ 40 * 3511057 * 2
def baseEnd_3511057 : Nat := 1201906564222116471360299

theorem tailTrace_3511057 : CollatzResearch.WordTrace tailWord_3511057 prefixEnd_3511057 1201906564222116471360299 := by
  unfold tailWord_3511057
  simp only [CollatzResearch.WordTrace]
  refine ⟨128058769241047604640867425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85372512827365069760578283 128058769241047604640867425)
  ·
    refine ⟨96044076930785703480650569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128058769241047604640867425 96044076930785703480650569)
    ·
      refine ⟨72033057698089277610487927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96044076930785703480650569 72033057698089277610487927)
      ·
        refine ⟨108049586547133916415731891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72033057698089277610487927 108049586547133916415731891)
        ·
          refine ⟨162074379820700874623597837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108049586547133916415731891 162074379820700874623597837)
          ·
            refine ⟨60777892432762827983849189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 162074379820700874623597837 60777892432762827983849189)
            ·
              refine ⟨11395854831143030246971723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60777892432762827983849189 11395854831143030246971723)
              ·
                refine ⟨17093782246714545370457585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11395854831143030246971723 17093782246714545370457585)
                ·
                  refine ⟨12820336685035909027843189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17093782246714545370457585 12820336685035909027843189)
                  ·
                    refine ⟨1201906564222116471360299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12820336685035909027843189 1201906564222116471360299)
                    ·
                      rfl

theorem cell22_3511057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 5].length) (baseStart_3511057 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3511057 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3511057 prefixEnd_3511057 := by exact prefixLift 3511057
  have htrace : WordTrace (prefixWord ++ tailWord_3511057) baseStart_3511057 baseEnd_3511057 := by
    simpa [prefixWord, tailWord_3511057, baseEnd_3511057] using wordTrace_append hprefix tailTrace_3511057
  have hstable : (prefixWord ++ tailWord_3511057).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3511057).length < 2 ^ (prefixWord ++ tailWord_3511057).sum := by decide
  have hdescent : baseEnd_3511057 < baseStart_3511057 := by decide
  rcases family_descends (prefixWord ++ tailWord_3511057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3511059 : List Nat := [1, 1, 1, 2, 1, 3, 7, 1, 5]
def baseStart_3511059 : Nat := 118140960795 + 3511059 * 2 ^ 59
def prefixEnd_3511059 : Nat := 4983230072969 + 3 ^ 40 * 3511059 * 2
def baseEnd_3511059 : Nat := 400635749620996377603431

theorem tailTrace_3511059 : CollatzResearch.WordTrace tailWord_3511059 prefixEnd_3511059 400635749620996377603431 := by
  unfold tailWord_3511059
  simp only [CollatzResearch.WordTrace]
  refine ⟨128058842187040358982440231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85372561458026905988293487 128058842187040358982440231)
  ·
    refine ⟨192088263280560538473660347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128058842187040358982440231 192088263280560538473660347)
    ·
      refine ⟨288132394920840807710490521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192088263280560538473660347 288132394920840807710490521)
      ·
        refine ⟨216099296190630605782867891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 288132394920840807710490521 216099296190630605782867891)
        ·
          refine ⟨324148944285945908674301837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216099296190630605782867891 324148944285945908674301837)
          ·
            refine ⟨121555854107229715752863189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 324148944285945908674301837 121555854107229715752863189)
            ·
              refine ⟨2848965330638196462957731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 121555854107229715752863189 2848965330638196462957731)
              ·
                refine ⟨4273447995957294694436597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2848965330638196462957731 4273447995957294694436597)
                ·
                  refine ⟨400635749620996377603431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4273447995957294694436597 400635749620996377603431)
                  ·
                    rfl

theorem cell22_3511059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 7, 1, 5].length) (baseStart_3511059 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3511059 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3511059 prefixEnd_3511059 := by exact prefixLift 3511059
  have htrace : WordTrace (prefixWord ++ tailWord_3511059) baseStart_3511059 baseEnd_3511059 := by
    simpa [prefixWord, tailWord_3511059, baseEnd_3511059] using wordTrace_append hprefix tailTrace_3511059
  have hstable : (prefixWord ++ tailWord_3511059).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3511059).length < 2 ^ (prefixWord ++ tailWord_3511059).sum := by decide
  have hdescent : baseEnd_3511059 < baseStart_3511059 := by decide
  rcases family_descends (prefixWord ++ tailWord_3511059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3511089 : List Nat := [1, 2, 2, 3, 2, 1, 1, 5, 1, 4]
def baseStart_3511089 : Nat := 118140960795 + 3511089 * 2 ^ 59
def prefixEnd_3511089 : Nat := 4983230072969 + 3 ^ 40 * 3511089 * 2
def baseEnd_3511089 : Nat := 1201917518476079054560201

theorem tailTrace_3511089 : CollatzResearch.WordTrace tailWord_3511089 prefixEnd_3511089 1201917518476079054560201 := by
  unfold tailWord_3511089
  simp only [CollatzResearch.WordTrace]
  refine ⟨128059936376931674106032321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85373290917954449404021547 128059936376931674106032321)
  ·
    refine ⟨96044952282698755579524241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128059936376931674106032321 96044952282698755579524241)
    ·
      refine ⟨72033714212024066684643181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96044952282698755579524241 72033714212024066684643181)
      ·
        refine ⟨27012642829509025006741193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72033714212024066684643181 27012642829509025006741193)
        ·
          refine ⟨20259482122131768755055895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27012642829509025006741193 20259482122131768755055895)
          ·
            refine ⟨30389223183197653132583843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20259482122131768755055895 30389223183197653132583843)
            ·
              refine ⟨45583834774796479698875765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30389223183197653132583843 45583834774796479698875765)
              ·
                refine ⟨4273484510137169971769603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45583834774796479698875765 4273484510137169971769603)
                ·
                  refine ⟨6410226765205754957654405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4273484510137169971769603 6410226765205754957654405)
                  ·
                    refine ⟨1201917518476079054560201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6410226765205754957654405 1201917518476079054560201)
                    ·
                      rfl

theorem cell22_3511089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 5, 1, 4].length) (baseStart_3511089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3511089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3511089 prefixEnd_3511089 := by exact prefixLift 3511089
  have htrace : WordTrace (prefixWord ++ tailWord_3511089) baseStart_3511089 baseEnd_3511089 := by
    simpa [prefixWord, tailWord_3511089, baseEnd_3511089] using wordTrace_append hprefix tailTrace_3511089
  have hstable : (prefixWord ++ tailWord_3511089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3511089).length < 2 ^ (prefixWord ++ tailWord_3511089).sum := by decide
  have hdescent : baseEnd_3511089 < baseStart_3511089 := by decide
  rcases family_descends (prefixWord ++ tailWord_3511089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3511104 : List Nat := [2, 1, 1, 2, 2, 1, 1, 8, 4]
def baseStart_3511104 : Nat := 118140960795 + 3511104 * 2 ^ 59
def prefixEnd_3511104 : Nat := 4983230072969 + 3 ^ 40 * 3511104 * 2
def baseEnd_3511104 : Nat := 400640884427541338478385

theorem tailTrace_3511104 : CollatzResearch.WordTrace tailWord_3511104 prefixEnd_3511104 400640884427541338478385 := by
  unfold tailWord_3511104
  simp only [CollatzResearch.WordTrace]
  refine ⟨64030241735938665833914183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85373655647918221111885577 64030241735938665833914183)
  ·
    refine ⟨96045362603907998750871275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64030241735938665833914183 96045362603907998750871275)
    ·
      refine ⟨144068043905861998126306913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96045362603907998750871275 144068043905861998126306913)
      ·
        refine ⟨108051032929396498594730185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144068043905861998126306913 108051032929396498594730185)
        ·
          refine ⟨81038274697047373946047639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108051032929396498594730185 81038274697047373946047639)
          ·
            refine ⟨121557412045571060919071459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81038274697047373946047639 121557412045571060919071459)
            ·
              refine ⟨182336118068356591378607189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121557412045571060919071459 182336118068356591378607189)
              ·
                refine ⟨2136751383613553805218053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 182336118068356591378607189 2136751383613553805218053)
                ·
                  refine ⟨400640884427541338478385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2136751383613553805218053 400640884427541338478385)
                  ·
                    rfl

theorem cell22_3511104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 8, 4].length) (baseStart_3511104 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3511104 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3511104 prefixEnd_3511104 := by exact prefixLift 3511104
  have htrace : WordTrace (prefixWord ++ tailWord_3511104) baseStart_3511104 baseEnd_3511104 := by
    simpa [prefixWord, tailWord_3511104, baseEnd_3511104] using wordTrace_append hprefix tailTrace_3511104
  have hstable : (prefixWord ++ tailWord_3511104).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3511104).length < 2 ^ (prefixWord ++ tailWord_3511104).sum := by decide
  have hdescent : baseEnd_3511104 < baseStart_3511104 := by decide
  rcases family_descends (prefixWord ++ tailWord_3511104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3511164 : List Nat := [2, 2, 2, 1, 1, 1, 1, 2, 7, 3]
def baseStart_3511164 : Nat := 118140960795 + 3511164 * 2 ^ 59
def prefixEnd_3511164 : Nat := 4983230072969 + 3 ^ 40 * 3511164 * 2
def baseEnd_3511164 : Nat := 1201943192508803858934971

theorem tailTrace_3511164 : CollatzResearch.WordTrace tailWord_3511164 prefixEnd_3511164 1201943192508803858934971 := by
  unfold tailWord_3511164
  simp only [CollatzResearch.WordTrace]
  refine ⟨64031335925829980957506273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85375114567773307943341697 64031335925829980957506273)
  ·
    refine ⟨48023501944372485718129705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64031335925829980957506273 48023501944372485718129705)
    ·
      refine ⟨36017626458279364288597279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48023501944372485718129705 36017626458279364288597279)
      ·
        refine ⟨54026439687419046432895919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36017626458279364288597279 54026439687419046432895919)
        ·
          refine ⟨81039659531128569649343879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54026439687419046432895919 81039659531128569649343879)
          ·
            refine ⟨121559489296692854474015819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81039659531128569649343879 121559489296692854474015819)
            ·
              refine ⟨182339233945039281711023729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121559489296692854474015819 182339233945039281711023729)
              ·
                refine ⟨136754425458779461283267797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 182339233945039281711023729 136754425458779461283267797)
                ·
                  refine ⟨3205181846690143623826589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 136754425458779461283267797 3205181846690143623826589)
                  ·
                    refine ⟨1201943192508803858934971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3205181846690143623826589 1201943192508803858934971)
                    ·
                      rfl

theorem cell22_3511164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 2, 7, 3].length) (baseStart_3511164 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3511164 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3511164 prefixEnd_3511164 := by exact prefixLift 3511164
  have htrace : WordTrace (prefixWord ++ tailWord_3511164) baseStart_3511164 baseEnd_3511164 := by
    simpa [prefixWord, tailWord_3511164, baseEnd_3511164] using wordTrace_append hprefix tailTrace_3511164
  have hstable : (prefixWord ++ tailWord_3511164).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3511164).length < 2 ^ (prefixWord ++ tailWord_3511164).sum := by decide
  have hdescent : baseEnd_3511164 < baseStart_3511164 := by decide
  rcases family_descends (prefixWord ++ tailWord_3511164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3511170 : List Nat := [3, 4, 2, 2, 1, 1, 2, 1, 1, 5]
def baseStart_3511170 : Nat := 118140960795 + 3511170 * 2 ^ 59
def prefixEnd_3511170 : Nat := 4983230072969 + 3 ^ 40 * 3511170 * 2
def baseEnd_3511170 : Nat := 1201945246431421843284953

theorem tailTrace_3511170 : CollatzResearch.WordTrace tailWord_3511170 prefixEnd_3511170 1201945246431421843284953 := by
  unfold tailWord_3511170
  simp only [CollatzResearch.WordTrace]
  refine ⟨32015722672409556234932741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85375260459758816626487309 32015722672409556234932741)
  ·
    refine ⟨6002948001076791794049889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32015722672409556234932741 6002948001076791794049889)
    ·
      refine ⟨4502211000807593845537417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6002948001076791794049889 4502211000807593845537417)
      ·
        refine ⟨3376658250605695384153063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4502211000807593845537417 3376658250605695384153063)
        ·
          refine ⟨5064987375908543076229595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3376658250605695384153063 5064987375908543076229595)
          ·
            refine ⟨7597481063862814614344393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5064987375908543076229595 7597481063862814614344393)
            ·
              refine ⟨5698110797897110960758295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7597481063862814614344393 5698110797897110960758295)
              ·
                refine ⟨8547166196845666441137443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5698110797897110960758295 8547166196845666441137443)
                ·
                  refine ⟨12820749295268499661706165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8547166196845666441137443 12820749295268499661706165)
                  ·
                    refine ⟨1201945246431421843284953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12820749295268499661706165 1201945246431421843284953)
                    ·
                      rfl

theorem cell22_3511170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 2, 1, 1, 5].length) (baseStart_3511170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3511170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3511170 prefixEnd_3511170 := by exact prefixLift 3511170
  have htrace : WordTrace (prefixWord ++ tailWord_3511170) baseStart_3511170 baseEnd_3511170 := by
    simpa [prefixWord, tailWord_3511170, baseEnd_3511170] using wordTrace_append hprefix tailTrace_3511170
  have hstable : (prefixWord ++ tailWord_3511170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3511170).length < 2 ^ (prefixWord ++ tailWord_3511170).sum := by decide
  have hdescent : baseEnd_3511170 < baseStart_3511170 := by decide
  rcases family_descends (prefixWord ++ tailWord_3511170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3511239 : List Nat := [1, 1, 4, 1, 1, 2, 4, 2, 6]
def baseStart_3511239 : Nat := 118140960795 + 3511239 * 2 ^ 59
def prefixEnd_3511239 : Nat := 4983230072969 + 3 ^ 40 * 3511239 * 2
def baseEnd_3511239 : Nat := 400656288847176221103247

theorem tailTrace_3511239 : CollatzResearch.WordTrace tailWord_3511239 prefixEnd_3511239 400656288847176221103247 := by
  unfold tailWord_3511239
  simp only [CollatzResearch.WordTrace]
  refine ⟨128065407326388249723992771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85376938217592166482661847 128065407326388249723992771)
  ·
    refine ⟨192098110989582374585989157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128065407326388249723992771 192098110989582374585989157)
    ·
      refine ⟨36018395810546695234872967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 192098110989582374585989157 36018395810546695234872967)
      ·
        refine ⟨54027593715820042852309451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36018395810546695234872967 54027593715820042852309451)
        ·
          refine ⟨81041390573730064278464177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54027593715820042852309451 81041390573730064278464177)
          ·
            refine ⟨60781042930297548208848133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81041390573730064278464177 60781042930297548208848133)
            ·
              refine ⟨11396445549430790289159025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60781042930297548208848133 11396445549430790289159025)
              ·
                refine ⟨8547334162073092716869269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11396445549430790289159025 8547334162073092716869269)
                ·
                  refine ⟨400656288847176221103247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8547334162073092716869269 400656288847176221103247)
                  ·
                    rfl

theorem cell22_3511239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 2, 6].length) (baseStart_3511239 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3511239 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3511239 prefixEnd_3511239 := by exact prefixLift 3511239
  have htrace : WordTrace (prefixWord ++ tailWord_3511239) baseStart_3511239 baseEnd_3511239 := by
    simpa [prefixWord, tailWord_3511239, baseEnd_3511239] using wordTrace_append hprefix tailTrace_3511239
  have hstable : (prefixWord ++ tailWord_3511239).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3511239).length < 2 ^ (prefixWord ++ tailWord_3511239).sum := by decide
  have hdescent : baseEnd_3511239 < baseStart_3511239 := by decide
  rcases family_descends (prefixWord ++ tailWord_3511239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3511346 : List Nat := [3, 2, 1, 1, 2, 2, 1, 5, 5]
def baseStart_3511346 : Nat := 118140960795 + 3511346 * 2 ^ 59
def prefixEnd_3511346 : Nat := 4983230072969 + 3 ^ 40 * 3511346 * 2
def baseEnd_3511346 : Nat := 400668498276072016961471

theorem tailTrace_3511346 : CollatzResearch.WordTrace tailWord_3511346 prefixEnd_3511346 400668498276072016961471 := by
  unfold tailWord_3511346
  simp only [CollatzResearch.WordTrace]
  refine ⟨32017327484250151749534473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85379539958000404665425261 32017327484250151749534473)
  ·
    refine ⟨24012995613187613812150855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32017327484250151749534473 24012995613187613812150855)
    ·
      refine ⟨36019493419781420718226283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24012995613187613812150855 36019493419781420718226283)
      ·
        refine ⟨54029240129672131077339425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36019493419781420718226283 54029240129672131077339425)
        ·
          refine ⟨40521930097254098308004569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54029240129672131077339425 40521930097254098308004569)
          ·
            refine ⟨30391447572940573731003427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40521930097254098308004569 30391447572940573731003427)
            ·
              refine ⟨45587171359410860596505141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30391447572940573731003427 45587171359410860596505141)
              ·
                refine ⟨4273797314944768180922357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45587171359410860596505141 4273797314944768180922357)
                ·
                  refine ⟨400668498276072016961471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4273797314944768180922357 400668498276072016961471)
                  ·
                    rfl

theorem cell22_3511346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 5, 5].length) (baseStart_3511346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3511346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3511346 prefixEnd_3511346 := by exact prefixLift 3511346
  have htrace : WordTrace (prefixWord ++ tailWord_3511346) baseStart_3511346 baseEnd_3511346 := by
    simpa [prefixWord, tailWord_3511346, baseEnd_3511346] using wordTrace_append hprefix tailTrace_3511346
  have hstable : (prefixWord ++ tailWord_3511346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3511346).length < 2 ^ (prefixWord ++ tailWord_3511346).sum := by decide
  have hdescent : baseEnd_3511346 < baseStart_3511346 := by decide
  rcases family_descends (prefixWord ++ tailWord_3511346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3511350 : List Nat := [5, 1, 2, 1, 1, 3, 1, 2, 3, 3]
def baseStart_3511350 : Nat := 118140960795 + 3511350 * 2 ^ 59
def prefixEnd_3511350 : Nat := 4983230072969 + 3 ^ 40 * 3511350 * 2
def baseEnd_3511350 : Nat := 1202006864109961373784401

theorem tailTrace_3511350 : CollatzResearch.WordTrace tailWord_3511350 prefixEnd_3511350 1202006864109961373784401 := by
  unfold tailWord_3511350
  simp only [CollatzResearch.WordTrace]
  refine ⟨8004340989311632230080219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 85379637219324077120855669 8004340989311632230080219)
  ·
    refine ⟨12006511483967448345120329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8004340989311632230080219 12006511483967448345120329)
    ·
      refine ⟨9004883612975586258840247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12006511483967448345120329 9004883612975586258840247)
      ·
        refine ⟨13507325419463379388260371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9004883612975586258840247 13507325419463379388260371)
        ·
          refine ⟨20260988129195069082390557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13507325419463379388260371 20260988129195069082390557)
          ·
            refine ⟨7597870548448150905896459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20260988129195069082390557 7597870548448150905896459)
            ·
              refine ⟨11396805822672226358844689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7597870548448150905896459 11396805822672226358844689)
              ·
                refine ⟨8547604367004169769133517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11396805822672226358844689 8547604367004169769133517)
                ·
                  refine ⟨3205351637626563663425069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8547604367004169769133517 3205351637626563663425069)
                  ·
                    refine ⟨1202006864109961373784401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3205351637626563663425069 1202006864109961373784401)
                    ·
                      rfl

theorem cell22_3511350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 2, 3, 3].length) (baseStart_3511350 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3511350 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3511350 prefixEnd_3511350 := by exact prefixLift 3511350
  have htrace : WordTrace (prefixWord ++ tailWord_3511350) baseStart_3511350 baseEnd_3511350 := by
    simpa [prefixWord, tailWord_3511350, baseEnd_3511350] using wordTrace_append hprefix tailTrace_3511350
  have hstable : (prefixWord ++ tailWord_3511350).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3511350).length < 2 ^ (prefixWord ++ tailWord_3511350).sum := by decide
  have hdescent : baseEnd_3511350 < baseStart_3511350 := by decide
  rcases family_descends (prefixWord ++ tailWord_3511350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3511391 : List Nat := [1, 1, 2, 3, 1, 1, 6, 1, 6]
def baseStart_3511391 : Nat := 118140960795 + 3511391 * 2 ^ 59
def prefixEnd_3511391 : Nat := 4983230072969 + 3 ^ 40 * 3511391 * 2
def baseEnd_3511391 : Nat := 400673633082616977836425

theorem tailTrace_3511391 : CollatzResearch.WordTrace tailWord_3511391 prefixEnd_3511391 400673633082616977836425 := by
  unfold tailWord_3511391
  simp only [CollatzResearch.WordTrace]
  refine ⟨128070951221837579683526027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85380634147891719789017351 128070951221837579683526027)
  ·
    refine ⟨192106426832756369525289041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128070951221837579683526027 192106426832756369525289041)
    ·
      refine ⟨144079820124567277143966781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192106426832756369525289041 144079820124567277143966781)
      ·
        refine ⟨54029932546712728928987543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144079820124567277143966781 54029932546712728928987543)
        ·
          refine ⟨81044898820069093393481315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54029932546712728928987543 81044898820069093393481315)
          ·
            refine ⟨121567348230103640090221973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81044898820069093393481315 121567348230103640090221973)
            ·
              refine ⟨5698469448286108129229155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 121567348230103640090221973 5698469448286108129229155)
              ·
                refine ⟨8547704172429162193843733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5698469448286108129229155 8547704172429162193843733)
                ·
                  refine ⟨400673633082616977836425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8547704172429162193843733 400673633082616977836425)
                  ·
                    rfl

theorem cell22_3511391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 6, 1, 6].length) (baseStart_3511391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3511391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3511391 prefixEnd_3511391 := by exact prefixLift 3511391
  have htrace : WordTrace (prefixWord ++ tailWord_3511391) baseStart_3511391 baseEnd_3511391 := by
    simpa [prefixWord, tailWord_3511391, baseEnd_3511391] using wordTrace_append hprefix tailTrace_3511391
  have hstable : (prefixWord ++ tailWord_3511391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3511391).length < 2 ^ (prefixWord ++ tailWord_3511391).sum := by decide
  have hdescent : baseEnd_3511391 < baseStart_3511391 := by decide
  rcases family_descends (prefixWord ++ tailWord_3511391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3511421 : List Nat := [1, 4, 1, 1, 3, 1, 1, 3, 1, 6]
def baseStart_3511421 : Nat := 118140960795 + 3511421 * 2 ^ 59
def prefixEnd_3511421 : Nat := 4983230072969 + 3 ^ 40 * 3511421 * 2
def baseEnd_3511421 : Nat := 1202031168860940855259183

theorem tailTrace_3511421 : CollatzResearch.WordTrace tailWord_3511421 prefixEnd_3511421 1202031168860940855259183 := by
  unfold tailWord_3511421
  simp only [CollatzResearch.WordTrace]
  refine ⟨128072045411728894807118117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85381363607819263204745411 128072045411728894807118117)
  ·
    refine ⟨24013508514699167776334647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 128072045411728894807118117 24013508514699167776334647)
    ·
      refine ⟨36020262772048751664501971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24013508514699167776334647 36020262772048751664501971)
      ·
        refine ⟨54030394158073127496752957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36020262772048751664501971 54030394158073127496752957)
        ·
          refine ⟨20261397809277422811282359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54030394158073127496752957 20261397809277422811282359)
          ·
            refine ⟨30392096713916134216923539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20261397809277422811282359 30392096713916134216923539)
            ·
              refine ⟨45588145070874201325385309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30392096713916134216923539 45588145070874201325385309)
              ·
                refine ⟨17095554401577825497019491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45588145070874201325385309 17095554401577825497019491)
                ·
                  refine ⟨25643331602366738245529237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17095554401577825497019491 25643331602366738245529237)
                  ·
                    refine ⟨1202031168860940855259183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25643331602366738245529237 1202031168860940855259183)
                    ·
                      rfl

theorem cell22_3511421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 3, 1, 6].length) (baseStart_3511421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3511421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3511421 prefixEnd_3511421 := by exact prefixLift 3511421
  have htrace : WordTrace (prefixWord ++ tailWord_3511421) baseStart_3511421 baseEnd_3511421 := by
    simpa [prefixWord, tailWord_3511421, baseEnd_3511421] using wordTrace_append hprefix tailTrace_3511421
  have hstable : (prefixWord ++ tailWord_3511421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3511421).length < 2 ^ (prefixWord ++ tailWord_3511421).sum := by decide
  have hdescent : baseEnd_3511421 < baseStart_3511421 := by decide
  rcases family_descends (prefixWord ++ tailWord_3511421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3511425 : List Nat := [1, 2, 4, 2, 2, 1, 3, 3, 4]
def baseStart_3511425 : Nat := 118140960795 + 3511425 * 2 ^ 59
def prefixEnd_3511425 : Nat := 4983230072969 + 3 ^ 40 * 3511425 * 2
def baseEnd_3511425 : Nat := 400677512714228726053057

theorem tailTrace_3511425 : CollatzResearch.WordTrace tailWord_3511425 prefixEnd_3511425 400677512714228726053057 := by
  unfold tailWord_3511425
  simp only [CollatzResearch.WordTrace]
  refine ⟨128072191303714403490263729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85381460869142935660175819 128072191303714403490263729)
  ·
    refine ⟨96054143477785802617697797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128072191303714403490263729 96054143477785802617697797)
    ·
      refine ⟨18010151902084837990818337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 96054143477785802617697797 18010151902084837990818337)
      ·
        refine ⟨13507613926563628493113753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18010151902084837990818337 13507613926563628493113753)
        ·
          refine ⟨10130710444922721369835315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13507613926563628493113753 10130710444922721369835315)
          ·
            refine ⟨15196065667384082054752973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10130710444922721369835315 15196065667384082054752973)
            ·
              refine ⟨5698524625269030770532365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15196065667384082054752973 5698524625269030770532365)
              ·
                refine ⟨2136946734475886538949637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5698524625269030770532365 2136946734475886538949637)
                ·
                  refine ⟨400677512714228726053057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2136946734475886538949637 400677512714228726053057)
                  ·
                    rfl

theorem cell22_3511425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 3, 3, 4].length) (baseStart_3511425 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3511425 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3511425 prefixEnd_3511425 := by exact prefixLift 3511425
  have htrace : WordTrace (prefixWord ++ tailWord_3511425) baseStart_3511425 baseEnd_3511425 := by
    simpa [prefixWord, tailWord_3511425, baseEnd_3511425] using wordTrace_append hprefix tailTrace_3511425
  have hstable : (prefixWord ++ tailWord_3511425).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3511425).length < 2 ^ (prefixWord ++ tailWord_3511425).sum := by decide
  have hdescent : baseEnd_3511425 < baseStart_3511425 := by decide
  rcases family_descends (prefixWord ++ tailWord_3511425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3511438 : List Nat := [4, 1, 1, 3, 2, 1, 1, 1, 4, 4]
def baseStart_3511438 : Nat := 118140960795 + 3511438 * 2 ^ 59
def prefixEnd_3511438 : Nat := 4983230072969 + 3 ^ 40 * 3511438 * 2
def baseEnd_3511438 : Nat := 1202036988308358477584131

theorem tailTrace_3511438 : CollatzResearch.WordTrace tailWord_3511438 prefixEnd_3511438 1202036988308358477584131 := by
  unfold tailWord_3511438
  simp only [CollatzResearch.WordTrace]
  refine ⟨16009083181583413338810871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85381776968444871140324645 16009083181583413338810871)
  ·
    refine ⟨24013624772375120008216307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16009083181583413338810871 24013624772375120008216307)
    ·
      refine ⟨36020437158562680012324461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24013624772375120008216307 36020437158562680012324461)
      ·
        refine ⟨13507663934461005004621673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36020437158562680012324461 13507663934461005004621673)
        ·
          refine ⟨10130747950845753753466255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13507663934461005004621673 10130747950845753753466255)
          ·
            refine ⟨15196121926268630630199383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10130747950845753753466255 15196121926268630630199383)
            ·
              refine ⟨22794182889402945945299075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15196121926268630630199383 22794182889402945945299075)
              ·
                refine ⟨34191274334104418917948613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22794182889402945945299075 34191274334104418917948613)
                ·
                  refine ⟨6410863937644578547115365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34191274334104418917948613 6410863937644578547115365)
                  ·
                    refine ⟨1202036988308358477584131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6410863937644578547115365 1202036988308358477584131)
                    ·
                      rfl

theorem cell22_3511438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 1, 4, 4].length) (baseStart_3511438 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3511438 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3511438 prefixEnd_3511438 := by exact prefixLift 3511438
  have htrace : WordTrace (prefixWord ++ tailWord_3511438) baseStart_3511438 baseEnd_3511438 := by
    simpa [prefixWord, tailWord_3511438, baseEnd_3511438] using wordTrace_append hprefix tailTrace_3511438
  have hstable : (prefixWord ++ tailWord_3511438).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3511438).length < 2 ^ (prefixWord ++ tailWord_3511438).sum := by decide
  have hdescent : baseEnd_3511438 < baseStart_3511438 := by decide
  rcases family_descends (prefixWord ++ tailWord_3511438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3511442 : List Nat := [3, 2, 3, 1, 1, 3, 3, 2, 4]
def baseStart_3511442 : Nat := 118140960795 + 3511442 * 2 ^ 59
def prefixEnd_3511442 : Nat := 4983230072969 + 3 ^ 40 * 3511442 * 2
def baseEnd_3511442 : Nat := 400679452530034600161373

theorem tailTrace_3511442 : CollatzResearch.WordTrace tailWord_3511442 prefixEnd_3511442 400679452530034600161373 := by
  unfold tailWord_3511442
  simp only [CollatzResearch.WordTrace]
  refine ⟨32018202836163203848408145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85381874229768543595755053 32018202836163203848408145)
  ·
    refine ⟨24013652127122402886306109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32018202836163203848408145 24013652127122402886306109)
    ·
      refine ⟨9005119547670901082364791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24013652127122402886306109 9005119547670901082364791)
      ·
        refine ⟨13507679321506351623547187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9005119547670901082364791 13507679321506351623547187)
        ·
          refine ⟨20261518982259527435320781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13507679321506351623547187 20261518982259527435320781)
          ·
            refine ⟨7598069618347322788245293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20261518982259527435320781 7598069618347322788245293)
            ·
              refine ⟨2849276106880246045591985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7598069618347322788245293 2849276106880246045591985)
              ·
                refine ⟨2136957080160184534193989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2849276106880246045591985 2136957080160184534193989)
                ·
                  refine ⟨400679452530034600161373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2136957080160184534193989 400679452530034600161373)
                  ·
                    rfl

theorem cell22_3511442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 3, 2, 4].length) (baseStart_3511442 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3511442 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3511442 prefixEnd_3511442 := by exact prefixLift 3511442
  have htrace : WordTrace (prefixWord ++ tailWord_3511442) baseStart_3511442 baseEnd_3511442 := by
    simpa [prefixWord, tailWord_3511442, baseEnd_3511442] using wordTrace_append hprefix tailTrace_3511442
  have hstable : (prefixWord ++ tailWord_3511442).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3511442).length < 2 ^ (prefixWord ++ tailWord_3511442).sum := by decide
  have hdescent : baseEnd_3511442 < baseStart_3511442 := by decide
  rcases family_descends (prefixWord ++ tailWord_3511442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3511498 : List Nat := [3, 1, 2, 1, 3, 2, 1, 4, 5]
def baseStart_3511498 : Nat := 118140960795 + 3511498 * 2 ^ 59
def prefixEnd_3511498 : Nat := 4983230072969 + 3 ^ 40 * 3511498 * 2
def baseEnd_3511498 : Nat := 400685842511512773694649

theorem tailTrace_3511498 : CollatzResearch.WordTrace tailWord_3511498 prefixEnd_3511498 400685842511512773694649 := by
  unfold tailWord_3511498
  simp only [CollatzResearch.WordTrace]
  refine ⟨32018713458112484239417787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85383235888299957971780765 32018713458112484239417787)
  ·
    refine ⟨48028070187168726359126681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32018713458112484239417787 48028070187168726359126681)
    ·
      refine ⟨36021052640376544769345011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48028070187168726359126681 36021052640376544769345011)
      ·
        refine ⟨54031578960564817154017517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36021052640376544769345011 54031578960564817154017517)
        ·
          refine ⟨20261842110211806432756569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54031578960564817154017517 20261842110211806432756569)
          ·
            refine ⟨15196381582658854824567427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20261842110211806432756569 15196381582658854824567427)
            ·
              refine ⟨22794572373988282236851141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15196381582658854824567427 22794572373988282236851141)
              ·
                refine ⟨4273982320122802919409589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22794572373988282236851141 4273982320122802919409589)
                ·
                  refine ⟨400685842511512773694649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4273982320122802919409589 400685842511512773694649)
                  ·
                    rfl

theorem cell22_3511498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 4, 5].length) (baseStart_3511498 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3511498 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3511498 prefixEnd_3511498 := by exact prefixLift 3511498
  have htrace : WordTrace (prefixWord ++ tailWord_3511498) baseStart_3511498 baseEnd_3511498 := by
    simpa [prefixWord, tailWord_3511498, baseEnd_3511498] using wordTrace_append hprefix tailTrace_3511498
  have hstable : (prefixWord ++ tailWord_3511498).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3511498).length < 2 ^ (prefixWord ++ tailWord_3511498).sum := by decide
  have hdescent : baseEnd_3511498 < baseStart_3511498 := by decide
  rcases family_descends (prefixWord ++ tailWord_3511498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3511528 : List Nat := [2, 1, 4, 1, 2, 1, 1, 3, 3, 4]
def baseStart_3511528 : Nat := 118140960795 + 3511528 * 2 ^ 59
def prefixEnd_3511528 : Nat := 4983230072969 + 3 ^ 40 * 3511528 * 2
def baseEnd_3511528 : Nat := 1202067797147628242833855

theorem tailTrace_3511528 : CollatzResearch.WordTrace tailWord_3511528 prefixEnd_3511528 1202067797147628242833855 := by
  unfold tailWord_3511528
  simp only [CollatzResearch.WordTrace]
  refine ⟨64037974011170626040631619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85383965348227501387508825 64037974011170626040631619)
  ·
    refine ⟨96056961016755939060947429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64037974011170626040631619 96056961016755939060947429)
    ·
      refine ⟨18010680190641738573927643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 96056961016755939060947429 18010680190641738573927643)
      ·
        refine ⟨27016020285962607860891465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18010680190641738573927643 27016020285962607860891465)
        ·
          refine ⟨20262015214471955895668599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27016020285962607860891465 20262015214471955895668599)
          ·
            refine ⟨30393022821707933843502899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20262015214471955895668599 30393022821707933843502899)
            ·
              refine ⟨45589534232561900765254349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30393022821707933843502899 45589534232561900765254349)
              ·
                refine ⟨17096075337210712786970381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45589534232561900765254349 17096075337210712786970381)
                ·
                  refine ⟨6411028251454017295113893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17096075337210712786970381 6411028251454017295113893)
                  ·
                    refine ⟨1202067797147628242833855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6411028251454017295113893 1202067797147628242833855)
                    ·
                      rfl

theorem cell22_3511528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 3, 3, 4].length) (baseStart_3511528 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3511528 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3511528 prefixEnd_3511528 := by exact prefixLift 3511528
  have htrace : WordTrace (prefixWord ++ tailWord_3511528) baseStart_3511528 baseEnd_3511528 := by
    simpa [prefixWord, tailWord_3511528, baseEnd_3511528] using wordTrace_append hprefix tailTrace_3511528
  have hstable : (prefixWord ++ tailWord_3511528).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3511528).length < 2 ^ (prefixWord ++ tailWord_3511528).sum := by decide
  have hdescent : baseEnd_3511528 < baseStart_3511528 := by decide
  rcases family_descends (prefixWord ++ tailWord_3511528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3511560 : List Nat := [2, 1, 3, 2, 4, 1, 2, 1, 6]
def baseStart_3511560 : Nat := 118140960795 + 3511560 * 2 ^ 59
def prefixEnd_3511560 : Nat := 4983230072969 + 3 ^ 40 * 3511560 * 2
def baseEnd_3511560 : Nat := 400692917133863608677919

theorem tailTrace_3511560 : CollatzResearch.WordTrace tailWord_3511560 prefixEnd_3511560 400692917133863608677919 := by
  unfold tailWord_3511560
  simp only [CollatzResearch.WordTrace]
  refine ⟨64038557579112660773214067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85384743438816881030952089 64038557579112660773214067)
  ·
    refine ⟨96057836368668991159821101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64038557579112660773214067 96057836368668991159821101)
    ·
      refine ⟨36021688638250871684932913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96057836368668991159821101 36021688638250871684932913)
      ·
        refine ⟨27016266478688153763699685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36021688638250871684932913 27016266478688153763699685)
        ·
          refine ⟨5065549964754028830693691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27016266478688153763699685 5065549964754028830693691)
          ·
            refine ⟨7598324947131043246040537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5065549964754028830693691 7598324947131043246040537)
            ·
              refine ⟨5698743710348282434530403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7598324947131043246040537 5698743710348282434530403)
              ·
                refine ⟨8548115565522423651795605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5698743710348282434530403 8548115565522423651795605)
                ·
                  refine ⟨400692917133863608677919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8548115565522423651795605 400692917133863608677919)
                  ·
                    rfl

theorem cell22_3511560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 2, 1, 6].length) (baseStart_3511560 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3511560 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3511560 prefixEnd_3511560 := by exact prefixLift 3511560
  have htrace : WordTrace (prefixWord ++ tailWord_3511560) baseStart_3511560 baseEnd_3511560 := by
    simpa [prefixWord, tailWord_3511560, baseEnd_3511560] using wordTrace_append hprefix tailTrace_3511560
  have hstable : (prefixWord ++ tailWord_3511560).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3511560).length < 2 ^ (prefixWord ++ tailWord_3511560).sum := by decide
  have hdescent : baseEnd_3511560 < baseStart_3511560 := by decide
  rcases family_descends (prefixWord ++ tailWord_3511560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3511588 : List Nat := [2, 3, 1, 3, 1, 1, 3, 8]
def baseStart_3511588 : Nat := 118140960795 + 3511588 * 2 ^ 59
def prefixEnd_3511588 : Nat := 4983230072969 + 3 ^ 40 * 3511588 * 2
def baseEnd_3511588 : Nat := 133565370708200898481519

theorem tailTrace_3511588 : CollatzResearch.WordTrace tailWord_3511588 prefixEnd_3511588 133565370708200898481519 := by
  unfold tailWord_3511588
  simp only [CollatzResearch.WordTrace]
  refine ⟨64039068201061941164223709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85385424268082588218964945 64039068201061941164223709)
  ·
    refine ⟨24014650575398227936583891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64039068201061941164223709 24014650575398227936583891)
    ·
      refine ⟨36021975863097341904875837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24014650575398227936583891 36021975863097341904875837)
      ·
        refine ⟨13508240948661503214328439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36021975863097341904875837 13508240948661503214328439)
        ·
          refine ⟨20262361422992254821492659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13508240948661503214328439 20262361422992254821492659)
          ·
            refine ⟨30393542134488382232238989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20262361422992254821492659 30393542134488382232238989)
            ·
              refine ⟨11397578300433143337089621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30393542134488382232238989 11397578300433143337089621)
              ·
                refine ⟨133565370708200898481519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11397578300433143337089621 133565370708200898481519)
                ·
                  rfl

theorem cell22_3511588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 8].length) (baseStart_3511588 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3511588 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3511588 prefixEnd_3511588 := by exact prefixLift 3511588
  have htrace : WordTrace (prefixWord ++ tailWord_3511588) baseStart_3511588 baseEnd_3511588 := by
    simpa [prefixWord, tailWord_3511588, baseEnd_3511588] using wordTrace_append hprefix tailTrace_3511588
  have hstable : (prefixWord ++ tailWord_3511588).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3511588).length < 2 ^ (prefixWord ++ tailWord_3511588).sum := by decide
  have hdescent : baseEnd_3511588 < baseStart_3511588 := by decide
  rcases family_descends (prefixWord ++ tailWord_3511588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3511594 : List Nat := [3, 1, 4, 2, 1, 3, 1, 3, 4]
def baseStart_3511594 : Nat := 118140960795 + 3511594 * 2 ^ 59
def prefixEnd_3511594 : Nat := 4983230072969 + 3 ^ 40 * 3511594 * 2
def baseEnd_3511594 : Nat := 400696796765475356894551

theorem tailTrace_3511594 : CollatzResearch.WordTrace tailWord_3511594 prefixEnd_3511594 400696796765475356894551 := by
  unfold tailWord_3511594
  simp only [CollatzResearch.WordTrace]
  refine ⟨32019588810025536338291459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85385570160068096902110557 32019588810025536338291459)
  ·
    refine ⟨48029383215038304507437189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32019588810025536338291459 48029383215038304507437189)
    ·
      refine ⟨9005509352819682095144473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48029383215038304507437189 9005509352819682095144473)
      ·
        refine ⟨6754132014614761571358355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9005509352819682095144473 6754132014614761571358355)
        ·
          refine ⟨10131198021922142357037533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6754132014614761571358355 10131198021922142357037533)
          ·
            refine ⟨3799199258220803383889075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10131198021922142357037533 3799199258220803383889075)
            ·
              refine ⟨5698798887331205075833613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3799199258220803383889075 5698798887331205075833613)
              ·
                refine ⟨2137049582749201903437605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5698798887331205075833613 2137049582749201903437605)
                ·
                  refine ⟨400696796765475356894551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2137049582749201903437605 400696796765475356894551)
                  ·
                    rfl

theorem cell22_3511594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 1, 3, 4].length) (baseStart_3511594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3511594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3511594 prefixEnd_3511594 := by exact prefixLift 3511594
  have htrace : WordTrace (prefixWord ++ tailWord_3511594) baseStart_3511594 baseEnd_3511594 := by
    simpa [prefixWord, tailWord_3511594, baseEnd_3511594] using wordTrace_append hprefix tailTrace_3511594
  have hstable : (prefixWord ++ tailWord_3511594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3511594).length < 2 ^ (prefixWord ++ tailWord_3511594).sum := by decide
  have hdescent : baseEnd_3511594 < baseStart_3511594 := by decide
  rcases family_descends (prefixWord ++ tailWord_3511594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3511682 : List Nat := [3, 4, 2, 1, 1, 1, 1, 1, 1, 7]
def baseStart_3511682 : Nat := 118140960795 + 3511682 * 2 ^ 59
def prefixEnd_3511682 : Nat := 4983230072969 + 3 ^ 40 * 3511682 * 2
def baseEnd_3511682 : Nat := 1202120514494823174483383

theorem tailTrace_3511682 : CollatzResearch.WordTrace tailWord_3511682 prefixEnd_3511682 1202120514494823174483383 := by
  unfold tailWord_3511682
  simp only [CollatzResearch.WordTrace]
  refine ⟨32020391215945834095592325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85387709909188890921579533 32020391215945834095592325)
  ·
    refine ⟨6003823352989843892923561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32020391215945834095592325 6003823352989843892923561)
    ·
      refine ⟨4502867514742382919692671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6003823352989843892923561 4502867514742382919692671)
      ·
        refine ⟨6754301272113574379539007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4502867514742382919692671 6754301272113574379539007)
        ·
          refine ⟨10131451908170361569308511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6754301272113574379539007 10131451908170361569308511)
          ·
            refine ⟨15197177862255542353962767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10131451908170361569308511 15197177862255542353962767)
            ·
              refine ⟨22795766793383313530944151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15197177862255542353962767 22795766793383313530944151)
              ·
                refine ⟨34193650190074970296416227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22795766793383313530944151 34193650190074970296416227)
                ·
                  refine ⟨51290475285112455444624341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34193650190074970296416227 51290475285112455444624341)
                  ·
                    refine ⟨1202120514494823174483383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51290475285112455444624341 1202120514494823174483383)
                    ·
                      rfl

theorem cell22_3511682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_3511682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3511682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3511682 prefixEnd_3511682 := by exact prefixLift 3511682
  have htrace : WordTrace (prefixWord ++ tailWord_3511682) baseStart_3511682 baseEnd_3511682 := by
    simpa [prefixWord, tailWord_3511682, baseEnd_3511682] using wordTrace_append hprefix tailTrace_3511682
  have hstable : (prefixWord ++ tailWord_3511682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3511682).length < 2 ^ (prefixWord ++ tailWord_3511682).sum := by decide
  have hdescent : baseEnd_3511682 < baseStart_3511682 := by decide
  rcases family_descends (prefixWord ++ tailWord_3511682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3511712 : List Nat := [2, 1, 1, 4, 1, 2, 4, 3, 4]
def baseStart_3511712 : Nat := 118140960795 + 3511712 * 2 ^ 59
def prefixEnd_3511712 : Nat := 4983230072969 + 3 ^ 40 * 3511712 * 2
def baseEnd_3511712 : Nat := 400710261369304365411097

theorem tailTrace_3511712 : CollatzResearch.WordTrace tailWord_3511712 prefixEnd_3511712 400710261369304365411097 := by
  unfold tailWord_3511712
  simp only [CollatzResearch.WordTrace]
  refine ⟨64041329526837325752980695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85388439369116434337307593 64041329526837325752980695)
  ·
    refine ⟨96061994290255988629471043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64041329526837325752980695 96061994290255988629471043)
    ·
      refine ⟨144092991435383982944206565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96061994290255988629471043 144092991435383982944206565)
      ·
        refine ⟨27017435894134496802038731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 144092991435383982944206565 27017435894134496802038731)
        ·
          refine ⟨40526153841201745203058097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27017435894134496802038731 40526153841201745203058097)
          ·
            refine ⟨30394615380901308902293573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40526153841201745203058097 30394615380901308902293573)
            ·
              refine ⟨5698990383918995419180045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30394615380901308902293573 5698990383918995419180045)
              ·
                refine ⟨2137121393969623282192517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5698990383918995419180045 2137121393969623282192517)
                ·
                  refine ⟨400710261369304365411097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2137121393969623282192517 400710261369304365411097)
                  ·
                    rfl

theorem cell22_3511712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 4, 3, 4].length) (baseStart_3511712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3511712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3511712 prefixEnd_3511712 := by exact prefixLift 3511712
  have htrace : WordTrace (prefixWord ++ tailWord_3511712) baseStart_3511712 baseEnd_3511712 := by
    simpa [prefixWord, tailWord_3511712, baseEnd_3511712] using wordTrace_append hprefix tailTrace_3511712
  have hstable : (prefixWord ++ tailWord_3511712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3511712).length < 2 ^ (prefixWord ++ tailWord_3511712).sum := by decide
  have hdescent : baseEnd_3511712 < baseStart_3511712 := by decide
  rcases family_descends (prefixWord ++ tailWord_3511712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3511714 : List Nat := [3, 3, 1, 2, 1, 2, 4, 1, 1, 4]
def baseStart_3511714 : Nat := 118140960795 + 3511714 * 2 ^ 59
def prefixEnd_3511714 : Nat := 4983230072969 + 3 ^ 40 * 3511714 * 2
def baseEnd_3511714 : Nat := 1202131468748785757683285

theorem tailTrace_3511714 : CollatzResearch.WordTrace tailWord_3511714 prefixEnd_3511714 1202131468748785757683285 := by
  unfold tailWord_3511714
  simp only [CollatzResearch.WordTrace]
  refine ⟨32020682999916851461883549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85388487999778270565022797 32020682999916851461883549)
  ·
    refine ⟨12007756124968819298206331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32020682999916851461883549 12007756124968819298206331)
    ·
      refine ⟨18011634187453228947309497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12007756124968819298206331 18011634187453228947309497)
      ·
        refine ⟨13508725640589921710482123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18011634187453228947309497 13508725640589921710482123)
        ·
          refine ⟨20263088460884882565723185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13508725640589921710482123 20263088460884882565723185)
          ·
            refine ⟨15197316345663661924292389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20263088460884882565723185 15197316345663661924292389)
            ·
              refine ⟨2849496814811936610804823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15197316345663661924292389 2849496814811936610804823)
              ·
                refine ⟨4274245222217904916207235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2849496814811936610804823 4274245222217904916207235)
                ·
                  refine ⟨6411367833326857374310853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4274245222217904916207235 6411367833326857374310853)
                  ·
                    refine ⟨1202131468748785757683285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6411367833326857374310853 1202131468748785757683285)
                    ·
                      rfl

theorem cell22_3511714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 4, 1, 1, 4].length) (baseStart_3511714 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3511714 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3511714 prefixEnd_3511714 := by exact prefixLift 3511714
  have htrace : WordTrace (prefixWord ++ tailWord_3511714) baseStart_3511714 baseEnd_3511714 := by
    simpa [prefixWord, tailWord_3511714, baseEnd_3511714] using wordTrace_append hprefix tailTrace_3511714
  have hstable : (prefixWord ++ tailWord_3511714).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3511714).length < 2 ^ (prefixWord ++ tailWord_3511714).sum := by decide
  have hdescent : baseEnd_3511714 < baseStart_3511714 := by decide
  rcases family_descends (prefixWord ++ tailWord_3511714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3511845 : List Nat := [1, 3, 1, 2, 2, 1, 1, 1, 5, 5]
def baseStart_3511845 : Nat := 118140960795 + 3511845 * 2 ^ 59
def prefixEnd_3511845 : Nat := 4983230072969 + 3 ^ 40 * 3511845 * 2
def baseEnd_3511845 : Nat := 1202176312725945082657883

theorem tailTrace_3511845 : CollatzResearch.WordTrace tailWord_3511845 prefixEnd_3511845 1202176312725945082657883 := by
  unfold tailWord_3511845
  simp only [CollatzResearch.WordTrace]
  refine ⟨128087509962192815220552989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85391673308128543480368659 128087509962192815220552989)
  ·
    refine ⟨48032816235822305707707371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128087509962192815220552989 48032816235822305707707371)
    ·
      refine ⟨72049224353733458561561057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48032816235822305707707371 72049224353733458561561057)
      ·
        refine ⟨54036918265300093921170793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72049224353733458561561057 54036918265300093921170793)
        ·
          refine ⟨40527688698975070440878095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54036918265300093921170793 40527688698975070440878095)
          ·
            refine ⟨60791533048462605661317143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40527688698975070440878095 60791533048462605661317143)
            ·
              refine ⟨91187299572693908491975715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60791533048462605661317143 91187299572693908491975715)
              ·
                refine ⟨136780949359040862737963573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91187299572693908491975715 136780949359040862737963573)
                ·
                  refine ⟨12823214002410080881684085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 136780949359040862737963573 12823214002410080881684085)
                  ·
                    refine ⟨1202176312725945082657883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12823214002410080881684085 1202176312725945082657883)
                    ·
                      rfl

theorem cell22_3511845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 1, 5, 5].length) (baseStart_3511845 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3511845 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3511845 prefixEnd_3511845 := by exact prefixLift 3511845
  have htrace : WordTrace (prefixWord ++ tailWord_3511845) baseStart_3511845 baseEnd_3511845 := by
    simpa [prefixWord, tailWord_3511845, baseEnd_3511845] using wordTrace_append hprefix tailTrace_3511845
  have hstable : (prefixWord ++ tailWord_3511845).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3511845).length < 2 ^ (prefixWord ++ tailWord_3511845).sum := by decide
  have hdescent : baseEnd_3511845 < baseStart_3511845 := by decide
  rcases family_descends (prefixWord ++ tailWord_3511845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3511926 : List Nat := [5, 1, 1, 2, 2, 3, 2, 6]
def baseStart_3511926 : Nat := 118140960795 + 3511926 * 2 ^ 59
def prefixEnd_3511926 : Nat := 4983230072969 + 3 ^ 40 * 3511926 * 2
def baseEnd_3511926 : Nat := 133578226742365319042515

theorem tailTrace_3511926 : CollatzResearch.WordTrace tailWord_3511926 prefixEnd_3511926 133578226742365319042515 := by
  unfold tailWord_3511926
  simp only [CollatzResearch.WordTrace]
  refine ⟨8005654017181210378390727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 85393642849932910702834421 8005654017181210378390727)
  ·
    refine ⟨12008481025771815567586091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8005654017181210378390727 12008481025771815567586091)
    ·
      refine ⟨18012721538657723351379137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12008481025771815567586091 18012721538657723351379137)
      ·
        refine ⟨13509541153993292513534353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18012721538657723351379137 13509541153993292513534353)
        ·
          refine ⟨10132155865494969385150765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13509541153993292513534353 10132155865494969385150765)
          ·
            refine ⟨3799558449560613519431537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10132155865494969385150765 3799558449560613519431537)
            ·
              refine ⟨2849668837170460139573653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3799558449560613519431537 2849668837170460139573653)
              ·
                refine ⟨133578226742365319042515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2849668837170460139573653 133578226742365319042515)
                ·
                  rfl

theorem cell22_3511926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 2, 6].length) (baseStart_3511926 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3511926 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3511926 prefixEnd_3511926 := by exact prefixLift 3511926
  have htrace : WordTrace (prefixWord ++ tailWord_3511926) baseStart_3511926 baseEnd_3511926 := by
    simpa [prefixWord, tailWord_3511926, baseEnd_3511926] using wordTrace_append hprefix tailTrace_3511926
  have hstable : (prefixWord ++ tailWord_3511926).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3511926).length < 2 ^ (prefixWord ++ tailWord_3511926).sum := by decide
  have hdescent : baseEnd_3511926 < baseStart_3511926 := by decide
  rcases family_descends (prefixWord ++ tailWord_3511926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3511937 : List Nat := [1, 2, 4, 2, 1, 2, 1, 2, 7]
def baseStart_3511937 : Nat := 118140960795 + 3511937 * 2 ^ 59
def prefixEnd_3511937 : Nat := 4983230072969 + 3 ^ 40 * 3511937 * 2
def baseEnd_3511937 : Nat := 400735935402029169785867

theorem tailTrace_3511937 : CollatzResearch.WordTrace tailWord_3511937 prefixEnd_3511937 400735935402029169785867 := by
  unfold tailWord_3511937
  simp only [CollatzResearch.WordTrace]
  refine ⟨128090865477859514932902065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85393910318573009955268043 128090865477859514932902065)
  ·
    refine ⟨96068149108394636199676549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128090865477859514932902065 96068149108394636199676549)
    ·
      refine ⟨18012777957823994287439353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 96068149108394636199676549 18012777957823994287439353)
      ·
        refine ⟨13509583468367995715579515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18012777957823994287439353 13509583468367995715579515)
        ·
          refine ⟨20264375202551993573369273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13509583468367995715579515 20264375202551993573369273)
          ·
            refine ⟨15198281401913995180026955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20264375202551993573369273 15198281401913995180026955)
            ·
              refine ⟨22797422102870992770040433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15198281401913995180026955 22797422102870992770040433)
              ·
                refine ⟨17098066577153244577530325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22797422102870992770040433 17098066577153244577530325)
                ·
                  refine ⟨400735935402029169785867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17098066577153244577530325 400735935402029169785867)
                  ·
                    rfl

theorem cell22_3511937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 2, 7].length) (baseStart_3511937 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3511937 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3511937 prefixEnd_3511937 := by exact prefixLift 3511937
  have htrace : WordTrace (prefixWord ++ tailWord_3511937) baseStart_3511937 baseEnd_3511937 := by
    simpa [prefixWord, tailWord_3511937, baseEnd_3511937] using wordTrace_append hprefix tailTrace_3511937
  have hstable : (prefixWord ++ tailWord_3511937).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3511937).length < 2 ^ (prefixWord ++ tailWord_3511937).sum := by decide
  have hdescent : baseEnd_3511937 < baseStart_3511937 := by decide
  rcases family_descends (prefixWord ++ tailWord_3511937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3511984 : List Nat := [2, 1, 1, 1, 2, 1, 7, 2, 1, 4]
def baseStart_3511984 : Nat := 118140960795 + 3511984 * 2 ^ 59
def prefixEnd_3511984 : Nat := 4983230072969 + 3 ^ 40 * 3511984 * 2
def baseEnd_3511984 : Nat := 1202223895266595053432457

theorem tailTrace_3511984 : CollatzResearch.WordTrace tailWord_3511984 prefixEnd_3511984 1202223895266595053432457 := by
  unfold tailWord_3511984
  simp only [CollatzResearch.WordTrace]
  refine ⟨64046289854344620979931503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85395053139126161306575337 64046289854344620979931503)
  ·
    refine ⟨96069434781516931469897255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64046289854344620979931503 96069434781516931469897255)
    ·
      refine ⟨144104152172275397204845883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96069434781516931469897255 144104152172275397204845883)
      ·
        refine ⟨216156228258413095807268825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144104152172275397204845883 216156228258413095807268825)
        ·
          refine ⟨162117171193809821855451619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 216156228258413095807268825 162117171193809821855451619)
          ·
            refine ⟨243175756790714732783177429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162117171193809821855451619 243175756790714732783177429)
            ·
              refine ⟨5699431799782376549605721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 243175756790714732783177429 5699431799782376549605721)
              ·
                refine ⟨4274573849836782412204291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5699431799782376549605721 4274573849836782412204291)
                ·
                  refine ⟨6411860774755173618306437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4274573849836782412204291 6411860774755173618306437)
                  ·
                    refine ⟨1202223895266595053432457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6411860774755173618306437 1202223895266595053432457)
                    ·
                      rfl

theorem cell22_3511984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 7, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 7, 2, 1, 4].length) (baseStart_3511984 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3511984 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3511984 prefixEnd_3511984 := by exact prefixLift 3511984
  have htrace : WordTrace (prefixWord ++ tailWord_3511984) baseStart_3511984 baseEnd_3511984 := by
    simpa [prefixWord, tailWord_3511984, baseEnd_3511984] using wordTrace_append hprefix tailTrace_3511984
  have hstable : (prefixWord ++ tailWord_3511984).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3511984).length < 2 ^ (prefixWord ++ tailWord_3511984).sum := by decide
  have hdescent : baseEnd_3511984 < baseStart_3511984 := by decide
  rcases family_descends (prefixWord ++ tailWord_3511984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3511999 : List Nat := [1, 1, 2, 2, 2, 3, 2, 5, 4]
def baseStart_3511999 : Nat := 118140960795 + 3511999 * 2 ^ 59
def prefixEnd_3511999 : Nat := 4983230072969 + 3 ^ 40 * 3511999 * 2
def baseEnd_3511999 : Nat := 400743010024380004769137

theorem tailTrace_3511999 : CollatzResearch.WordTrace tailWord_3511999 prefixEnd_3511999 400743010024380004769137 := by
  unfold tailWord_3511999
  simp only [CollatzResearch.WordTrace]
  refine ⟨128093126803634899521659051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85395417869089933014439367 128093126803634899521659051)
  ·
    refine ⟨192139690205452349282488577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128093126803634899521659051 192139690205452349282488577)
    ·
      refine ⟨144104767654089261961866433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192139690205452349282488577 144104767654089261961866433)
      ·
        refine ⟨108078575740566946471399825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144104767654089261961866433 108078575740566946471399825)
        ·
          refine ⟨81058931805425209853549869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108078575740566946471399825 81058931805425209853549869)
          ·
            refine ⟨30397099427034453695081201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81058931805425209853549869 30397099427034453695081201)
            ·
              refine ⟨22797824570275840271310901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30397099427034453695081201 22797824570275840271310901)
              ·
                refine ⟨2137296053463360025435397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22797824570275840271310901 2137296053463360025435397)
                ·
                  refine ⟨400743010024380004769137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2137296053463360025435397 400743010024380004769137)
                  ·
                    rfl

theorem cell22_3511999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 5, 4].length) (baseStart_3511999 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3511999 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3511999 prefixEnd_3511999 := by exact prefixLift 3511999
  have htrace : WordTrace (prefixWord ++ tailWord_3511999) baseStart_3511999 baseEnd_3511999 := by
    simpa [prefixWord, tailWord_3511999, baseEnd_3511999] using wordTrace_append hprefix tailTrace_3511999
  have hstable : (prefixWord ++ tailWord_3511999).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3511999).length < 2 ^ (prefixWord ++ tailWord_3511999).sum := by decide
  have hdescent : baseEnd_3511999 < baseStart_3511999 := by decide
  rcases family_descends (prefixWord ++ tailWord_3511999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3512052 : List Nat := [2, 6, 1, 1, 1, 3, 2, 1, 1, 4]
def baseStart_3512052 : Nat := 118140960795 + 3512052 * 2 ^ 59
def prefixEnd_3512052 : Nat := 4983230072969 + 3 ^ 40 * 3512052 * 2
def baseEnd_3512052 : Nat := 1202247173056265542732249

theorem tailTrace_3512052 : CollatzResearch.WordTrace tailWord_3512052 prefixEnd_3512052 1202247173056265542732249 := by
  unfold tailWord_3512052
  simp only [CollatzResearch.WordTrace]
  refine ⟨64047529936221444786669205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85396706581628593048892273 64047529936221444786669205)
  ·
    refine ⟨3002227965760380224375119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 64047529936221444786669205 3002227965760380224375119)
    ·
      refine ⟨4503341948640570336562679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3002227965760380224375119 4503341948640570336562679)
      ·
        refine ⟨6755012922960855504844019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4503341948640570336562679 6755012922960855504844019)
        ·
          refine ⟨10132519384441283257266029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6755012922960855504844019 10132519384441283257266029)
          ·
            refine ⟨3799694769165481221474761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10132519384441283257266029 3799694769165481221474761)
            ·
              refine ⟨2849771076874110916106071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3799694769165481221474761 2849771076874110916106071)
              ·
                refine ⟨4274656615311166374159107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2849771076874110916106071 4274656615311166374159107)
                ·
                  refine ⟨6411984922966749561238661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4274656615311166374159107 6411984922966749561238661)
                  ·
                    refine ⟨1202247173056265542732249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6411984922966749561238661 1202247173056265542732249)
                    ·
                      rfl

theorem cell22_3512052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 2, 1, 1, 4].length) (baseStart_3512052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3512052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3512052 prefixEnd_3512052 := by exact prefixLift 3512052
  have htrace : WordTrace (prefixWord ++ tailWord_3512052) baseStart_3512052 baseEnd_3512052 := by
    simpa [prefixWord, tailWord_3512052, baseEnd_3512052] using wordTrace_append hprefix tailTrace_3512052
  have hstable : (prefixWord ++ tailWord_3512052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3512052).length < 2 ^ (prefixWord ++ tailWord_3512052).sum := by decide
  have hdescent : baseEnd_3512052 < baseStart_3512052 := by decide
  rcases family_descends (prefixWord ++ tailWord_3512052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3512140 : List Nat := [2, 2, 1, 3, 5, 1, 2, 1, 5]
def baseStart_3512140 : Nat := 118140960795 + 3512140 * 2 ^ 59
def prefixEnd_3512140 : Nat := 4983230072969 + 3 ^ 40 * 3512140 * 2
def baseEnd_3512140 : Nat := 400759099084887548843993

theorem tailTrace_3512140 : CollatzResearch.WordTrace tailWord_3512140 prefixEnd_3512140 400759099084887548843993 := by
  unfold tailWord_3512140
  simp only [CollatzResearch.WordTrace]
  refine ⟨64049134748062040301270937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85398846330749387068361249 64049134748062040301270937)
  ·
    refine ⟨48036851061046530225953203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64049134748062040301270937 48036851061046530225953203)
    ·
      refine ⟨72055276591569795338929805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48036851061046530225953203 72055276591569795338929805)
      ·
        refine ⟨27020728721838673252098677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72055276591569795338929805 27020728721838673252098677)
        ·
          refine ⟨2533193317672375617384251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27020728721838673252098677 2533193317672375617384251)
          ·
            refine ⟨3799789976508563426076377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2533193317672375617384251 3799789976508563426076377)
            ·
              refine ⟨2849842482381422569557283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3799789976508563426076377 2849842482381422569557283)
              ·
                refine ⟨4274763723572133854335925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2849842482381422569557283 4274763723572133854335925)
                ·
                  refine ⟨400759099084887548843993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4274763723572133854335925 400759099084887548843993)
                  ·
                    rfl

theorem cell22_3512140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 2, 1, 5].length) (baseStart_3512140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3512140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3512140 prefixEnd_3512140 := by exact prefixLift 3512140
  have htrace : WordTrace (prefixWord ++ tailWord_3512140) baseStart_3512140 baseEnd_3512140 := by
    simpa [prefixWord, tailWord_3512140, baseEnd_3512140] using wordTrace_append hprefix tailTrace_3512140
  have hstable : (prefixWord ++ tailWord_3512140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3512140).length < 2 ^ (prefixWord ++ tailWord_3512140).sum := by decide
  have hdescent : baseEnd_3512140 < baseStart_3512140 := by decide
  rcases family_descends (prefixWord ++ tailWord_3512140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3512181 : List Nat := [1, 3, 4, 1, 1, 1, 1, 4, 2, 4]
def baseStart_3512181 : Nat := 118140960795 + 3512181 * 2 ^ 59
def prefixEnd_3512181 : Nat := 4983230072969 + 3 ^ 40 * 3512181 * 2
def baseEnd_3512181 : Nat := 1202291332392552206256853

theorem tailTrace_3512181 : CollatzResearch.WordTrace tailWord_3512181 prefixEnd_3512181 1202291332392552206256853 := by
  unfold tailWord_3512181
  simp only [CollatzResearch.WordTrace]
  refine ⟨128099764888975544604784397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85399843259317029736522931 128099764888975544604784397)
  ·
    refine ⟨48037411833365829226794149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128099764888975544604784397 48037411833365829226794149)
    ·
      refine ⟨9007014718756092980023903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48037411833365829226794149 9007014718756092980023903)
      ·
        refine ⟨13510522078134139470035855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9007014718756092980023903 13510522078134139470035855)
        ·
          refine ⟨20265783117201209205053783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13510522078134139470035855 20265783117201209205053783)
          ·
            refine ⟨30398674675801813807580675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20265783117201209205053783 30398674675801813807580675)
            ·
              refine ⟨45598012013702720711371013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30398674675801813807580675 45598012013702720711371013)
              ·
                refine ⟨8549627252569260133382065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45598012013702720711371013 8549627252569260133382065)
                ·
                  refine ⟨6412220439426945100036549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8549627252569260133382065 6412220439426945100036549)
                  ·
                    refine ⟨1202291332392552206256853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6412220439426945100036549 1202291332392552206256853)
                    ·
                      rfl

theorem cell22_3512181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 4, 2, 4].length) (baseStart_3512181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3512181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3512181 prefixEnd_3512181 := by exact prefixLift 3512181
  have htrace : WordTrace (prefixWord ++ tailWord_3512181) baseStart_3512181 baseEnd_3512181 := by
    simpa [prefixWord, tailWord_3512181, baseEnd_3512181] using wordTrace_append hprefix tailTrace_3512181
  have hstable : (prefixWord ++ tailWord_3512181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3512181).length < 2 ^ (prefixWord ++ tailWord_3512181).sum := by decide
  have hdescent : baseEnd_3512181 < baseStart_3512181 := by decide
  rcases family_descends (prefixWord ++ tailWord_3512181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3512224 : List Nat := [2, 1, 1, 4, 1, 1, 1, 4, 7]
def baseStart_3512224 : Nat := 118140960795 + 3512224 * 2 ^ 59
def prefixEnd_3512224 : Nat := 4983230072969 + 3 ^ 40 * 3512224 * 2
def baseEnd_3512224 : Nat := 400768684057104809143907

theorem tailTrace_3512224 : CollatzResearch.WordTrace tailWord_3512224 prefixEnd_3512224 400768684057104809143907 := by
  unfold tailWord_3512224
  simp only [CollatzResearch.WordTrace]
  refine ⟨64050666613909881474299863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85400888818546508632399817 64050666613909881474299863)
  ·
    refine ⟨96075999920864822211449795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64050666613909881474299863 96075999920864822211449795)
    ·
      refine ⟨144113999881297233317174693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96075999920864822211449795 144113999881297233317174693)
      ·
        refine ⟨27021374977743231246970255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 144113999881297233317174693 27021374977743231246970255)
        ·
          refine ⟨40532062466614846870455383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27021374977743231246970255 40532062466614846870455383)
          ·
            refine ⟨60798093699922270305683075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40532062466614846870455383 60798093699922270305683075)
            ·
              refine ⟨91197140549883405458524613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60798093699922270305683075 91197140549883405458524613)
              ·
                refine ⟨17099463853103138523473365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 91197140549883405458524613 17099463853103138523473365)
                ·
                  refine ⟨400768684057104809143907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17099463853103138523473365 400768684057104809143907)
                  ·
                    rfl

theorem cell22_3512224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 4, 7].length) (baseStart_3512224 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3512224 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3512224 prefixEnd_3512224 := by exact prefixLift 3512224
  have htrace : WordTrace (prefixWord ++ tailWord_3512224) baseStart_3512224 baseEnd_3512224 := by
    simpa [prefixWord, tailWord_3512224, baseEnd_3512224] using wordTrace_append hprefix tailTrace_3512224
  have hstable : (prefixWord ++ tailWord_3512224).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3512224).length < 2 ^ (prefixWord ++ tailWord_3512224).sum := by decide
  have hdescent : baseEnd_3512224 < baseStart_3512224 := by decide
  rcases family_descends (prefixWord ++ tailWord_3512224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3512239 : List Nat := [1, 1, 2, 1, 2, 2, 3, 1, 4, 5]
def baseStart_3512239 : Nat := 118140960795 + 3512239 * 2 ^ 59
def prefixEnd_3512239 : Nat := 4983230072969 + 3 ^ 40 * 3512239 * 2
def baseEnd_3512239 : Nat := 1202311186977859388306675

theorem tailTrace_3512239 : CollatzResearch.WordTrace tailWord_3512239 prefixEnd_3512239 1202311186977859388306675 := by
  unfold tailWord_3512239
  simp only [CollatzResearch.WordTrace]
  refine ⟨128101880322765420510395771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85401253548510280340263847 128101880322765420510395771)
  ·
    refine ⟨192152820484148130765593657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128101880322765420510395771 192152820484148130765593657)
    ·
      refine ⟨144114615363111098074195243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192152820484148130765593657 144114615363111098074195243)
      ·
        refine ⟨216171923044666647111292865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144114615363111098074195243 216171923044666647111292865)
        ·
          refine ⟨162128942283499985333469649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 216171923044666647111292865 162128942283499985333469649)
          ·
            refine ⟨121596706712624989000102237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162128942283499985333469649 121596706712624989000102237)
            ·
              refine ⟨45598765017234370875038339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 121596706712624989000102237 45598765017234370875038339)
              ·
                refine ⟨68398147525851556312557509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45598765017234370875038339 68398147525851556312557509)
                ·
                  refine ⟨12824652661097166808604533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 68398147525851556312557509 12824652661097166808604533)
                  ·
                    refine ⟨1202311186977859388306675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12824652661097166808604533 1202311186977859388306675)
                    ·
                      rfl

theorem cell22_3512239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 1, 4, 5].length) (baseStart_3512239 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3512239 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3512239 prefixEnd_3512239 := by exact prefixLift 3512239
  have htrace : WordTrace (prefixWord ++ tailWord_3512239) baseStart_3512239 baseEnd_3512239 := by
    simpa [prefixWord, tailWord_3512239, baseEnd_3512239] using wordTrace_append hprefix tailTrace_3512239
  have hstable : (prefixWord ++ tailWord_3512239).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3512239).length < 2 ^ (prefixWord ++ tailWord_3512239).sum := by decide
  have hdescent : baseEnd_3512239 < baseStart_3512239 := by decide
  rcases family_descends (prefixWord ++ tailWord_3512239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3512241 : List Nat := [1, 2, 2, 4, 2, 2, 1, 1, 7]
def baseStart_3512241 : Nat := 118140960795 + 3512241 * 2 ^ 59
def prefixEnd_3512241 : Nat := 4983230072969 + 3 ^ 40 * 3512241 * 2
def baseEnd_3512241 : Nat := 400770623872910683252223

theorem tailTrace_3512241 : CollatzResearch.WordTrace tailWord_3512241 prefixEnd_3512241 400770623872910683252223 := by
  unfold tailWord_3512241
  simp only [CollatzResearch.WordTrace]
  refine ⟨128101953268758174851968577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85401302179172116567979051 128101953268758174851968577)
  ·
    refine ⟨96076464951568631138976433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128101953268758174851968577 96076464951568631138976433)
    ·
      refine ⟨72057348713676473354232325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96076464951568631138976433 72057348713676473354232325)
      ·
        refine ⟨13510752883814338753918561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72057348713676473354232325 13510752883814338753918561)
        ·
          refine ⟨10133064662860754065438921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13510752883814338753918561 10133064662860754065438921)
          ·
            refine ⟨7599798497145565549079191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10133064662860754065438921 7599798497145565549079191)
            ·
              refine ⟨11399697745718348323618787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7599798497145565549079191 11399697745718348323618787)
              ·
                refine ⟨17099546618577522485428181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11399697745718348323618787 17099546618577522485428181)
                ·
                  refine ⟨400770623872910683252223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17099546618577522485428181 400770623872910683252223)
                  ·
                    rfl

theorem cell22_3512241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 1, 7].length) (baseStart_3512241 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3512241 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3512241 prefixEnd_3512241 := by exact prefixLift 3512241
  have htrace : WordTrace (prefixWord ++ tailWord_3512241) baseStart_3512241 baseEnd_3512241 := by
    simpa [prefixWord, tailWord_3512241, baseEnd_3512241] using wordTrace_append hprefix tailTrace_3512241
  have hstable : (prefixWord ++ tailWord_3512241).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3512241).length < 2 ^ (prefixWord ++ tailWord_3512241).sum := by decide
  have hdescent : baseEnd_3512241 < baseStart_3512241 := by decide
  rcases family_descends (prefixWord ++ tailWord_3512241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3512245 : List Nat := [1, 3, 3, 2, 1, 2, 2, 4, 1, 3]
def baseStart_3512245 : Nat := 118140960795 + 3512245 * 2 ^ 59
def prefixEnd_3512245 : Nat := 4983230072969 + 3 ^ 40 * 3512245 * 2
def baseEnd_3512245 : Nat := 1202313240900477372656657

theorem tailTrace_3512245 : CollatzResearch.WordTrace tailWord_3512245 prefixEnd_3512245 1202313240900477372656657 := by
  unfold tailWord_3512245
  simp only [CollatzResearch.WordTrace]
  refine ⟨128102099160743683535114189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85401399440495789023409459 128102099160743683535114189)
  ·
    refine ⟨48038287185278881325667821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128102099160743683535114189 48038287185278881325667821)
    ·
      refine ⟨18014357694479580497125433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48038287185278881325667821 18014357694479580497125433)
      ·
        refine ⟨13510768270859685372844075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18014357694479580497125433 13510768270859685372844075)
        ·
          refine ⟨20266152406289528059266113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13510768270859685372844075 20266152406289528059266113)
          ·
            refine ⟨15199614304717146044449585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20266152406289528059266113 15199614304717146044449585)
            ·
              refine ⟨11399710728537859533337189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15199614304717146044449585 11399710728537859533337189)
              ·
                refine ⟨2137445761600848662500723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11399710728537859533337189 2137445761600848662500723)
                ·
                  refine ⟨3206168642401272993751085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2137445761600848662500723 3206168642401272993751085)
                  ·
                    refine ⟨1202313240900477372656657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3206168642401272993751085 1202313240900477372656657)
                    ·
                      rfl

theorem cell22_3512245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 4, 1, 3].length) (baseStart_3512245 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3512245 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3512245 prefixEnd_3512245 := by exact prefixLift 3512245
  have htrace : WordTrace (prefixWord ++ tailWord_3512245) baseStart_3512245 baseEnd_3512245 := by
    simpa [prefixWord, tailWord_3512245, baseEnd_3512245] using wordTrace_append hprefix tailTrace_3512245
  have hstable : (prefixWord ++ tailWord_3512245).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3512245).length < 2 ^ (prefixWord ++ tailWord_3512245).sum := by decide
  have hdescent : baseEnd_3512245 < baseStart_3512245 := by decide
  rcases family_descends (prefixWord ++ tailWord_3512245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3512316 : List Nat := [2, 2, 2, 1, 2, 2, 1, 2, 4, 4]
def baseStart_3512316 : Nat := 118140960795 + 3512316 * 2 ^ 59
def prefixEnd_3512316 : Nat := 4983230072969 + 3 ^ 40 * 3512316 * 2
def baseEnd_3512316 : Nat := 1202337545651456854131439

theorem tailTrace_3512316 : CollatzResearch.WordTrace tailWord_3512316 prefixEnd_3512316 1202337545651456854131439 := by
  unfold tailWord_3512316
  simp only [CollatzResearch.WordTrace]
  refine ⟨64052344371743231330474401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85403125828990975107299201 64052344371743231330474401)
  ·
    refine ⟨48039258278807423497855801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64052344371743231330474401 48039258278807423497855801)
    ·
      refine ⟨36029443709105567623391851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48039258278807423497855801 36029443709105567623391851)
      ·
        refine ⟨54044165563658351435087777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36029443709105567623391851 54044165563658351435087777)
        ·
          refine ⟨40533124172743763576315833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54044165563658351435087777 40533124172743763576315833)
          ·
            refine ⟨30399843129557822682236875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40533124172743763576315833 30399843129557822682236875)
            ·
              refine ⟨45599764694336734023355313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30399843129557822682236875 45599764694336734023355313)
              ·
                refine ⟨34199823520752550517516485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45599764694336734023355313 34199823520752550517516485)
                ·
                  refine ⟨6412466910141103222034341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34199823520752550517516485 6412466910141103222034341)
                  ·
                    refine ⟨1202337545651456854131439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6412466910141103222034341 1202337545651456854131439)
                    ·
                      rfl

theorem cell22_3512316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 2, 4, 4].length) (baseStart_3512316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3512316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3512316 prefixEnd_3512316 := by exact prefixLift 3512316
  have htrace : WordTrace (prefixWord ++ tailWord_3512316) baseStart_3512316 baseEnd_3512316 := by
    simpa [prefixWord, tailWord_3512316, baseEnd_3512316] using wordTrace_append hprefix tailTrace_3512316
  have hstable : (prefixWord ++ tailWord_3512316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3512316).length < 2 ^ (prefixWord ++ tailWord_3512316).sum := by decide
  have hdescent : baseEnd_3512316 < baseStart_3512316 := by decide
  rcases family_descends (prefixWord ++ tailWord_3512316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3512391 : List Nat := [1, 1, 4, 1, 3, 1, 1, 2, 1, 7]
def baseStart_3512391 : Nat := 118140960795 + 3512391 * 2 ^ 59
def prefixEnd_3512391 : Nat := 4983230072969 + 3 ^ 40 * 3512391 * 2
def baseEnd_3512391 : Nat := 1202363219684181658506209

theorem tailTrace_3512391 : CollatzResearch.WordTrace tailWord_3512391 prefixEnd_3512391 1202363219684181658506209 := by
  unfold tailWord_3512391
  simp only [CollatzResearch.WordTrace]
  refine ⟨128107424218214750469929027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85404949478809833646619351 128107424218214750469929027)
  ·
    refine ⟨192161136327322125704893541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128107424218214750469929027 192161136327322125704893541)
    ·
      refine ⟨36030213061372898569667539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 192161136327322125704893541 36030213061372898569667539)
      ·
        refine ⟨54045319592059347854501309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36030213061372898569667539 54045319592059347854501309)
        ·
          refine ⟨20266994847022255445437991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54045319592059347854501309 20266994847022255445437991)
          ·
            refine ⟨30400492270533383168156987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20266994847022255445437991 30400492270533383168156987)
            ·
              refine ⟨45600738405800074752235481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30400492270533383168156987 45600738405800074752235481)
              ·
                refine ⟨34200553804350056064176611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45600738405800074752235481 34200553804350056064176611)
                ·
                  refine ⟨51300830706525084096264917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34200553804350056064176611 51300830706525084096264917)
                  ·
                    refine ⟨1202363219684181658506209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51300830706525084096264917 1202363219684181658506209)
                    ·
                      rfl

theorem cell22_3512391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 2, 1, 7].length) (baseStart_3512391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3512391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3512391 prefixEnd_3512391 := by exact prefixLift 3512391
  have htrace : WordTrace (prefixWord ++ tailWord_3512391) baseStart_3512391 baseEnd_3512391 := by
    simpa [prefixWord, tailWord_3512391, baseEnd_3512391] using wordTrace_append hprefix tailTrace_3512391
  have hstable : (prefixWord ++ tailWord_3512391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3512391).length < 2 ^ (prefixWord ++ tailWord_3512391).sum := by decide
  have hdescent : baseEnd_3512391 < baseStart_3512391 := by decide
  rcases family_descends (prefixWord ++ tailWord_3512391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3512455 : List Nat := [1, 1, 4, 2, 1, 1, 5, 3, 4]
def baseStart_3512455 : Nat := 118140960795 + 3512455 * 2 ^ 59
def prefixEnd_3512455 : Nat := 4983230072969 + 3 ^ 40 * 3512455 * 2
def baseEnd_3512455 : Nat := 400795042730702274968671

theorem tailTrace_3512455 : CollatzResearch.WordTrace tailWord_3512455 prefixEnd_3512455 400795042730702274968671 := by
  unfold tailWord_3512455
  simp only [CollatzResearch.WordTrace]
  refine ⟨128109758489982889400258819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85406505659988592933505879 128109758489982889400258819)
  ·
    refine ⟨192164637734974334100388229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128109758489982889400258819 192164637734974334100388229)
    ·
      refine ⟨36030869575307687643822793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 192164637734974334100388229 36030869575307687643822793)
      ·
        refine ⟨27023152181480765732867095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36030869575307687643822793 27023152181480765732867095)
        ·
          refine ⟨40534728272221148599300643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27023152181480765732867095 40534728272221148599300643)
          ·
            refine ⟨60802092408331722898950965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40534728272221148599300643 60802092408331722898950965)
            ·
              refine ⟨5700196163281099021776653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 60802092408331722898950965 5700196163281099021776653)
              ·
                refine ⟨2137573561230412133166245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5700196163281099021776653 2137573561230412133166245)
                ·
                  refine ⟨400795042730702274968671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2137573561230412133166245 400795042730702274968671)
                  ·
                    rfl

theorem cell22_3512455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 5, 3, 4].length) (baseStart_3512455 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3512455 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3512455 prefixEnd_3512455 := by exact prefixLift 3512455
  have htrace : WordTrace (prefixWord ++ tailWord_3512455) baseStart_3512455 baseEnd_3512455 := by
    simpa [prefixWord, tailWord_3512455, baseEnd_3512455] using wordTrace_append hprefix tailTrace_3512455
  have hstable : (prefixWord ++ tailWord_3512455).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3512455).length < 2 ^ (prefixWord ++ tailWord_3512455).sum := by decide
  have hdescent : baseEnd_3512455 < baseStart_3512455 := by decide
  rcases family_descends (prefixWord ++ tailWord_3512455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3512472 : List Nat := [2, 1, 2, 4, 4, 1, 1, 1, 6]
def baseStart_3512472 : Nat := 118140960795 + 3512472 * 2 ^ 59
def prefixEnd_3512472 : Nat := 4983230072969 + 3 ^ 40 * 3512472 * 2
def baseEnd_3512472 : Nat := 400796982546508149076987

theorem tailTrace_3512472 : CollatzResearch.WordTrace tailWord_3512472 prefixEnd_3512472 400796982546508149076987 := by
  unfold tailWord_3512472
  simp only [CollatzResearch.WordTrace]
  refine ⟨64055189265460650651813835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85406919020614200869085113 64055189265460650651813835)
  ·
    refine ⟨96082783898190975977720753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64055189265460650651813835 96082783898190975977720753)
    ·
      refine ⟨72062087923643231983290565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96082783898190975977720753 72062087923643231983290565)
      ·
        refine ⟨13511641485683105996866981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72062087923643231983290565 13511641485683105996866981)
        ·
          refine ⟨2533432778565582374412559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13511641485683105996866981 2533432778565582374412559)
          ·
            refine ⟨3800149167848373561618839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2533432778565582374412559 3800149167848373561618839)
            ·
              refine ⟨5700223751772560342428259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3800149167848373561618839 5700223751772560342428259)
              ·
                refine ⟨8550335627658840513642389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5700223751772560342428259 8550335627658840513642389)
                ·
                  refine ⟨400796982546508149076987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8550335627658840513642389 400796982546508149076987)
                  ·
                    rfl

theorem cell22_3512472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 1, 1, 6].length) (baseStart_3512472 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3512472 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3512472 prefixEnd_3512472 := by exact prefixLift 3512472
  have htrace : WordTrace (prefixWord ++ tailWord_3512472) baseStart_3512472 baseEnd_3512472 := by
    simpa [prefixWord, tailWord_3512472, baseEnd_3512472] using wordTrace_append hprefix tailTrace_3512472
  have hstable : (prefixWord ++ tailWord_3512472).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3512472).length < 2 ^ (prefixWord ++ tailWord_3512472).sum := by decide
  have hdescent : baseEnd_3512472 < baseStart_3512472 := by decide
  rcases family_descends (prefixWord ++ tailWord_3512472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3512575 : List Nat := [1, 1, 2, 2, 1, 4, 3, 3, 1, 4]
def baseStart_3512575 : Nat := 118140960795 + 3512575 * 2 ^ 59
def prefixEnd_3512575 : Nat := 4983230072969 + 3 ^ 40 * 3512575 * 2
def baseEnd_3512575 : Nat := 1202426206644466511905645

theorem tailTrace_3512575 : CollatzResearch.WordTrace tailWord_3512575 prefixEnd_3512575 1202426206644466511905645 := by
  unfold tailWord_3512575
  simp only [CollatzResearch.WordTrace]
  refine ⟨128114135249548149894627179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85409423499698766596418119 128114135249548149894627179)
  ·
    refine ⟨192171202874322224841940769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128114135249548149894627179 192171202874322224841940769)
    ·
      refine ⟨144128402155741668631455577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192171202874322224841940769 144128402155741668631455577)
      ·
        refine ⟨108096301616806251473591683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144128402155741668631455577 108096301616806251473591683)
        ·
          refine ⟨162144452425209377210387525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108096301616806251473591683 162144452425209377210387525)
          ·
            refine ⟨30402084829726758226947661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 162144452425209377210387525 30402084829726758226947661)
            ·
              refine ⟨11400781811147534335105373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30402084829726758226947661 11400781811147534335105373)
              ·
                refine ⟨4275293179180325375664515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11400781811147534335105373 4275293179180325375664515)
                ·
                  refine ⟨6412939768770488063496773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4275293179180325375664515 6412939768770488063496773)
                  ·
                    refine ⟨1202426206644466511905645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6412939768770488063496773 1202426206644466511905645)
                    ·
                      rfl

theorem cell22_3512575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 3, 1, 4].length) (baseStart_3512575 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3512575 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3512575 prefixEnd_3512575 := by exact prefixLift 3512575
  have htrace : WordTrace (prefixWord ++ tailWord_3512575) baseStart_3512575 baseEnd_3512575 := by
    simpa [prefixWord, tailWord_3512575, baseEnd_3512575] using wordTrace_append hprefix tailTrace_3512575
  have hstable : (prefixWord ++ tailWord_3512575).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3512575).length < 2 ^ (prefixWord ++ tailWord_3512575).sum := by decide
  have hdescent : baseEnd_3512575 < baseStart_3512575 := by decide
  rcases family_descends (prefixWord ++ tailWord_3512575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3512590 : List Nat := [4, 1, 1, 2, 1, 2, 4, 1, 6]
def baseStart_3512590 : Nat := 118140960795 + 3512590 * 2 ^ 59
def prefixEnd_3512590 : Nat := 4983230072969 + 3 ^ 40 * 3512590 * 2
def baseEnd_3512590 : Nat := 400810447150337157593533

theorem tailTrace_3512590 : CollatzResearch.WordTrace tailWord_3512590 prefixEnd_3512590 400810447150337157593533 := by
  unfold tailWord_3512590
  simp only [CollatzResearch.WordTrace]
  refine ⟨16014335293061725932052903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85409788229662538304282149 16014335293061725932052903)
  ·
    refine ⟨24021502939592588898079355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16014335293061725932052903 24021502939592588898079355)
    ·
      refine ⟨36032254409388883347119033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24021502939592588898079355 36032254409388883347119033)
      ·
        refine ⟨27024190807041662510339275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36032254409388883347119033 27024190807041662510339275)
        ·
          refine ⟨40536286210562493765508913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27024190807041662510339275 40536286210562493765508913)
          ·
            refine ⟨30402214657921870324131685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40536286210562493765508913 30402214657921870324131685)
            ·
              refine ⟨5700415248360350685774691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30402214657921870324131685 5700415248360350685774691)
              ·
                refine ⟨8550622872540526028662037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5700415248360350685774691 8550622872540526028662037)
                ·
                  refine ⟨400810447150337157593533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8550622872540526028662037 400810447150337157593533)
                  ·
                    rfl

theorem cell22_3512590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 4, 1, 6].length) (baseStart_3512590 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3512590 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3512590 prefixEnd_3512590 := by exact prefixLift 3512590
  have htrace : WordTrace (prefixWord ++ tailWord_3512590) baseStart_3512590 baseEnd_3512590 := by
    simpa [prefixWord, tailWord_3512590, baseEnd_3512590] using wordTrace_append hprefix tailTrace_3512590
  have hstable : (prefixWord ++ tailWord_3512590).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3512590).length < 2 ^ (prefixWord ++ tailWord_3512590).sum := by decide
  have hdescent : baseEnd_3512590 < baseStart_3512590 := by decide
  rcases family_descends (prefixWord ++ tailWord_3512590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3512603 : List Nat := [1, 1, 1, 1, 1, 1, 7, 2, 1, 6]
def baseStart_3512603 : Nat := 118140960795 + 3512603 * 2 ^ 59
def prefixEnd_3512603 : Nat := 4983230072969 + 3 ^ 40 * 3512603 * 2
def baseEnd_3512603 : Nat := 1202435791616683772205559

theorem tailTrace_3512603 : CollatzResearch.WordTrace tailWord_3512603 prefixEnd_3512603 1202435791616683772205559 := by
  unfold tailWord_3512603
  simp only [CollatzResearch.WordTrace]
  refine ⟨128115156493446710676646463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85410104328964473784430975 128115156493446710676646463)
  ·
    refine ⟨192172734740170066014969695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128115156493446710676646463 192172734740170066014969695)
    ·
      refine ⟨288259102110255099022454543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192172734740170066014969695 288259102110255099022454543)
      ·
        refine ⟨432388653165382648533681815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 288259102110255099022454543 432388653165382648533681815)
        ·
          refine ⟨648582979748073972800522723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 432388653165382648533681815 648582979748073972800522723)
          ·
            refine ⟨972874469622110959200784085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 648582979748073972800522723 972874469622110959200784085)
            ·
              refine ⟨22801745381768225606268377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 972874469622110959200784085 22801745381768225606268377)
              ·
                refine ⟨17101309036326169204701283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22801745381768225606268377 17101309036326169204701283)
                ·
                  refine ⟨25651963554489253807051925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17101309036326169204701283 25651963554489253807051925)
                  ·
                    refine ⟨1202435791616683772205559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25651963554489253807051925 1202435791616683772205559)
                    ·
                      rfl

theorem cell22_3512603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 2, 1, 6].length) (baseStart_3512603 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3512603 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3512603 prefixEnd_3512603 := by exact prefixLift 3512603
  have htrace : WordTrace (prefixWord ++ tailWord_3512603) baseStart_3512603 baseEnd_3512603 := by
    simpa [prefixWord, tailWord_3512603, baseEnd_3512603] using wordTrace_append hprefix tailTrace_3512603
  have hstable : (prefixWord ++ tailWord_3512603).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3512603).length < 2 ^ (prefixWord ++ tailWord_3512603).sum := by decide
  have hdescent : baseEnd_3512603 < baseStart_3512603 := by decide
  rcases family_descends (prefixWord ++ tailWord_3512603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3512641 : List Nat := [1, 2, 5, 2, 2, 1, 3, 2, 4]
def baseStart_3512641 : Nat := 118140960795 + 3512641 * 2 ^ 59
def prefixEnd_3512641 : Nat := 4983230072969 + 3 ^ 40 * 3512641 * 2
def baseEnd_3512641 : Nat := 400816266597754779918481

theorem tailTrace_3512641 : CollatzResearch.WordTrace tailWord_3512641 prefixEnd_3512641 400816266597754779918481 := by
  unfold tailWord_3512641
  simp only [CollatzResearch.WordTrace]
  refine ⟨128116542467309043166529777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85411028311539362111019851 128116542467309043166529777)
  ·
    refine ⟨96087406850481782374897333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128116542467309043166529777 96087406850481782374897333)
    ·
      refine ⟨9008194392232667097646625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 96087406850481782374897333 9008194392232667097646625)
      ·
        refine ⟨6756145794174500323234969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9008194392232667097646625 6756145794174500323234969)
        ·
          refine ⟨5067109345630875242426227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6756145794174500323234969 5067109345630875242426227)
          ·
            refine ⟨7600664018446312863639341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5067109345630875242426227 7600664018446312863639341)
            ·
              refine ⟨2850249006917367323864753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7600664018446312863639341 2850249006917367323864753)
              ·
                refine ⟨2137686755188025492898565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2850249006917367323864753 2137686755188025492898565)
                ·
                  refine ⟨400816266597754779918481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2137686755188025492898565 400816266597754779918481)
                  ·
                    rfl

theorem cell22_3512641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 3, 2, 4].length) (baseStart_3512641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3512641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3512641 prefixEnd_3512641 := by exact prefixLift 3512641
  have htrace : WordTrace (prefixWord ++ tailWord_3512641) baseStart_3512641 baseEnd_3512641 := by
    simpa [prefixWord, tailWord_3512641, baseEnd_3512641] using wordTrace_append hprefix tailTrace_3512641
  have hstable : (prefixWord ++ tailWord_3512641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3512641).length < 2 ^ (prefixWord ++ tailWord_3512641).sum := by decide
  have hdescent : baseEnd_3512641 < baseStart_3512641 := by decide
  rcases family_descends (prefixWord ++ tailWord_3512641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3512701 : List Nat := [1, 4, 1, 1, 2, 3, 4, 2, 1, 3]
def baseStart_3512701 : Nat := 118140960795 + 3512701 * 2 ^ 59
def prefixEnd_3512701 : Nat := 4983230072969 + 3 ^ 40 * 3512701 * 2
def baseEnd_3512701 : Nat := 1202469339019444183255259

theorem tailTrace_3512701 : CollatzResearch.WordTrace tailWord_3512701 prefixEnd_3512701 1202469339019444183255259 := by
  unfold tailWord_3512701
  simp only [CollatzResearch.WordTrace]
  refine ⟨128118730847091673413713957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85412487231394448942475971 128118730847091673413713957)
  ·
    refine ⟨24022262033829688765071367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 128118730847091673413713957 24022262033829688765071367)
    ·
      refine ⟨36033393050744533147607051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24022262033829688765071367 36033393050744533147607051)
      ·
        refine ⟨54050089576116799721410577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36033393050744533147607051 54050089576116799721410577)
        ·
          refine ⟨40537567182087599791057933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54050089576116799721410577 40537567182087599791057933)
          ·
            refine ⟨15201587693282849921646725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40537567182087599791057933 15201587693282849921646725)
            ·
              refine ⟨2850297692490534360308761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15201587693282849921646725 2850297692490534360308761)
              ·
                refine ⟨2137723269367900770231571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2850297692490534360308761 2137723269367900770231571)
                ·
                  refine ⟨3206584904051851155347357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2137723269367900770231571 3206584904051851155347357)
                  ·
                    refine ⟨1202469339019444183255259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3206584904051851155347357 1202469339019444183255259)
                    ·
                      rfl

theorem cell22_3512701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 4, 2, 1, 3].length) (baseStart_3512701 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3512701 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3512701 prefixEnd_3512701 := by exact prefixLift 3512701
  have htrace : WordTrace (prefixWord ++ tailWord_3512701) baseStart_3512701 baseEnd_3512701 := by
    simpa [prefixWord, tailWord_3512701, baseEnd_3512701] using wordTrace_append hprefix tailTrace_3512701
  have hstable : (prefixWord ++ tailWord_3512701).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3512701).length < 2 ^ (prefixWord ++ tailWord_3512701).sum := by decide
  have hdescent : baseEnd_3512701 < baseStart_3512701 := by decide
  rcases family_descends (prefixWord ++ tailWord_3512701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3512967 : List Nat := [1, 1, 4, 2, 1, 2, 1, 1, 9]
def baseStart_3512967 : Nat := 118140960795 + 3512967 * 2 ^ 59
def prefixEnd_3512967 : Nat := 4983230072969 + 3 ^ 40 * 3512967 * 2
def baseEnd_3512967 : Nat := 400853465418502718701481

theorem tailTrace_3512967 : CollatzResearch.WordTrace tailWord_3512967 prefixEnd_3512967 400853465418502718701481 := by
  unfold tailWord_3512967
  simp only [CollatzResearch.WordTrace]
  refine ⟨128128432664128000842897155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85418955109418667228598103 128128432664128000842897155)
  ·
    refine ⟨192192648996192001264345733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128128432664128000842897155 192192648996192001264345733)
    ·
      refine ⟨36036121686786000237064825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 192192648996192001264345733 36036121686786000237064825)
      ·
        refine ⟨27027091265089500177798619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36036121686786000237064825 27027091265089500177798619)
        ·
          refine ⟨40540636897634250266697929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27027091265089500177798619 40540636897634250266697929)
          ·
            refine ⟨30405477673225687700023447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40540636897634250266697929 30405477673225687700023447)
            ·
              refine ⟨45608216509838531550035171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30405477673225687700023447 45608216509838531550035171)
              ·
                refine ⟨68412324764757797325052757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45608216509838531550035171 68412324764757797325052757)
                ·
                  refine ⟨400853465418502718701481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 68412324764757797325052757 400853465418502718701481)
                  ·
                    rfl

theorem cell22_3512967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 1, 9].length) (baseStart_3512967 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3512967 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3512967 prefixEnd_3512967 := by exact prefixLift 3512967
  have htrace : WordTrace (prefixWord ++ tailWord_3512967) baseStart_3512967 baseEnd_3512967 := by
    simpa [prefixWord, tailWord_3512967, baseEnd_3512967] using wordTrace_append hprefix tailTrace_3512967
  have hstable : (prefixWord ++ tailWord_3512967).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3512967).length < 2 ^ (prefixWord ++ tailWord_3512967).sum := by decide
  have hdescent : baseEnd_3512967 < baseStart_3512967 := by decide
  rcases family_descends (prefixWord ++ tailWord_3512967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3512971 : List Nat := [1, 1, 1, 1, 4, 1, 2, 7, 1, 3]
def baseStart_3512971 : Nat := 118140960795 + 3512971 * 2 ^ 59
def prefixEnd_3512971 : Nat := 4983230072969 + 3 ^ 40 * 3512971 * 2
def baseEnd_3512971 : Nat := 1202561765537253479004431

theorem tailTrace_3512971 : CollatzResearch.WordTrace tailWord_3512971 prefixEnd_3512971 1202561765537253479004431 := by
  unfold tailWord_3512971
  simp only [CollatzResearch.WordTrace]
  refine ⟨128128578556113509526042767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85419052370742339684028511 128128578556113509526042767)
  ·
    refine ⟨192192867834170264289064151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128128578556113509526042767 192192867834170264289064151)
    ·
      refine ⟨288289301751255396433596227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192192867834170264289064151 288289301751255396433596227)
      ·
        refine ⟨432433952626883094650394341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 288289301751255396433596227 432433952626883094650394341)
        ·
          refine ⟨81081366117540580246948939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 432433952626883094650394341 81081366117540580246948939)
          ·
            refine ⟨121622049176310870370423409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81081366117540580246948939 121622049176310870370423409)
            ·
              refine ⟨91216536882233152777817557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121622049176310870370423409 91216536882233152777817557)
              ·
                refine ⟨2137887583177339518230099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 91216536882233152777817557 2137887583177339518230099)
                ·
                  refine ⟨3206831374766009277345149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2137887583177339518230099 3206831374766009277345149)
                  ·
                    refine ⟨1202561765537253479004431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3206831374766009277345149 1202561765537253479004431)
                    ·
                      rfl

theorem cell22_3512971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 7, 1, 3].length) (baseStart_3512971 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3512971 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3512971 prefixEnd_3512971 := by exact prefixLift 3512971
  have htrace : WordTrace (prefixWord ++ tailWord_3512971) baseStart_3512971 baseEnd_3512971 := by
    simpa [prefixWord, tailWord_3512971, baseEnd_3512971] using wordTrace_append hprefix tailTrace_3512971
  have hstable : (prefixWord ++ tailWord_3512971).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3512971).length < 2 ^ (prefixWord ++ tailWord_3512971).sum := by decide
  have hdescent : baseEnd_3512971 < baseStart_3512971 := by decide
  rcases family_descends (prefixWord ++ tailWord_3512971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3512984 : List Nat := [2, 1, 2, 4, 1, 1, 2, 4, 5]
def baseStart_3512984 : Nat := 118140960795 + 3512984 * 2 ^ 59
def prefixEnd_3512984 : Nat := 4983230072969 + 3 ^ 40 * 3512984 * 2
def baseEnd_3512984 : Nat := 400855405234308592809797

theorem tailTrace_3512984 : CollatzResearch.WordTrace tailWord_3512984 prefixEnd_3512984 400855405234308592809797 := by
  unfold tailWord_3512984
  simp only [CollatzResearch.WordTrace]
  refine ⟨64064526352533206373133003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85419368470044275164177337 64064526352533206373133003)
  ·
    refine ⟨96096789528799809559699505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64064526352533206373133003 96096789528799809559699505)
    ·
      refine ⟨72072592146599857169774629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96096789528799809559699505 72072592146599857169774629)
      ·
        refine ⟨13513611027487473219332743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72072592146599857169774629 13513611027487473219332743)
        ·
          refine ⟨20270416541231209828999115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13513611027487473219332743 20270416541231209828999115)
          ·
            refine ⟨30405624811846814743498673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20270416541231209828999115 30405624811846814743498673)
            ·
              refine ⟨22804218608885111057624005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30405624811846814743498673 22804218608885111057624005)
              ·
                refine ⟨4275790989165958323304501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22804218608885111057624005 4275790989165958323304501)
                ·
                  refine ⟨400855405234308592809797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4275790989165958323304501 400855405234308592809797)
                  ·
                    rfl

theorem cell22_3512984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 4, 5].length) (baseStart_3512984 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3512984 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3512984 prefixEnd_3512984 := by exact prefixLift 3512984
  have htrace : WordTrace (prefixWord ++ tailWord_3512984) baseStart_3512984 baseEnd_3512984 := by
    simpa [prefixWord, tailWord_3512984, baseEnd_3512984] using wordTrace_append hprefix tailTrace_3512984
  have hstable : (prefixWord ++ tailWord_3512984).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3512984).length < 2 ^ (prefixWord ++ tailWord_3512984).sum := by decide
  have hdescent : baseEnd_3512984 < baseStart_3512984 := by decide
  rcases family_descends (prefixWord ++ tailWord_3512984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3512988 : List Nat := [2, 2, 3, 2, 2, 3, 1, 1, 3, 3]
def baseStart_3512988 : Nat := 118140960795 + 3512988 * 2 ^ 59
def prefixEnd_3512988 : Nat := 4983230072969 + 3 ^ 40 * 3512988 * 2
def baseEnd_3512988 : Nat := 1202567584984671101329379

theorem tailTrace_3512988 : CollatzResearch.WordTrace tailWord_3512988 prefixEnd_3512988 1202567584984671101329379 := by
  unfold tailWord_3512988
  simp only [CollatzResearch.WordTrace]
  refine ⟨64064599298525960714705809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85419465731367947619607745 64064599298525960714705809)
  ·
    refine ⟨48048449473894470536029357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64064599298525960714705809 48048449473894470536029357)
    ·
      refine ⟨18018168552710426451011009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48048449473894470536029357 18018168552710426451011009)
      ·
        refine ⟨13513626414532819838258257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18018168552710426451011009 13513626414532819838258257)
        ·
          refine ⟨10135219810899614878693693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13513626414532819838258257 10135219810899614878693693)
          ·
            refine ⟨3800707429087355579510135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10135219810899614878693693 3800707429087355579510135)
            ·
              refine ⟨5701061143631033369265203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3800707429087355579510135 5701061143631033369265203)
              ·
                refine ⟨8551591715446550053897805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5701061143631033369265203 8551591715446550053897805)
                ·
                  refine ⟨3206846893292456270211677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8551591715446550053897805 3206846893292456270211677)
                  ·
                    refine ⟨1202567584984671101329379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3206846893292456270211677 1202567584984671101329379)
                    ·
                      rfl

theorem cell22_3512988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 1, 1, 3, 3].length) (baseStart_3512988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3512988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3512988 prefixEnd_3512988 := by exact prefixLift 3512988
  have htrace : WordTrace (prefixWord ++ tailWord_3512988) baseStart_3512988 baseEnd_3512988 := by
    simpa [prefixWord, tailWord_3512988, baseEnd_3512988] using wordTrace_append hprefix tailTrace_3512988
  have hstable : (prefixWord ++ tailWord_3512988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3512988).length < 2 ^ (prefixWord ++ tailWord_3512988).sum := by decide
  have hdescent : baseEnd_3512988 < baseStart_3512988 := by decide
  rcases family_descends (prefixWord ++ tailWord_3512988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3512997 : List Nat := [1, 3, 1, 2, 1, 2, 1, 1, 2, 8]
def baseStart_3512997 : Nat := 118140960795 + 3512997 * 2 ^ 59
def prefixEnd_3512997 : Nat := 4983230072969 + 3 ^ 40 * 3512997 * 2
def baseEnd_3512997 : Nat := 1202570665868598077854351

theorem tailTrace_3512997 : CollatzResearch.WordTrace tailWord_3512997 prefixEnd_3512997 1202570665868598077854351 := by
  unfold tailWord_3512997
  simp only [CollatzResearch.WordTrace]
  refine ⟨128129526854019315966489245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85419684569346210644326163 128129526854019315966489245)
  ·
    refine ⟨48048572570257243487433467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128129526854019315966489245 48048572570257243487433467)
    ·
      refine ⟨72072858855385865231150201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48048572570257243487433467 72072858855385865231150201)
      ·
        refine ⟨54054644141539398923362651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72072858855385865231150201 54054644141539398923362651)
        ·
          refine ⟨81081966212309098385043977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54054644141539398923362651 81081966212309098385043977)
          ·
            refine ⟨60811474659231823788782983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81081966212309098385043977 60811474659231823788782983)
            ·
              refine ⟨91217211988847735683174475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60811474659231823788782983 91217211988847735683174475)
              ·
                refine ⟨136825817983271603524761713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91217211988847735683174475 136825817983271603524761713)
                ·
                  refine ⟨102619363487453702643571285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 136825817983271603524761713 102619363487453702643571285)
                  ·
                    refine ⟨1202570665868598077854351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 102619363487453702643571285 1202570665868598077854351)
                    ·
                      rfl

theorem cell22_3512997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 1, 2, 8].length) (baseStart_3512997 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3512997 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3512997 prefixEnd_3512997 := by exact prefixLift 3512997
  have htrace : WordTrace (prefixWord ++ tailWord_3512997) baseStart_3512997 baseEnd_3512997 := by
    simpa [prefixWord, tailWord_3512997, baseEnd_3512997] using wordTrace_append hprefix tailTrace_3512997
  have hstable : (prefixWord ++ tailWord_3512997).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3512997).length < 2 ^ (prefixWord ++ tailWord_3512997).sum := by decide
  have hdescent : baseEnd_3512997 < baseStart_3512997 := by decide
  rcases family_descends (prefixWord ++ tailWord_3512997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3513061 : List Nat := [1, 3, 1, 4, 1, 3, 2, 1, 1, 5]
def baseStart_3513061 : Nat := 118140960795 + 3513061 * 2 ^ 59
def prefixEnd_3513061 : Nat := 4983230072969 + 3 ^ 40 * 3513061 * 2
def baseEnd_3513061 : Nat := 1202592574376523244254155

theorem tailTrace_3513061 : CollatzResearch.WordTrace tailWord_3513061 prefixEnd_3513061 1202592574376523244254155 := by
  unfold tailWord_3513061
  simp only [CollatzResearch.WordTrace]
  refine ⟨128131861125787454896819037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85421240750524969931212691 128131861125787454896819037)
  ·
    refine ⟨48049447922170295586307139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128131861125787454896819037 48049447922170295586307139)
    ·
      refine ⟨72074171883255443379460709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48049447922170295586307139 72074171883255443379460709)
      ·
        refine ⟨13513907228110395633648883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72074171883255443379460709 13513907228110395633648883)
        ·
          refine ⟨20270860842165593450473325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13513907228110395633648883 20270860842165593450473325)
          ·
            refine ⟨7601572815812097543927497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20270860842165593450473325 7601572815812097543927497)
            ·
              refine ⟨5701179611859073157945623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7601572815812097543927497 5701179611859073157945623)
              ·
                refine ⟨8551769417788609736918435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5701179611859073157945623 8551769417788609736918435)
                ·
                  refine ⟨12827654126682914605377653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8551769417788609736918435 12827654126682914605377653)
                  ·
                    refine ⟨1202592574376523244254155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12827654126682914605377653 1202592574376523244254155)
                    ·
                      rfl

theorem cell22_3513061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 2, 1, 1, 5].length) (baseStart_3513061 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3513061 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3513061 prefixEnd_3513061 := by exact prefixLift 3513061
  have htrace : WordTrace (prefixWord ++ tailWord_3513061) baseStart_3513061 baseEnd_3513061 := by
    simpa [prefixWord, tailWord_3513061, baseEnd_3513061] using wordTrace_append hprefix tailTrace_3513061
  have hstable : (prefixWord ++ tailWord_3513061).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3513061).length < 2 ^ (prefixWord ++ tailWord_3513061).sum := by decide
  have hdescent : baseEnd_3513061 < baseStart_3513061 := by decide
  rcases family_descends (prefixWord ++ tailWord_3513061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3513095 : List Nat := [1, 1, 4, 4, 1, 3, 1, 2, 2, 3]
def baseStart_3513095 : Nat := 118140960795 + 3513095 * 2 ^ 59
def prefixEnd_3513095 : Nat := 4983230072969 + 3 ^ 40 * 3513095 * 2
def baseEnd_3513095 : Nat := 1202604213271358488904051

theorem tailTrace_3513095 : CollatzResearch.WordTrace tailWord_3513095 prefixEnd_3513095 1202604213271358488904051 := by
  unfold tailWord_3513095
  simp only [CollatzResearch.WordTrace]
  refine ⟨128133101207664278703556739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85422067471776185802371159 128133101207664278703556739)
  ·
    refine ⟨192199651811496418055335109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128133101207664278703556739 192199651811496418055335109)
    ·
      refine ⟨36037434714655578385375333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 192199651811496418055335109 36037434714655578385375333)
      ·
        refine ⟨6757019008997920947257875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36037434714655578385375333 6757019008997920947257875)
        ·
          refine ⟨10135528513496881420886813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6757019008997920947257875 10135528513496881420886813)
          ·
            refine ⟨3800823192561330532832555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10135528513496881420886813 3800823192561330532832555)
            ·
              refine ⟨5701234788841995799248833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3800823192561330532832555 5701234788841995799248833)
              ·
                refine ⟨4275926091631496849436625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5701234788841995799248833 4275926091631496849436625)
                ·
                  refine ⟨3206944568723622637077469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4275926091631496849436625 3206944568723622637077469)
                  ·
                    refine ⟨1202604213271358488904051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3206944568723622637077469 1202604213271358488904051)
                    ·
                      rfl

theorem cell22_3513095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 1, 2, 2, 3].length) (baseStart_3513095 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3513095 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3513095 prefixEnd_3513095 := by exact prefixLift 3513095
  have htrace : WordTrace (prefixWord ++ tailWord_3513095) baseStart_3513095 baseEnd_3513095 := by
    simpa [prefixWord, tailWord_3513095, baseEnd_3513095] using wordTrace_append hprefix tailTrace_3513095
  have hstable : (prefixWord ++ tailWord_3513095).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3513095).length < 2 ^ (prefixWord ++ tailWord_3513095).sum := by decide
  have hdescent : baseEnd_3513095 < baseStart_3513095 := by decide
  rcases family_descends (prefixWord ++ tailWord_3513095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3513196 : List Nat := [2, 2, 1, 1, 4, 1, 3, 2, 1, 5]
def baseStart_3513196 : Nat := 118140960795 + 3513196 * 2 ^ 59
def prefixEnd_3513196 : Nat := 4983230072969 + 3 ^ 40 * 3513196 * 2
def baseEnd_3513196 : Nat := 1202638787635427892128741

theorem tailTrace_3513196 : CollatzResearch.WordTrace tailWord_3513196 prefixEnd_3513196 1202638787635427892128741 := by
  unfold tailWord_3513196
  simp only [CollatzResearch.WordTrace]
  refine ⟨64068392490149186476491721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85424523320198915301988961 64068392490149186476491721)
  ·
    refine ⟨48051294367611889857368791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64068392490149186476491721 48051294367611889857368791)
    ·
      refine ⟨72076941551417834786053187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48051294367611889857368791 72076941551417834786053187)
      ·
        refine ⟨108115412327126752179079781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72076941551417834786053187 108115412327126752179079781)
        ·
          refine ⟨20271639811336266033577459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 108115412327126752179079781 20271639811336266033577459)
          ·
            refine ⟨30407459717004399050366189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20271639811336266033577459 30407459717004399050366189)
            ·
              refine ⟨11402797393876649643887321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30407459717004399050366189 11402797393876649643887321)
              ·
                refine ⟨8552098045407487232915491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11402797393876649643887321 8552098045407487232915491)
                ·
                  refine ⟨12828147068111230849373237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8552098045407487232915491 12828147068111230849373237)
                  ·
                    refine ⟨1202638787635427892128741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12828147068111230849373237 1202638787635427892128741)
                    ·
                      rfl

theorem cell22_3513196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 5].length) (baseStart_3513196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3513196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3513196 prefixEnd_3513196 := by exact prefixLift 3513196
  have htrace : WordTrace (prefixWord ++ tailWord_3513196) baseStart_3513196 baseEnd_3513196 := by
    simpa [prefixWord, tailWord_3513196, baseEnd_3513196] using wordTrace_append hprefix tailTrace_3513196
  have hstable : (prefixWord ++ tailWord_3513196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3513196).length < 2 ^ (prefixWord ++ tailWord_3513196).sum := by decide
  have hdescent : baseEnd_3513196 < baseStart_3513196 := by decide
  rcases family_descends (prefixWord ++ tailWord_3513196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3513209 : List Nat := [1, 2, 1, 3, 2, 13]
def baseStart_3513209 : Nat := 118140960795 + 3513209 * 2 ^ 59
def prefixEnd_3513209 : Nat := 4983230072969 + 3 ^ 40 * 3513209 * 2
def baseEnd_3513209 : Nat := 14847447380260496192021

theorem tailTrace_3513209 : CollatzResearch.WordTrace tailWord_3513209 prefixEnd_3513209 14847447380260496192021 := by
  unfold tailWord_3513209
  simp only [CollatzResearch.WordTrace]
  refine ⟨128137259129251276173206681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85424839419500850782137787 128137259129251276173206681)
  ·
    refine ⟨96102944346938457129905011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128137259129251276173206681 96102944346938457129905011)
    ·
      refine ⟨144154416520407685694857517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96102944346938457129905011 144154416520407685694857517)
      ·
        refine ⟨54057906195152882135571569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144154416520407685694857517 54057906195152882135571569)
        ·
          refine ⟨40543429646364661601678677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54057906195152882135571569 40543429646364661601678677)
          ·
            refine ⟨14847447380260496192021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 40543429646364661601678677 14847447380260496192021)
            ·
              rfl

theorem cell22_3513209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 13].length) (baseStart_3513209 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3513209 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3513209 prefixEnd_3513209 := by exact prefixLift 3513209
  have htrace : WordTrace (prefixWord ++ tailWord_3513209) baseStart_3513209 baseEnd_3513209 := by
    simpa [prefixWord, tailWord_3513209, baseEnd_3513209] using wordTrace_append hprefix tailTrace_3513209
  have hstable : (prefixWord ++ tailWord_3513209).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3513209).length < 2 ^ (prefixWord ++ tailWord_3513209).sum := by decide
  have hdescent : baseEnd_3513209 < baseStart_3513209 := by decide
  rcases family_descends (prefixWord ++ tailWord_3513209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3513211 : List Nat := [1, 1, 1, 1, 1, 5, 4, 2, 2, 4]
def baseStart_3513211 : Nat := 118140960795 + 3513211 * 2 ^ 59
def prefixEnd_3513211 : Nat := 4983230072969 + 3 ^ 40 * 3513211 * 2
def baseEnd_3513211 : Nat := 1202643922441972853003695

theorem tailTrace_3513211 : CollatzResearch.WordTrace tailWord_3513211 prefixEnd_3513211 1202643922441972853003695 := by
  unfold tailWord_3513211
  simp only [CollatzResearch.WordTrace]
  refine ⟨128137332075244030514779487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85424888050162687009852991 128137332075244030514779487)
  ·
    refine ⟨192205998112866045772169231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128137332075244030514779487 192205998112866045772169231)
    ·
      refine ⟨288308997169299068658253847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192205998112866045772169231 288308997169299068658253847)
      ·
        refine ⟨432463495753948602987380771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 288308997169299068658253847 432463495753948602987380771)
        ·
          refine ⟨648695243630922904481071157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 432463495753948602987380771 648695243630922904481071157)
          ·
            refine ⟨60815179090399022295100421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 648695243630922904481071157 60815179090399022295100421)
            ·
              refine ⟨11402846079449816680331329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60815179090399022295100421 11402846079449816680331329)
              ·
                refine ⟨8552134559587362510248497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11402846079449816680331329 8552134559587362510248497)
                ·
                  refine ⟨6414100919690521882686373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8552134559587362510248497 6414100919690521882686373)
                  ·
                    refine ⟨1202643922441972853003695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6414100919690521882686373 1202643922441972853003695)
                    ·
                      rfl

theorem cell22_3513211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 2, 2, 4].length) (baseStart_3513211 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3513211 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3513211 prefixEnd_3513211 := by exact prefixLift 3513211
  have htrace : WordTrace (prefixWord ++ tailWord_3513211) baseStart_3513211 baseEnd_3513211 := by
    simpa [prefixWord, tailWord_3513211, baseEnd_3513211] using wordTrace_append hprefix tailTrace_3513211
  have hstable : (prefixWord ++ tailWord_3513211).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3513211).length < 2 ^ (prefixWord ++ tailWord_3513211).sum := by decide
  have hdescent : baseEnd_3513211 < baseStart_3513211 := by decide
  rcases family_descends (prefixWord ++ tailWord_3513211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3513213 : List Nat := [1, 4, 1, 1, 2, 1, 3, 4, 2, 3]
def baseStart_3513213 : Nat := 118140960795 + 3513213 * 2 ^ 59
def prefixEnd_3513213 : Nat := 4983230072969 + 3 ^ 40 * 3513213 * 2
def baseEnd_3513213 : Nat := 1202644607082845514453689

theorem tailTrace_3513213 : CollatzResearch.WordTrace tailWord_3513213 prefixEnd_3513213 1202644607082845514453689 := by
  unfold tailWord_3513213
  simp only [CollatzResearch.WordTrace]
  refine ⟨128137405021236784856352293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85424936680824523237568195 128137405021236784856352293)
  ·
    refine ⟨24025763441481897160566055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 128137405021236784856352293 24025763441481897160566055)
    ·
      refine ⟨36038645162222845740849083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24025763441481897160566055 36038645162222845740849083)
      ·
        refine ⟨54057967743334268611273625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36038645162222845740849083 54057967743334268611273625)
        ·
          refine ⟨40543475807500701458455219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54057967743334268611273625 40543475807500701458455219)
          ·
            refine ⟨60815213711251052187682829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40543475807500701458455219 60815213711251052187682829)
            ·
              refine ⟨22805705141719144570381061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60815213711251052187682829 22805705141719144570381061)
              ·
                refine ⟨4276069714072339606946449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22805705141719144570381061 4276069714072339606946449)
                ·
                  refine ⟨3207052285554254705209837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4276069714072339606946449 3207052285554254705209837)
                  ·
                    refine ⟨1202644607082845514453689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3207052285554254705209837 1202644607082845514453689)
                    ·
                      rfl

theorem cell22_3513213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 4, 2, 3].length) (baseStart_3513213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3513213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3513213 prefixEnd_3513213 := by exact prefixLift 3513213
  have htrace : WordTrace (prefixWord ++ tailWord_3513213) baseStart_3513213 baseEnd_3513213 := by
    simpa [prefixWord, tailWord_3513213, baseEnd_3513213] using wordTrace_append hprefix tailTrace_3513213
  have hstable : (prefixWord ++ tailWord_3513213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3513213).length < 2 ^ (prefixWord ++ tailWord_3513213).sum := by decide
  have hdescent : baseEnd_3513213 < baseStart_3513213 := by decide
  rcases family_descends (prefixWord ++ tailWord_3513213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3513309 : List Nat := [1, 4, 3, 1, 2, 3, 1, 3, 1, 3]
def baseStart_3513309 : Nat := 118140960795 + 3513309 * 2 ^ 59
def prefixEnd_3513309 : Nat := 4983230072969 + 3 ^ 40 * 3513309 * 2
def baseEnd_3513309 : Nat := 1202677469844733264053395

theorem tailTrace_3513309 : CollatzResearch.WordTrace tailWord_3513309 prefixEnd_3513309 1202677469844733264053395 := by
  unfold tailWord_3513309
  simp only [CollatzResearch.WordTrace]
  refine ⟨128140906428888993251846981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85427270952592662167897987 128140906428888993251846981)
  ·
    refine ⟨24026419955416686234721309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 128140906428888993251846981 24026419955416686234721309)
    ·
      refine ⟨9009907483281257338020491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24026419955416686234721309 9009907483281257338020491)
      ·
        refine ⟨13514861224921886007030737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9009907483281257338020491 13514861224921886007030737)
        ·
          refine ⟨10136145918691414505273053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13514861224921886007030737 10136145918691414505273053)
          ·
            refine ⟨3801054719509280439477395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10136145918691414505273053 3801054719509280439477395)
            ·
              refine ⟨5701582079263920659216093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3801054719509280439477395 5701582079263920659216093)
              ·
                refine ⟨2138093279723970247206035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5701582079263920659216093 2138093279723970247206035)
                ·
                  refine ⟨3207139919585955370809053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2138093279723970247206035 3207139919585955370809053)
                  ·
                    refine ⟨1202677469844733264053395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3207139919585955370809053 1202677469844733264053395)
                    ·
                      rfl

theorem cell22_3513309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 1, 3, 1, 3].length) (baseStart_3513309 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3513309 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3513309 prefixEnd_3513309 := by exact prefixLift 3513309
  have htrace : WordTrace (prefixWord ++ tailWord_3513309) baseStart_3513309 baseEnd_3513309 := by
    simpa [prefixWord, tailWord_3513309, baseEnd_3513309] using wordTrace_append hprefix tailTrace_3513309
  have hstable : (prefixWord ++ tailWord_3513309).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3513309).length < 2 ^ (prefixWord ++ tailWord_3513309).sum := by decide
  have hdescent : baseEnd_3513309 < baseStart_3513309 := by decide
  rcases family_descends (prefixWord ++ tailWord_3513309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3513380 : List Nat := [2, 3, 1, 4, 1, 1, 2, 2, 2, 4]
def baseStart_3513380 : Nat := 118140960795 + 3513380 * 2 ^ 59
def prefixEnd_3513380 : Nat := 4983230072969 + 3 ^ 40 * 3513380 * 2
def baseEnd_3513380 : Nat := 1202701774595712745528177

theorem tailTrace_3513380 : CollatzResearch.WordTrace tailWord_3513380 prefixEnd_3513380 1202701774595712745528177 := by
  unfold tailWord_3513380
  simp only [CollatzResearch.WordTrace]
  refine ⟨64071748005815886188840797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85428997341087848251787729 64071748005815886188840797)
  ·
    refine ⟨24026905502180957320815299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64071748005815886188840797 24026905502180957320815299)
    ·
      refine ⟨36040358253271435981222949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24026905502180957320815299 36040358253271435981222949)
      ·
        refine ⟨6757567172488394246479303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36040358253271435981222949 6757567172488394246479303)
        ·
          refine ⟨10136350758732591369718955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6757567172488394246479303 10136350758732591369718955)
          ·
            refine ⟨15204526138098887054578433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10136350758732591369718955 15204526138098887054578433)
            ·
              refine ⟨11403394603574165290933825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15204526138098887054578433 11403394603574165290933825)
              ·
                refine ⟨8552545952680623968200369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11403394603574165290933825 8552545952680623968200369)
                ·
                  refine ⟨6414409464510467976150277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8552545952680623968200369 6414409464510467976150277)
                  ·
                    refine ⟨1202701774595712745528177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6414409464510467976150277 1202701774595712745528177)
                    ·
                      rfl

theorem cell22_3513380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 2, 2, 4].length) (baseStart_3513380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3513380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3513380 prefixEnd_3513380 := by exact prefixLift 3513380
  have htrace : WordTrace (prefixWord ++ tailWord_3513380) baseStart_3513380 baseEnd_3513380 := by
    simpa [prefixWord, tailWord_3513380, baseEnd_3513380] using wordTrace_append hprefix tailTrace_3513380
  have hstable : (prefixWord ++ tailWord_3513380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3513380).length < 2 ^ (prefixWord ++ tailWord_3513380).sum := by decide
  have hdescent : baseEnd_3513380 < baseStart_3513380 := by decide
  rcases family_descends (prefixWord ++ tailWord_3513380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3513414 : List Nat := [6, 1, 1, 1, 1, 4, 1, 1, 2, 4]
def baseStart_3513414 : Nat := 118140960795 + 3513414 * 2 ^ 59
def prefixEnd_3513414 : Nat := 4983230072969 + 3 ^ 40 * 3513414 * 2
def baseEnd_3513414 : Nat := 1202713413490547990178073

theorem tailTrace_3513414 : CollatzResearch.WordTrace tailWord_3513414 prefixEnd_3513414 1202713413490547990178073 := by
  unfold tailWord_3513414
  simp only [CollatzResearch.WordTrace]
  refine ⟨4004523002922143630763103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 85429824062339064122946197 4004523002922143630763103)
  ·
    refine ⟨6006784504383215446144655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4004523002922143630763103 6006784504383215446144655)
    ·
      refine ⟨9010176756574823169216983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6006784504383215446144655 9010176756574823169216983)
      ·
        refine ⟨13515265134862234753825475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9010176756574823169216983 13515265134862234753825475)
        ·
          refine ⟨20272897702293352130738213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13515265134862234753825475 20272897702293352130738213)
          ·
            refine ⟨3801168319180003524513415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20272897702293352130738213 3801168319180003524513415)
            ·
              refine ⟨5701752478770005286770123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3801168319180003524513415 5701752478770005286770123)
              ·
                refine ⟨8552628718155007930155185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5701752478770005286770123 8552628718155007930155185)
                ·
                  refine ⟨6414471538616255947616389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8552628718155007930155185 6414471538616255947616389)
                  ·
                    refine ⟨1202713413490547990178073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6414471538616255947616389 1202713413490547990178073)
                    ·
                      rfl

theorem cell22_3513414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 1, 1, 2, 4].length) (baseStart_3513414 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3513414 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3513414 prefixEnd_3513414 := by exact prefixLift 3513414
  have htrace : WordTrace (prefixWord ++ tailWord_3513414) baseStart_3513414 baseEnd_3513414 := by
    simpa [prefixWord, tailWord_3513414, baseEnd_3513414] using wordTrace_append hprefix tailTrace_3513414
  have hstable : (prefixWord ++ tailWord_3513414).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3513414).length < 2 ^ (prefixWord ++ tailWord_3513414).sum := by decide
  have hdescent : baseEnd_3513414 < baseStart_3513414 := by decide
  rcases family_descends (prefixWord ++ tailWord_3513414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3513468 : List Nat := [2, 2, 2, 1, 1, 3, 1, 4, 6]
def baseStart_3513468 : Nat := 118140960795 + 3513468 * 2 ^ 59
def prefixEnd_3513468 : Nat := 4983230072969 + 3 ^ 40 * 3513468 * 2
def baseEnd_3513468 : Nat := 400910632931369949775969

theorem tailTrace_3513468 : CollatzResearch.WordTrace tailWord_3513468 prefixEnd_3513468 400910632931369949775969 := by
  unfold tailWord_3513468
  simp only [CollatzResearch.WordTrace]
  refine ⟨64073352817656481703442529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85431137090208642271256705 64073352817656481703442529)
  ·
    refine ⟨48055014613242361277581897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64073352817656481703442529 48055014613242361277581897)
    ·
      refine ⟨36041260959931770958186423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48055014613242361277581897 36041260959931770958186423)
      ·
        refine ⟨54061891439897656437279635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36041260959931770958186423 54061891439897656437279635)
        ·
          refine ⟨81092837159846484655919453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54061891439897656437279635 81092837159846484655919453)
          ·
            refine ⟨30409813934942431745969795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81092837159846484655919453 30409813934942431745969795)
            ·
              refine ⟨45614720902413647618954693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30409813934942431745969795 45614720902413647618954693)
              ·
                refine ⟨8552760169202558928554005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45614720902413647618954693 8552760169202558928554005)
                ·
                  refine ⟨400910632931369949775969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8552760169202558928554005 400910632931369949775969)
                  ·
                    rfl

theorem cell22_3513468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 4, 6].length) (baseStart_3513468 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3513468 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3513468 prefixEnd_3513468 := by exact prefixLift 3513468
  have htrace : WordTrace (prefixWord ++ tailWord_3513468) baseStart_3513468 baseEnd_3513468 := by
    simpa [prefixWord, tailWord_3513468, baseEnd_3513468] using wordTrace_append hprefix tailTrace_3513468
  have hstable : (prefixWord ++ tailWord_3513468).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3513468).length < 2 ^ (prefixWord ++ tailWord_3513468).sum := by decide
  have hdescent : baseEnd_3513468 < baseStart_3513468 := by decide
  rcases family_descends (prefixWord ++ tailWord_3513468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3513483 : List Nat := [1, 1, 1, 1, 4, 1, 1, 6, 1, 5]
def baseStart_3513483 : Nat := 118140960795 + 3513483 * 2 ^ 59
def prefixEnd_3513483 : Nat := 4983230072969 + 3 ^ 40 * 3513483 * 2
def baseEnd_3513483 : Nat := 1202737033600654810202861

theorem tailTrace_3513483 : CollatzResearch.WordTrace tailWord_3513483 prefixEnd_3513483 1202737033600654810202861 := by
  unfold tailWord_3513483
  simp only [CollatzResearch.WordTrace]
  refine ⟨128147252730258620968681103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85431501820172413979120735 128147252730258620968681103)
  ·
    refine ⟨192220879095387931453021655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128147252730258620968681103 192220879095387931453021655)
    ·
      refine ⟨288331318643081897179532483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192220879095387931453021655 288331318643081897179532483)
      ·
        refine ⟨432496977964622845769298725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 288331318643081897179532483 432496977964622845769298725)
        ·
          refine ⟨81093183368366783581743511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 432496977964622845769298725 81093183368366783581743511)
          ·
            refine ⟨121639775052550175372615267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81093183368366783581743511 121639775052550175372615267)
            ·
              refine ⟨182459662578825263058922901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121639775052550175372615267 182459662578825263058922901)
              ·
                refine ⟨8552796683382434205887011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 182459662578825263058922901 8552796683382434205887011)
                ·
                  refine ⟨12829195025073651308830517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8552796683382434205887011 12829195025073651308830517)
                  ·
                    refine ⟨1202737033600654810202861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12829195025073651308830517 1202737033600654810202861)
                    ·
                      rfl

theorem cell22_3513483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 6, 1, 5].length) (baseStart_3513483 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3513483 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3513483 prefixEnd_3513483 := by exact prefixLift 3513483
  have htrace : WordTrace (prefixWord ++ tailWord_3513483) baseStart_3513483 baseEnd_3513483 := by
    simpa [prefixWord, tailWord_3513483, baseEnd_3513483] using wordTrace_append hprefix tailTrace_3513483
  have hstable : (prefixWord ++ tailWord_3513483).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3513483).length < 2 ^ (prefixWord ++ tailWord_3513483).sum := by decide
  have hdescent : baseEnd_3513483 < baseStart_3513483 := by decide
  rcases family_descends (prefixWord ++ tailWord_3513483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3513502 : List Nat := [4, 3, 1, 1, 2, 1, 3, 1, 6]
def baseStart_3513502 : Nat := 118140960795 + 3513502 * 2 ^ 59
def prefixEnd_3513502 : Nat := 4983230072969 + 3 ^ 40 * 3513502 * 2
def baseEnd_3513502 : Nat := 400914512562981697992601

theorem tailTrace_3513502 : CollatzResearch.WordTrace tailWord_3513502 prefixEnd_3513502 400914512562981697992601 := by
  unfold tailWord_3513502
  simp only [CollatzResearch.WordTrace]
  refine ⟨16018493214648723401702845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85431963811459858142415173 16018493214648723401702845)
  ·
    refine ⟨6006934955493271275638567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16018493214648723401702845 6006934955493271275638567)
    ·
      refine ⟨9010402433239906913457851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6006934955493271275638567 9010402433239906913457851)
      ·
        refine ⟨13515603649859860370186777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9010402433239906913457851 13515603649859860370186777)
        ·
          refine ⟨10136702737394895277640083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13515603649859860370186777 10136702737394895277640083)
          ·
            refine ⟨15205054106092342916460125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10136702737394895277640083 15205054106092342916460125)
            ·
              refine ⟨5701895289784628593672547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15205054106092342916460125 5701895289784628593672547)
              ·
                refine ⟨8552842934676942890508821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5701895289784628593672547 8552842934676942890508821)
                ·
                  refine ⟨400914512562981697992601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8552842934676942890508821 400914512562981697992601)
                  ·
                    rfl

theorem cell22_3513502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 3, 1, 6].length) (baseStart_3513502 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3513502 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3513502 prefixEnd_3513502 := by exact prefixLift 3513502
  have htrace : WordTrace (prefixWord ++ tailWord_3513502) baseStart_3513502 baseEnd_3513502 := by
    simpa [prefixWord, tailWord_3513502, baseEnd_3513502] using wordTrace_append hprefix tailTrace_3513502
  have hstable : (prefixWord ++ tailWord_3513502).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3513502).length < 2 ^ (prefixWord ++ tailWord_3513502).sum := by decide
  have hdescent : baseEnd_3513502 < baseStart_3513502 := by decide
  rcases family_descends (prefixWord ++ tailWord_3513502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3513532 : List Nat := [2, 2, 2, 3, 2, 2, 2, 1, 2, 4]
def baseStart_3513532 : Nat := 118140960795 + 3513532 * 2 ^ 59
def prefixEnd_3513532 : Nat := 4983230072969 + 3 ^ 40 * 3513532 * 2
def baseEnd_3513532 : Nat := 1202753807302035015727711

theorem tailTrace_3513532 : CollatzResearch.WordTrace tailWord_3513532 prefixEnd_3513532 1202753807302035015727711 := by
  unfold tailWord_3513532
  simp only [CollatzResearch.WordTrace]
  refine ⟨64074519953540551168607425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85432693271387401558143233 64074519953540551168607425)
  ·
    refine ⟨48055889965155413376455569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64074519953540551168607425 48055889965155413376455569)
    ·
      refine ⟨36041917473866560032341677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48055889965155413376455569 36041917473866560032341677)
      ·
        refine ⟨13515719052699960012128129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36041917473866560032341677 13515719052699960012128129)
        ·
          refine ⟨10136789289524970009096097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13515719052699960012128129 10136789289524970009096097)
          ·
            refine ⟨7602591967143727506822073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10136789289524970009096097 7602591967143727506822073)
            ·
              refine ⟨5701943975357795630116555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7602591967143727506822073 5701943975357795630116555)
              ·
                refine ⟨8552915963036693445174833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5701943975357795630116555 8552915963036693445174833)
                ·
                  refine ⟨6414686972277520083881125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8552915963036693445174833 6414686972277520083881125)
                  ·
                    refine ⟨1202753807302035015727711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6414686972277520083881125 1202753807302035015727711)
                    ·
                      rfl

theorem cell22_3513532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 2, 1, 2, 4].length) (baseStart_3513532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3513532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3513532 prefixEnd_3513532 := by exact prefixLift 3513532
  have htrace : WordTrace (prefixWord ++ tailWord_3513532) baseStart_3513532 baseEnd_3513532 := by
    simpa [prefixWord, tailWord_3513532, baseEnd_3513532] using wordTrace_append hprefix tailTrace_3513532
  have hstable : (prefixWord ++ tailWord_3513532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3513532).length < 2 ^ (prefixWord ++ tailWord_3513532).sum := by decide
  have hdescent : baseEnd_3513532 < baseStart_3513532 := by decide
  rcases family_descends (prefixWord ++ tailWord_3513532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3513538 : List Nat := [3, 5, 1, 1, 2, 1, 3, 1, 1, 4]
def baseStart_3513538 : Nat := 118140960795 + 3513538 * 2 ^ 59
def prefixEnd_3513538 : Nat := 4983230072969 + 3 ^ 40 * 3513538 * 2
def baseEnd_3513538 : Nat := 1202755861224653000077693

theorem tailTrace_3513538 : CollatzResearch.WordTrace tailWord_3513538 prefixEnd_3513538 1202755861224653000077693 := by
  unfold tailWord_3513538
  simp only [CollatzResearch.WordTrace]
  refine ⟨32037314686264841340483317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85432839163372910241288845 32037314686264841340483317)
  ·
    refine ⟨3003498251837328875670311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 32037314686264841340483317 3003498251837328875670311)
    ·
      refine ⟨4505247377755993313505467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3003498251837328875670311 4505247377755993313505467)
      ·
        refine ⟨6757871066633989970258201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4505247377755993313505467 6757871066633989970258201)
        ·
          refine ⟨5068403299975492477693651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6757871066633989970258201 5068403299975492477693651)
          ·
            refine ⟨7602604949963238716540477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5068403299975492477693651 7602604949963238716540477)
            ·
              refine ⟨2850976856236214518702679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7602604949963238716540477 2850976856236214518702679)
              ·
                refine ⟨4276465284354321778054019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2850976856236214518702679 4276465284354321778054019)
                ·
                  refine ⟨6414697926531482667081029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4276465284354321778054019 6414697926531482667081029)
                  ·
                    refine ⟨1202755861224653000077693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6414697926531482667081029 1202755861224653000077693)
                    ·
                      rfl

theorem cell22_3513538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 3, 1, 1, 4].length) (baseStart_3513538 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3513538 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3513538 prefixEnd_3513538 := by exact prefixLift 3513538
  have htrace : WordTrace (prefixWord ++ tailWord_3513538) baseStart_3513538 baseEnd_3513538 := by
    simpa [prefixWord, tailWord_3513538, baseEnd_3513538] using wordTrace_append hprefix tailTrace_3513538
  have hstable : (prefixWord ++ tailWord_3513538).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3513538).length < 2 ^ (prefixWord ++ tailWord_3513538).sum := by decide
  have hdescent : baseEnd_3513538 < baseStart_3513538 := by decide
  rcases family_descends (prefixWord ++ tailWord_3513538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3513543 : List Nat := [1, 1, 4, 1, 1, 1, 1, 2, 4, 6]
def baseStart_3513543 : Nat := 118140960795 + 3513543 * 2 ^ 59
def prefixEnd_3513543 : Nat := 4983230072969 + 3 ^ 40 * 3513543 * 2
def baseEnd_3513543 : Nat := 1202757572826834653702677

theorem tailTrace_3513543 : CollatzResearch.WordTrace tailWord_3513543 prefixEnd_3513543 1202757572826834653702677 := by
  unfold tailWord_3513543
  simp only [CollatzResearch.WordTrace]
  refine ⟨128149441110041251215865283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85432960740027500810576855 128149441110041251215865283)
  ·
    refine ⟨192224161665061876823797925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128149441110041251215865283 192224161665061876823797925)
    ·
      refine ⟨36042030312199101904462111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 192224161665061876823797925 36042030312199101904462111)
      ·
        refine ⟨54063045468298652856693167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36042030312199101904462111 54063045468298652856693167)
        ·
          refine ⟨81094568202447979285039751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54063045468298652856693167 81094568202447979285039751)
          ·
            refine ⟨121641852303671968927559627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81094568202447979285039751 121641852303671968927559627)
            ·
              refine ⟨182462778455507953391339441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121641852303671968927559627 182462778455507953391339441)
              ·
                refine ⟨136847083841630965043504581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 182462778455507953391339441 136847083841630965043504581)
                ·
                  refine ⟨25658828220305805945657109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 136847083841630965043504581 25658828220305805945657109)
                  ·
                    refine ⟨1202757572826834653702677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25658828220305805945657109 1202757572826834653702677)
                    ·
                      rfl

theorem cell22_3513543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 2, 4, 6].length) (baseStart_3513543 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3513543 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3513543 prefixEnd_3513543 := by exact prefixLift 3513543
  have htrace : WordTrace (prefixWord ++ tailWord_3513543) baseStart_3513543 baseEnd_3513543 := by
    simpa [prefixWord, tailWord_3513543, baseEnd_3513543] using wordTrace_append hprefix tailTrace_3513543
  have hstable : (prefixWord ++ tailWord_3513543).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3513543).length < 2 ^ (prefixWord ++ tailWord_3513543).sum := by decide
  have hdescent : baseEnd_3513543 < baseStart_3513543 := by decide
  rcases family_descends (prefixWord ++ tailWord_3513543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3513590 : List Nat := [5, 1, 1, 1, 1, 1, 1, 1, 3, 7]
def baseStart_3513590 : Nat := 118140960795 + 3513590 * 2 ^ 59
def prefixEnd_3513590 : Nat := 4983230072969 + 3 ^ 40 * 3513590 * 2
def baseEnd_3513590 : Nat := 1202773661887342197777533

theorem tailTrace_3513590 : CollatzResearch.WordTrace tailWord_3513590 prefixEnd_3513590 1202773661887342197777533 := by
  unfold tailWord_3513590
  simp only [CollatzResearch.WordTrace]
  refine ⟨8009447208804436140176639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 85434103560580652161884149 8009447208804436140176639)
  ·
    refine ⟨12014170813206654210264959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8009447208804436140176639 12014170813206654210264959)
    ·
      refine ⟨18021256219809981315397439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12014170813206654210264959 18021256219809981315397439)
      ·
        refine ⟨27031884329714971973096159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18021256219809981315397439 27031884329714971973096159)
        ·
          refine ⟨40547826494572457959644239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27031884329714971973096159 40547826494572457959644239)
          ·
            refine ⟨60821739741858686939466359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40547826494572457959644239 60821739741858686939466359)
            ·
              refine ⟨91232609612788030409199539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60821739741858686939466359 91232609612788030409199539)
              ·
                refine ⟨136848914419182045613799309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91232609612788030409199539 136848914419182045613799309)
                ·
                  refine ⟨51318342907193267105174741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 136848914419182045613799309 51318342907193267105174741)
                  ·
                    refine ⟨1202773661887342197777533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51318342907193267105174741 1202773661887342197777533)
                    ·
                      rfl

theorem cell22_3513590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 3, 7].length) (baseStart_3513590 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3513590 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3513590 prefixEnd_3513590 := by exact prefixLift 3513590
  have htrace : WordTrace (prefixWord ++ tailWord_3513590) baseStart_3513590 baseEnd_3513590 := by
    simpa [prefixWord, tailWord_3513590, baseEnd_3513590] using wordTrace_append hprefix tailTrace_3513590
  have hstable : (prefixWord ++ tailWord_3513590).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3513590).length < 2 ^ (prefixWord ++ tailWord_3513590).sum := by decide
  have hdescent : baseEnd_3513590 < baseStart_3513590 := by decide
  rcases family_descends (prefixWord ++ tailWord_3513590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3513596 : List Nat := [2, 2, 2, 1, 5, 1, 2, 3, 1, 3]
def baseStart_3513596 : Nat := 118140960795 + 3513596 * 2 ^ 59
def prefixEnd_3513596 : Nat := 4983230072969 + 3 ^ 40 * 3513596 * 2
def baseEnd_3513596 : Nat := 1202775715809960182127515

theorem tailTrace_3513596 : CollatzResearch.WordTrace tailWord_3513596 prefixEnd_3513596 1202775715809960182127515 := by
  unfold tailWord_3513596
  simp only [CollatzResearch.WordTrace]
  refine ⟨64075687089424620633772321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85434249452566160845029761 64075687089424620633772321)
  ·
    refine ⟨48056765317068465475329241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64075687089424620633772321 48056765317068465475329241)
    ·
      refine ⟨36042573987801349106496931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48056765317068465475329241 36042573987801349106496931)
      ·
        refine ⟨54063860981702023659745397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36042573987801349106496931 54063860981702023659745397)
        ·
          refine ⟨5068486967034564718101131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 54063860981702023659745397 5068486967034564718101131)
          ·
            refine ⟨7602730450551847077151697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5068486967034564718101131 7602730450551847077151697)
            ·
              refine ⟨5702047837913885307863773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7602730450551847077151697 5702047837913885307863773)
              ·
                refine ⟨2138267939217706990448915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5702047837913885307863773 2138267939217706990448915)
                ·
                  refine ⟨3207401908826560485673373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2138267939217706990448915 3207401908826560485673373)
                  ·
                    refine ⟨1202775715809960182127515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3207401908826560485673373 1202775715809960182127515)
                    ·
                      rfl

theorem cell22_3513596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 2, 3, 1, 3].length) (baseStart_3513596 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3513596 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3513596 prefixEnd_3513596 := by exact prefixLift 3513596
  have htrace : WordTrace (prefixWord ++ tailWord_3513596) baseStart_3513596 baseEnd_3513596 := by
    simpa [prefixWord, tailWord_3513596, baseEnd_3513596] using wordTrace_append hprefix tailTrace_3513596
  have hstable : (prefixWord ++ tailWord_3513596).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3513596).length < 2 ^ (prefixWord ++ tailWord_3513596).sum := by decide
  have hdescent : baseEnd_3513596 < baseStart_3513596 := by decide
  rcases family_descends (prefixWord ++ tailWord_3513596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3513652 : List Nat := [2, 5, 1, 1, 1, 1, 2, 1, 3, 5]
def baseStart_3513652 : Nat := 118140960795 + 3513652 * 2 ^ 59
def prefixEnd_3513652 : Nat := 4983230072969 + 3 ^ 40 * 3513652 * 2
def baseEnd_3513652 : Nat := 1202794885754394702727343

theorem tailTrace_3513652 : CollatzResearch.WordTrace tailWord_3513652 prefixEnd_3513652 1202794885754394702727343 := by
  unfold tailWord_3513652
  simp only [CollatzResearch.WordTrace]
  refine ⟨64076708333323181415791605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85435611111097575221055473 64076708333323181415791605)
  ·
    refine ⟨6007191406249048257730463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 64076708333323181415791605 6007191406249048257730463)
    ·
      refine ⟨9010787109373572386595695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6007191406249048257730463 9010787109373572386595695)
      ·
        refine ⟨13516180664060358579893543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9010787109373572386595695 13516180664060358579893543)
        ·
          refine ⟨20274270996090537869840315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13516180664060358579893543 20274270996090537869840315)
          ·
            refine ⟨30411406494135806804760473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20274270996090537869840315 30411406494135806804760473)
            ·
              refine ⟨22808554870601855103570355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30411406494135806804760473 22808554870601855103570355)
              ·
                refine ⟨34212832305902782655355533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22808554870601855103570355 34212832305902782655355533)
                ·
                  refine ⟨12829812114713543495758325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34212832305902782655355533 12829812114713543495758325)
                  ·
                    refine ⟨1202794885754394702727343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12829812114713543495758325 1202794885754394702727343)
                    ·
                      rfl

theorem cell22_3513652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 1, 3, 5].length) (baseStart_3513652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3513652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3513652 prefixEnd_3513652 := by exact prefixLift 3513652
  have htrace : WordTrace (prefixWord ++ tailWord_3513652) baseStart_3513652 baseEnd_3513652 := by
    simpa [prefixWord, tailWord_3513652, baseEnd_3513652] using wordTrace_append hprefix tailTrace_3513652
  have hstable : (prefixWord ++ tailWord_3513652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3513652).length < 2 ^ (prefixWord ++ tailWord_3513652).sum := by decide
  have hdescent : baseEnd_3513652 < baseStart_3513652 := by decide
  rcases family_descends (prefixWord ++ tailWord_3513652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3513697 : List Nat := [1, 2, 3, 1, 1, 1, 1, 6, 3, 3]
def baseStart_3513697 : Nat := 118140960795 + 3513697 * 2 ^ 59
def prefixEnd_3513697 : Nat := 4983230072969 + 3 ^ 40 * 3513697 * 2
def baseEnd_3513697 : Nat := 1202810290174029585352205

theorem tailTrace_3513697 : CollatzResearch.WordTrace tailWord_3513697 prefixEnd_3513697 1202810290174029585352205 := by
  unfold tailWord_3513697
  simp only [CollatzResearch.WordTrace]
  refine ⟨128155057951483335516971345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85436705300988890344647563 128155057951483335516971345)
  ·
    refine ⟨96116293463612501637728509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128155057951483335516971345 96116293463612501637728509)
    ·
      refine ⟨36043610048854688114148191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96116293463612501637728509 36043610048854688114148191)
      ·
        refine ⟨54065415073282032171222287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36043610048854688114148191 54065415073282032171222287)
        ·
          refine ⟨81098122609923048256833431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54065415073282032171222287 81098122609923048256833431)
          ·
            refine ⟨121647183914884572385250147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81098122609923048256833431 121647183914884572385250147)
            ·
              refine ⟨182470775872326858577875221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121647183914884572385250147 182470775872326858577875221)
              ·
                refine ⟨8553317619015321495837901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 182470775872326858577875221 8553317619015321495837901)
                ·
                  refine ⟨3207494107130745560939213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8553317619015321495837901 3207494107130745560939213)
                  ·
                    refine ⟨1202810290174029585352205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3207494107130745560939213 1202810290174029585352205)
                    ·
                      rfl

theorem cell22_3513697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 6, 3, 3].length) (baseStart_3513697 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3513697 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3513697 prefixEnd_3513697 := by exact prefixLift 3513697
  have htrace : WordTrace (prefixWord ++ tailWord_3513697) baseStart_3513697 baseEnd_3513697 := by
    simpa [prefixWord, tailWord_3513697, baseEnd_3513697] using wordTrace_append hprefix tailTrace_3513697
  have hstable : (prefixWord ++ tailWord_3513697).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3513697).length < 2 ^ (prefixWord ++ tailWord_3513697).sum := by decide
  have hdescent : baseEnd_3513697 < baseStart_3513697 := by decide
  rcases family_descends (prefixWord ++ tailWord_3513697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3513731 : List Nat := [1, 1, 1, 3, 5, 2, 1, 4, 1, 3]
def baseStart_3513731 : Nat := 118140960795 + 3513731 * 2 ^ 59
def prefixEnd_3513731 : Nat := 4983230072969 + 3 ^ 40 * 3513731 * 2
def baseEnd_3513731 : Nat := 1202821929068864830002101

theorem tailTrace_3513731 : CollatzResearch.WordTrace tailWord_3513731 prefixEnd_3513731 1202821929068864830002101 := by
  unfold tailWord_3513731
  simp only [CollatzResearch.WordTrace]
  refine ⟨128156298033360159323709047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85437532022240106215806031 128156298033360159323709047)
  ·
    refine ⟨192234447050040238985563571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128156298033360159323709047 192234447050040238985563571)
    ·
      refine ⟨288351670575060358478345357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192234447050040238985563571 288351670575060358478345357)
      ·
        refine ⟨108131876465647634429379509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 288351670575060358478345357 108131876465647634429379509)
        ·
          refine ⟨10137363418654465727754329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 108131876465647634429379509 10137363418654465727754329)
          ·
            refine ⟨7603022563990849295815747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10137363418654465727754329 7603022563990849295815747)
            ·
              refine ⟨11404533845986273943723621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7603022563990849295815747 11404533845986273943723621)
              ·
                refine ⟨2138350096122426364448179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11404533845986273943723621 2138350096122426364448179)
                ·
                  refine ⟨3207525144183639546672269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2138350096122426364448179 3207525144183639546672269)
                  ·
                    refine ⟨1202821929068864830002101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3207525144183639546672269 1202821929068864830002101)
                    ·
                      rfl

theorem cell22_3513731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 4, 1, 3].length) (baseStart_3513731 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3513731 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3513731 prefixEnd_3513731 := by exact prefixLift 3513731
  have htrace : WordTrace (prefixWord ++ tailWord_3513731) baseStart_3513731 baseEnd_3513731 := by
    simpa [prefixWord, tailWord_3513731, baseEnd_3513731] using wordTrace_append hprefix tailTrace_3513731
  have hstable : (prefixWord ++ tailWord_3513731).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3513731).length < 2 ^ (prefixWord ++ tailWord_3513731).sum := by decide
  have hdescent : baseEnd_3513731 < baseStart_3513731 := by decide
  rcases family_descends (prefixWord ++ tailWord_3513731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3513789 : List Nat := [1, 4, 1, 2, 2, 1, 1, 6, 4]
def baseStart_3513789 : Nat := 118140960795 + 3513789 * 2 ^ 59
def prefixEnd_3513789 : Nat := 4983230072969 + 3 ^ 40 * 3513789 * 2
def baseEnd_3513789 : Nat := 400947261218057337350641

theorem tailTrace_3513789 : CollatzResearch.WordTrace tailWord_3513789 prefixEnd_3513789 400947261218057337350641 := by
  unfold tailWord_3513789
  simp only [CollatzResearch.WordTrace]
  refine ⟨128158413467150035229320421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85438942311433356819546947 128158413467150035229320421)
  ·
    refine ⟨24029702525090631605497579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 128158413467150035229320421 24029702525090631605497579)
    ·
      refine ⟨36044553787635947408246369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24029702525090631605497579 36044553787635947408246369)
      ·
        refine ⟨27033415340726960556184777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36044553787635947408246369 27033415340726960556184777)
        ·
          refine ⟨20275061505545220417138583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27033415340726960556184777 20275061505545220417138583)
          ·
            refine ⟨30412592258317830625707875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20275061505545220417138583 30412592258317830625707875)
            ·
              refine ⟨45618888387476745938561813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30412592258317830625707875 45618888387476745938561813)
              ·
                refine ⟨2138385393162972465870085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 45618888387476745938561813 2138385393162972465870085)
                ·
                  refine ⟨400947261218057337350641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2138385393162972465870085 400947261218057337350641)
                  ·
                    rfl

theorem cell22_3513789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 6, 4].length) (baseStart_3513789 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3513789 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3513789 prefixEnd_3513789 := by exact prefixLift 3513789
  have htrace : WordTrace (prefixWord ++ tailWord_3513789) baseStart_3513789 baseEnd_3513789 := by
    simpa [prefixWord, tailWord_3513789, baseEnd_3513789] using wordTrace_append hprefix tailTrace_3513789
  have hstable : (prefixWord ++ tailWord_3513789).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3513789).length < 2 ^ (prefixWord ++ tailWord_3513789).sum := by decide
  have hdescent : baseEnd_3513789 < baseStart_3513789 := by decide
  rcases family_descends (prefixWord ++ tailWord_3513789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3513802 : List Nat := [3, 1, 2, 1, 2, 3, 1, 2, 1, 6]
def baseStart_3513802 : Nat := 118140960795 + 3513802 * 2 ^ 59
def prefixEnd_3513802 : Nat := 4983230072969 + 3 ^ 40 * 3513802 * 2
def baseEnd_3513802 : Nat := 1202846233819844311476883

theorem tailTrace_3513802 : CollatzResearch.WordTrace tailWord_3513802 prefixEnd_3513802 1202846233819844311476883 := by
  unfold tailWord_3513802
  simp only [CollatzResearch.WordTrace]
  refine ⟨32039721904025734612385915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85439258410735292299695773 32039721904025734612385915)
  ·
    refine ⟨48059582856038601918578873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32039721904025734612385915 48059582856038601918578873)
    ·
      refine ⟨36044687142028951438934155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48059582856038601918578873 36044687142028951438934155)
      ·
        refine ⟨54067030713043427158401233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36044687142028951438934155 54067030713043427158401233)
        ·
          refine ⟨40550273034782570368800925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54067030713043427158401233 40550273034782570368800925)
          ·
            refine ⟨15206352388043463888300347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40550273034782570368800925 15206352388043463888300347)
            ·
              refine ⟨22809528582065195832450521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15206352388043463888300347 22809528582065195832450521)
              ·
                refine ⟨17107146436548896874337891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22809528582065195832450521 17107146436548896874337891)
                ·
                  refine ⟨25660719654823345311506837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17107146436548896874337891 25660719654823345311506837)
                  ·
                    refine ⟨1202846233819844311476883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25660719654823345311506837 1202846233819844311476883)
                    ·
                      rfl

theorem cell22_3513802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 2, 1, 6].length) (baseStart_3513802 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3513802 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3513802 prefixEnd_3513802 := by exact prefixLift 3513802
  have htrace : WordTrace (prefixWord ++ tailWord_3513802) baseStart_3513802 baseEnd_3513802 := by
    simpa [prefixWord, tailWord_3513802, baseEnd_3513802] using wordTrace_append hprefix tailTrace_3513802
  have hstable : (prefixWord ++ tailWord_3513802).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3513802).length < 2 ^ (prefixWord ++ tailWord_3513802).sum := by decide
  have hdescent : baseEnd_3513802 < baseStart_3513802 := by decide
  rcases family_descends (prefixWord ++ tailWord_3513802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3513804 : List Nat := [2, 2, 1, 4, 2, 1, 3, 1, 1, 5]
def baseStart_3513804 : Nat := 118140960795 + 3513804 * 2 ^ 59
def prefixEnd_3513804 : Nat := 4983230072969 + 3 ^ 40 * 3513804 * 2
def baseEnd_3513804 : Nat := 1202846918460716972926877

theorem tailTrace_3513804 : CollatzResearch.WordTrace tailWord_3513804 prefixEnd_3513804 1202846918460716972926877 := by
  unfold tailWord_3513804
  simp only [CollatzResearch.WordTrace]
  refine ⟨64079480281047846395558233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85439307041397128527410977 64079480281047846395558233)
  ·
    refine ⟨48059610210785884796668675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64079480281047846395558233 48059610210785884796668675)
    ·
      refine ⟨72089415316178827195003013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48059610210785884796668675 72089415316178827195003013)
      ·
        refine ⟨13516765371783530099063065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72089415316178827195003013 13516765371783530099063065)
        ·
          refine ⟨10137574028837647574297299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13516765371783530099063065 10137574028837647574297299)
          ·
            refine ⟨15206361043256471361445949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10137574028837647574297299 15206361043256471361445949)
            ·
              refine ⟨5702385391221176760542231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15206361043256471361445949 5702385391221176760542231)
              ·
                refine ⟨8553578086831765140813347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5702385391221176760542231 8553578086831765140813347)
                ·
                  refine ⟨12830367130247647711220021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8553578086831765140813347 12830367130247647711220021)
                  ·
                    refine ⟨1202846918460716972926877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12830367130247647711220021 1202846918460716972926877)
                    ·
                      rfl

theorem cell22_3513804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 3, 1, 1, 5].length) (baseStart_3513804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3513804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3513804 prefixEnd_3513804 := by exact prefixLift 3513804
  have htrace : WordTrace (prefixWord ++ tailWord_3513804) baseStart_3513804 baseEnd_3513804 := by
    simpa [prefixWord, tailWord_3513804, baseEnd_3513804] using wordTrace_append hprefix tailTrace_3513804
  have hstable : (prefixWord ++ tailWord_3513804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3513804).length < 2 ^ (prefixWord ++ tailWord_3513804).sum := by decide
  have hdescent : baseEnd_3513804 < baseStart_3513804 := by decide
  rcases family_descends (prefixWord ++ tailWord_3513804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3513817 : List Nat := [1, 2, 1, 2, 4, 3, 1, 8]
def baseStart_3513817 : Nat := 118140960795 + 3513817 * 2 ^ 59
def prefixEnd_3513817 : Nat := 4983230072969 + 3 ^ 40 * 3513817 * 2
def baseEnd_3513817 : Nat := 133650152069598808039093

theorem tailTrace_3513817 : CollatzResearch.WordTrace tailWord_3513817 prefixEnd_3513817 133650152069598808039093 := by
  unfold tailWord_3513817
  simp only [CollatzResearch.WordTrace]
  refine ⟨128159434711048596011339705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85439623140699064007559803 128159434711048596011339705)
  ·
    refine ⟨96119576033286447008504779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128159434711048596011339705 96119576033286447008504779)
    ·
      refine ⟨144179364049929670512757169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96119576033286447008504779 144179364049929670512757169)
      ·
        refine ⟨108134523037447252884567877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144179364049929670512757169 108134523037447252884567877)
        ·
          refine ⟨20275223069521359915856477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 108134523037447252884567877 20275223069521359915856477)
          ·
            refine ⟨7603208651070509968446179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20275223069521359915856477 7603208651070509968446179)
            ·
              refine ⟨11404812976605764952669269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7603208651070509968446179 11404812976605764952669269)
              ·
                refine ⟨133650152069598808039093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11404812976605764952669269 133650152069598808039093)
                ·
                  rfl

theorem cell22_3513817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 8].length) (baseStart_3513817 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3513817 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3513817 prefixEnd_3513817 := by exact prefixLift 3513817
  have htrace : WordTrace (prefixWord ++ tailWord_3513817) baseStart_3513817 baseEnd_3513817 := by
    simpa [prefixWord, tailWord_3513817, baseEnd_3513817] using wordTrace_append hprefix tailTrace_3513817
  have hstable : (prefixWord ++ tailWord_3513817).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3513817).length < 2 ^ (prefixWord ++ tailWord_3513817).sum := by decide
  have hdescent : baseEnd_3513817 < baseStart_3513817 := by decide
  rcases family_descends (prefixWord ++ tailWord_3513817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3513834 : List Nat := [3, 1, 3, 1, 4, 2, 8]
def baseStart_3513834 : Nat := 118140960795 + 3513834 * 2 ^ 59
def prefixEnd_3513834 : Nat := 4983230072969 + 3 ^ 40 * 3513834 * 2
def baseEnd_3513834 : Nat := 44550266224955810913955

theorem tailTrace_3513834 : CollatzResearch.WordTrace tailWord_3513834 prefixEnd_3513834 44550266224955810913955 := by
  unfold tailWord_3513834
  simp only [CollatzResearch.WordTrace]
  refine ⟨32040013687996751978677139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85440036501324671943139037 32040013687996751978677139)
  ·
    refine ⟨48060020531995127968015709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32040013687996751978677139 48060020531995127968015709)
    ·
      refine ⟨18022507699498172988005891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48060020531995127968015709 18022507699498172988005891)
      ·
        refine ⟨27033761549247259482008837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18022507699498172988005891 27033761549247259482008837)
        ·
          refine ⟨5068830290483861152876657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27033761549247259482008837 5068830290483861152876657)
          ·
            refine ⟨3801622717862895864657493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5068830290483861152876657 3801622717862895864657493)
            ·
              refine ⟨44550266224955810913955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3801622717862895864657493 44550266224955810913955)
              ·
                rfl

theorem cell22_3513834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 8].length) (baseStart_3513834 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3513834 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3513834 prefixEnd_3513834 := by exact prefixLift 3513834
  have htrace : WordTrace (prefixWord ++ tailWord_3513834) baseStart_3513834 baseEnd_3513834 := by
    simpa [prefixWord, tailWord_3513834, baseEnd_3513834] using wordTrace_append hprefix tailTrace_3513834
  have hstable : (prefixWord ++ tailWord_3513834).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3513834).length < 2 ^ (prefixWord ++ tailWord_3513834).sum := by decide
  have hdescent : baseEnd_3513834 < baseStart_3513834 := by decide
  rcases family_descends (prefixWord ++ tailWord_3513834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3513909 : List Nat := [1, 3, 3, 1, 1, 3, 1, 2, 3, 4]
def baseStart_3513909 : Nat := 118140960795 + 3513909 * 2 ^ 59
def prefixEnd_3513909 : Nat := 4983230072969 + 3 ^ 40 * 3513909 * 2
def baseEnd_3513909 : Nat := 1202882862106531699051555

theorem tailTrace_3513909 : CollatzResearch.WordTrace tailWord_3513909 prefixEnd_3513909 1202882862106531699051555 := by
  unfold tailWord_3513909
  simp only [CollatzResearch.WordTrace]
  refine ⟨128162790226715295723688781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85441860151143530482459187 128162790226715295723688781)
  ·
    refine ⟨48061046335018235896383293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128162790226715295723688781 48061046335018235896383293)
    ·
      refine ⟨18022892375631838461143735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48061046335018235896383293 18022892375631838461143735)
      ·
        refine ⟨27034338563447757691715603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18022892375631838461143735 27034338563447757691715603)
        ·
          refine ⟨40551507845171636537573405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27034338563447757691715603 40551507845171636537573405)
          ·
            refine ⟨15206815441939363701590027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40551507845171636537573405 15206815441939363701590027)
            ·
              refine ⟨22810223162909045552385041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15206815441939363701590027 22810223162909045552385041)
              ·
                refine ⟨17107667372181784164288781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22810223162909045552385041 17107667372181784164288781)
                ·
                  refine ⟨6415375264568169061608293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17107667372181784164288781 6415375264568169061608293)
                  ·
                    refine ⟨1202882862106531699051555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6415375264568169061608293 1202882862106531699051555)
                    ·
                      rfl

theorem cell22_3513909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 2, 3, 4].length) (baseStart_3513909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3513909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3513909 prefixEnd_3513909 := by exact prefixLift 3513909
  have htrace : WordTrace (prefixWord ++ tailWord_3513909) baseStart_3513909 baseEnd_3513909 := by
    simpa [prefixWord, tailWord_3513909, baseEnd_3513909] using wordTrace_append hprefix tailTrace_3513909
  have hstable : (prefixWord ++ tailWord_3513909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3513909).length < 2 ^ (prefixWord ++ tailWord_3513909).sum := by decide
  have hdescent : baseEnd_3513909 < baseStart_3513909 := by decide
  rcases family_descends (prefixWord ++ tailWord_3513909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3513943 : List Nat := [1, 1, 3, 2, 2, 5, 2, 1, 1, 4]
def baseStart_3513943 : Nat := 118140960795 + 3513943 * 2 ^ 59
def prefixEnd_3513943 : Nat := 4983230072969 + 3 ^ 40 * 3513943 * 2
def baseEnd_3513943 : Nat := 1202894501001366943701451

theorem tailTrace_3513943 : CollatzResearch.WordTrace tailWord_3513943 prefixEnd_3513943 1202894501001366943701451 := by
  unfold tailWord_3513943
  simp only [CollatzResearch.WordTrace]
  refine ⟨128164030308592119530426483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85442686872394746353617655 128164030308592119530426483)
  ·
    refine ⟨192246045462888179295639725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128164030308592119530426483 192246045462888179295639725)
    ·
      refine ⟨72092267048583067235864897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 192246045462888179295639725 72092267048583067235864897)
      ·
        refine ⟨54069200286437300426898673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72092267048583067235864897 54069200286437300426898673)
        ·
          refine ⟨40551900214827975320174005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54069200286437300426898673 40551900214827975320174005)
          ·
            refine ⟨3801740645140122686266313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 40551900214827975320174005 3801740645140122686266313)
            ·
              refine ⟨2851305483855092014699735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3801740645140122686266313 2851305483855092014699735)
              ·
                refine ⟨4276958225782638022049603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2851305483855092014699735 4276958225782638022049603)
                ·
                  refine ⟨6415437338673957033074405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4276958225782638022049603 6415437338673957033074405)
                  ·
                    refine ⟨1202894501001366943701451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6415437338673957033074405 1202894501001366943701451)
                    ·
                      rfl

theorem cell22_3513943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 2, 1, 1, 4].length) (baseStart_3513943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3513943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3513943 prefixEnd_3513943 := by exact prefixLift 3513943
  have htrace : WordTrace (prefixWord ++ tailWord_3513943) baseStart_3513943 baseEnd_3513943 := by
    simpa [prefixWord, tailWord_3513943, baseEnd_3513943] using wordTrace_append hprefix tailTrace_3513943
  have hstable : (prefixWord ++ tailWord_3513943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3513943).length < 2 ^ (prefixWord ++ tailWord_3513943).sum := by decide
  have hdescent : baseEnd_3513943 < baseStart_3513943 := by decide
  rcases family_descends (prefixWord ++ tailWord_3513943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3513956 : List Nat := [2, 3, 1, 1, 2, 4, 1, 1, 4, 3]
def baseStart_3513956 : Nat := 118140960795 + 3513956 * 2 ^ 59
def prefixEnd_3513956 : Nat := 4983230072969 + 3 ^ 40 * 3513956 * 2
def baseEnd_3513956 : Nat := 1202898951167039243126411

theorem tailTrace_3513956 : CollatzResearch.WordTrace tailWord_3513956 prefixEnd_3513956 1202898951167039243126411 := by
  unfold tailWord_3513956
  simp only [CollatzResearch.WordTrace]
  refine ⟨64082252228772511375324861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85443002971696681833766481 64082252228772511375324861)
  ·
    refine ⟨24030844585789691765746823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64082252228772511375324861 24030844585789691765746823)
    ·
      refine ⟨36046266878684537648620235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24030844585789691765746823 36046266878684537648620235)
      ·
        refine ⟨54069400318026806472930353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36046266878684537648620235 54069400318026806472930353)
        ·
          refine ⟨40552050238520104854697765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54069400318026806472930353 40552050238520104854697765)
          ·
            refine ⟨7603509419722519660255831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40552050238520104854697765 7603509419722519660255831)
            ·
              refine ⟨11405264129583779490383747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7603509419722519660255831 11405264129583779490383747)
              ·
                refine ⟨17107896194375669235575621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11405264129583779490383747 17107896194375669235575621)
                ·
                  refine ⟨3207730536445437981670429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17107896194375669235575621 3207730536445437981670429)
                  ·
                    refine ⟨1202898951167039243126411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3207730536445437981670429 1202898951167039243126411)
                    ·
                      rfl

theorem cell22_3513956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 1, 4, 3].length) (baseStart_3513956 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3513956 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3513956 prefixEnd_3513956 := by exact prefixLift 3513956
  have htrace : WordTrace (prefixWord ++ tailWord_3513956) baseStart_3513956 baseEnd_3513956 := by
    simpa [prefixWord, tailWord_3513956, baseEnd_3513956] using wordTrace_append hprefix tailTrace_3513956
  have hstable : (prefixWord ++ tailWord_3513956).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3513956).length < 2 ^ (prefixWord ++ tailWord_3513956).sum := by decide
  have hdescent : baseEnd_3513956 < baseStart_3513956 := by decide
  rcases family_descends (prefixWord ++ tailWord_3513956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3513973 : List Nat := [1, 3, 4, 2, 1, 3, 1, 1, 1, 5]
def baseStart_3513973 : Nat := 118140960795 + 3513973 * 2 ^ 59
def prefixEnd_3513973 : Nat := 4983230072969 + 3 ^ 40 * 3513973 * 2
def baseEnd_3513973 : Nat := 1202904770614456865451359

theorem tailTrace_3513973 : CollatzResearch.WordTrace tailWord_3513973 prefixEnd_3513973 1202904770614456865451359 := by
  unfold tailWord_3513973
  simp only [CollatzResearch.WordTrace]
  refine ⟨128165124498483434654018573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85443416332322289769345715 128165124498483434654018573)
  ·
    refine ⟨48061921686931287995256965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128165124498483434654018573 48061921686931287995256965)
    ·
      refine ⟨9011610316299616499110681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48061921686931287995256965 9011610316299616499110681)
      ·
        refine ⟨6758707737224712374333011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9011610316299616499110681 6758707737224712374333011)
        ·
          refine ⟨10138061605837068561499517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6758707737224712374333011 10138061605837068561499517)
          ·
            refine ⟨3801773102188900710562319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10138061605837068561499517 3801773102188900710562319)
            ·
              refine ⟨5702659653283351065843479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3801773102188900710562319 5702659653283351065843479)
              ·
                refine ⟨8553989479925026598765219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5702659653283351065843479 8553989479925026598765219)
                ·
                  refine ⟨12830984219887539898147829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8553989479925026598765219 12830984219887539898147829)
                  ·
                    refine ⟨1202904770614456865451359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12830984219887539898147829 1202904770614456865451359)
                    ·
                      rfl

theorem cell22_3513973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 1, 1, 1, 5].length) (baseStart_3513973 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3513973 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3513973 prefixEnd_3513973 := by exact prefixLift 3513973
  have htrace : WordTrace (prefixWord ++ tailWord_3513973) baseStart_3513973 baseEnd_3513973 := by
    simpa [prefixWord, tailWord_3513973, baseEnd_3513973] using wordTrace_append hprefix tailTrace_3513973
  have hstable : (prefixWord ++ tailWord_3513973).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3513973).length < 2 ^ (prefixWord ++ tailWord_3513973).sum := by decide
  have hdescent : baseEnd_3513973 < baseStart_3513973 := by decide
  rcases family_descends (prefixWord ++ tailWord_3513973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3513992 : List Nat := [2, 1, 3, 5, 2, 1, 1, 3, 4]
def baseStart_3513992 : Nat := 118140960795 + 3513992 * 2 ^ 59
def prefixEnd_3513992 : Nat := 4983230072969 + 3 ^ 40 * 3513992 * 2
def baseEnd_3513992 : Nat := 400970424900915716408767

theorem tailTrace_3513992 : CollatzResearch.WordTrace tailWord_3513992 prefixEnd_3513992 400970424900915716408767 := by
  unfold tailWord_3513992
  simp only [CollatzResearch.WordTrace]
  refine ⟨64082908742707300449480115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85443878323609733932640153 64082908742707300449480115)
  ·
    refine ⟨96124363114060950674220173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64082908742707300449480115 96124363114060950674220173)
    ·
      refine ⟨36046636167772856502832565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96124363114060950674220173 36046636167772856502832565)
      ·
        refine ⟨3379372140728705297140553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 36046636167772856502832565 3379372140728705297140553)
        ·
          refine ⟨2534529105546528972855415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3379372140728705297140553 2534529105546528972855415)
          ·
            refine ⟨3801793658319793459283123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2534529105546528972855415 3801793658319793459283123)
            ·
              refine ⟨5702690487479690188924685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3801793658319793459283123 5702690487479690188924685)
              ·
                refine ⟨2138508932804883820846757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5702690487479690188924685 2138508932804883820846757)
                ·
                  refine ⟨400970424900915716408767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2138508932804883820846757 400970424900915716408767)
                  ·
                    rfl

theorem cell22_3513992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 1, 3, 4].length) (baseStart_3513992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3513992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3513992 prefixEnd_3513992 := by exact prefixLift 3513992
  have htrace : WordTrace (prefixWord ++ tailWord_3513992) baseStart_3513992 baseEnd_3513992 := by
    simpa [prefixWord, tailWord_3513992, baseEnd_3513992] using wordTrace_append hprefix tailTrace_3513992
  have hstable : (prefixWord ++ tailWord_3513992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3513992).length < 2 ^ (prefixWord ++ tailWord_3513992).sum := by decide
  have hdescent : baseEnd_3513992 < baseStart_3513992 := by decide
  rcases family_descends (prefixWord ++ tailWord_3513992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3514089 : List Nat := [1, 2, 1, 1, 1, 2, 3, 4, 1, 6]
def baseStart_3514089 : Nat := 118140960795 + 3514089 * 2 ^ 59
def prefixEnd_3514089 : Nat := 4983230072969 + 3 ^ 40 * 3514089 * 2
def baseEnd_3514089 : Nat := 1202944479785071229551003

theorem tailTrace_3514089 : CollatzResearch.WordTrace tailWord_3514089 prefixEnd_3514089 1202944479785071229551003 := by
  unfold tailWord_3514089
  simp only [CollatzResearch.WordTrace]
  refine ⟨128169355366063186465241321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85446236910708790976827547 128169355366063186465241321)
  ·
    refine ⟨96127016524547389848930991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128169355366063186465241321 96127016524547389848930991)
    ·
      refine ⟨144190524786821084773396487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96127016524547389848930991 144190524786821084773396487)
      ·
        refine ⟨216285787180231627160094731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144190524786821084773396487 216285787180231627160094731)
        ·
          refine ⟨324428680770347440740142097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216285787180231627160094731 324428680770347440740142097)
          ·
            refine ⟨243321510577760580555106573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 324428680770347440740142097 243321510577760580555106573)
            ·
              refine ⟨91245566466660217708164965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 243321510577760580555106573 91245566466660217708164965)
              ·
                refine ⟨17108543712498790820280931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 91245566466660217708164965 17108543712498790820280931)
                ·
                  refine ⟨25662815568748186230421397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17108543712498790820280931 25662815568748186230421397)
                  ·
                    refine ⟨1202944479785071229551003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25662815568748186230421397 1202944479785071229551003)
                    ·
                      rfl

theorem cell22_3514089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 4, 1, 6].length) (baseStart_3514089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3514089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3514089 prefixEnd_3514089 := by exact prefixLift 3514089
  have htrace : WordTrace (prefixWord ++ tailWord_3514089) baseStart_3514089 baseEnd_3514089 := by
    simpa [prefixWord, tailWord_3514089, baseEnd_3514089] using wordTrace_append hprefix tailTrace_3514089
  have hstable : (prefixWord ++ tailWord_3514089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3514089).length < 2 ^ (prefixWord ++ tailWord_3514089).sum := by decide
  have hdescent : baseEnd_3514089 < baseStart_3514089 := by decide
  rcases family_descends (prefixWord ++ tailWord_3514089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3514260 : List Nat := [2, 4, 2, 1, 1, 3, 2, 1, 1, 5]
def baseStart_3514260 : Nat := 118140960795 + 3514260 * 2 ^ 59
def prefixEnd_3514260 : Nat := 4983230072969 + 3 ^ 40 * 3514260 * 2
def baseEnd_3514260 : Nat := 1203003016579683783525479

theorem tailTrace_3514260 : CollatzResearch.WordTrace tailWord_3514260 prefixEnd_3514260 1203003016579683783525479 := by
  unfold tailWord_3514260
  simp only [CollatzResearch.WordTrace]
  refine ⟨64087796124221841334858117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85450394832295788446477489 64087796124221841334858117)
  ·
    refine ⟨12016461773291595250285897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64087796124221841334858117 12016461773291595250285897)
    ·
      refine ⟨9012346329968696437714423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12016461773291595250285897 9012346329968696437714423)
      ·
        refine ⟨13518519494953044656571635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9012346329968696437714423 13518519494953044656571635)
        ·
          refine ⟨20277779242429566984857453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13518519494953044656571635 20277779242429566984857453)
          ·
            refine ⟨7604167215911087619321545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20277779242429566984857453 7604167215911087619321545)
            ·
              refine ⟨5703125411933315714491159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7604167215911087619321545 5703125411933315714491159)
              ·
                refine ⟨8554688117899973571736739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5703125411933315714491159 8554688117899973571736739)
                ·
                  refine ⟨12832032176849960357605109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8554688117899973571736739 12832032176849960357605109)
                  ·
                    refine ⟨1203003016579683783525479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12832032176849960357605109 1203003016579683783525479)
                    ·
                      rfl

theorem cell22_3514260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 2, 1, 1, 5].length) (baseStart_3514260 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3514260 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3514260 prefixEnd_3514260 := by exact prefixLift 3514260
  have htrace : WordTrace (prefixWord ++ tailWord_3514260) baseStart_3514260 baseEnd_3514260 := by
    simpa [prefixWord, tailWord_3514260, baseEnd_3514260] using wordTrace_append hprefix tailTrace_3514260
  have hstable : (prefixWord ++ tailWord_3514260).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3514260).length < 2 ^ (prefixWord ++ tailWord_3514260).sum := by decide
  have hdescent : baseEnd_3514260 < baseStart_3514260 := by decide
  rcases family_descends (prefixWord ++ tailWord_3514260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3514339 : List Nat := [1, 1, 1, 6, 1, 4, 1, 3, 1, 3]
def baseStart_3514339 : Nat := 118140960795 + 3514339 * 2 ^ 59
def prefixEnd_3514339 : Nat := 4983230072969 + 3 ^ 40 * 3514339 * 2
def baseEnd_3514339 : Nat := 1203030059894153910800237

theorem tailTrace_3514339 : CollatzResearch.WordTrace tailWord_3514339 prefixEnd_3514339 1203030059894153910800237 := by
  unfold tailWord_3514339
  simp only [CollatzResearch.WordTrace]
  refine ⟨128178473615157479161842071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85452315743438319441228047 128178473615157479161842071)
  ·
    refine ⟨192267710422736218742763107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128178473615157479161842071 192267710422736218742763107)
    ·
      refine ⟨288401565634104328114144661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192267710422736218742763107 288401565634104328114144661)
      ·
        refine ⟨13518823389098640380350531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 288401565634104328114144661 13518823389098640380350531)
        ·
          refine ⟨20278235083647960570525797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13518823389098640380350531 20278235083647960570525797)
          ·
            refine ⟨3802169078183992606973587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20278235083647960570525797 3802169078183992606973587)
            ·
              refine ⟨5703253617275988910460381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3802169078183992606973587 5703253617275988910460381)
              ·
                refine ⟨2138720106478495841422643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5703253617275988910460381 2138720106478495841422643)
                ·
                  refine ⟨3208080159717743762133965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2138720106478495841422643 3208080159717743762133965)
                  ·
                    refine ⟨1203030059894153910800237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3208080159717743762133965 1203030059894153910800237)
                    ·
                      rfl

theorem cell22_3514339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 1, 3, 1, 3].length) (baseStart_3514339 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3514339 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3514339 prefixEnd_3514339 := by exact prefixLift 3514339
  have htrace : WordTrace (prefixWord ++ tailWord_3514339) baseStart_3514339 baseEnd_3514339 := by
    simpa [prefixWord, tailWord_3514339, baseEnd_3514339] using wordTrace_append hprefix tailTrace_3514339
  have hstable : (prefixWord ++ tailWord_3514339).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3514339).length < 2 ^ (prefixWord ++ tailWord_3514339).sum := by decide
  have hdescent : baseEnd_3514339 < baseStart_3514339 := by decide
  rcases family_descends (prefixWord ++ tailWord_3514339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3514363 : List Nat := [1, 1, 1, 1, 1, 3, 7, 1, 6]
def baseStart_3514363 : Nat := 118140960795 + 3514363 * 2 ^ 59
def prefixEnd_3514363 : Nat := 4983230072969 + 3 ^ 40 * 3514363 * 2
def baseEnd_3514363 : Nat := 401012758528208616066721

theorem tailTrace_3514363 : CollatzResearch.WordTrace tailWord_3514363 prefixEnd_3514363 401012758528208616066721 := by
  unfold tailWord_3514363
  simp only [CollatzResearch.WordTrace]
  refine ⟨128179348967070531260715743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85452899311380354173810495 128179348967070531260715743)
  ·
    refine ⟨192269023450605796891073615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128179348967070531260715743 192269023450605796891073615)
    ·
      refine ⟨288403535175908695336610423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192269023450605796891073615 288403535175908695336610423)
      ·
        refine ⟨432605302763863043004915635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 288403535175908695336610423 432605302763863043004915635)
        ·
          refine ⟨648907954145794564507373453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 432605302763863043004915635 648907954145794564507373453)
          ·
            refine ⟨243340482804672961690265045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 648907954145794564507373453 243340482804672961690265045)
            ·
              refine ⟨5703292565734522539615587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 243340482804672961690265045 5703292565734522539615587)
              ·
                refine ⟨8554938848601783809423381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5703292565734522539615587 8554938848601783809423381)
                ·
                  refine ⟨401012758528208616066721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8554938848601783809423381 401012758528208616066721)
                  ·
                    rfl

theorem cell22_3514363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 7, 1, 6].length) (baseStart_3514363 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3514363 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3514363 prefixEnd_3514363 := by exact prefixLift 3514363
  have htrace : WordTrace (prefixWord ++ tailWord_3514363) baseStart_3514363 baseEnd_3514363 := by
    simpa [prefixWord, tailWord_3514363, baseEnd_3514363] using wordTrace_append hprefix tailTrace_3514363
  have hstable : (prefixWord ++ tailWord_3514363).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3514363).length < 2 ^ (prefixWord ++ tailWord_3514363).sum := by decide
  have hdescent : baseEnd_3514363 < baseStart_3514363 := by decide
  rcases family_descends (prefixWord ++ tailWord_3514363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3514414 : List Nat := [4, 1, 3, 1, 1, 2, 4, 2, 4]
def baseStart_3514414 : Nat := 118140960795 + 3514414 * 2 ^ 59
def prefixEnd_3514414 : Nat := 4983230072969 + 3 ^ 40 * 3514414 * 2
def baseEnd_3514414 : Nat := 401018577975626238391669

theorem tailTrace_3514414 : CollatzResearch.WordTrace tailWord_3514414 prefixEnd_3514414 401018577975626238391669 := by
  unfold tailWord_3514414
  simp only [CollatzResearch.WordTrace]
  refine ⟨16022651136235720871352787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85454139393257177980548197 16022651136235720871352787)
  ·
    refine ⟨24033976704353581307029181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16022651136235720871352787 24033976704353581307029181)
    ·
      refine ⟨9012741264132592990135943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24033976704353581307029181 9012741264132592990135943)
      ·
        refine ⟨13519111896198889485203915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9012741264132592990135943 13519111896198889485203915)
        ·
          refine ⟨20278667844298334227805873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13519111896198889485203915 20278667844298334227805873)
          ·
            refine ⟨15209000883223750670854405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20278667844298334227805873 15209000883223750670854405)
            ·
              refine ⟨2851687665604453250785201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15209000883223750670854405 2851687665604453250785201)
              ·
                refine ⟨2138765749203339938088901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2851687665604453250785201 2138765749203339938088901)
                ·
                  refine ⟨401018577975626238391669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2138765749203339938088901 401018577975626238391669)
                  ·
                    rfl

theorem cell22_3514414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 4, 2, 4].length) (baseStart_3514414 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3514414 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3514414 prefixEnd_3514414 := by exact prefixLift 3514414
  have htrace : WordTrace (prefixWord ++ tailWord_3514414) baseStart_3514414 baseEnd_3514414 := by
    simpa [prefixWord, tailWord_3514414, baseEnd_3514414] using wordTrace_append hprefix tailTrace_3514414
  have hstable : (prefixWord ++ tailWord_3514414).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3514414).length < 2 ^ (prefixWord ++ tailWord_3514414).sum := by decide
  have hdescent : baseEnd_3514414 < baseStart_3514414 := by decide
  rcases family_descends (prefixWord ++ tailWord_3514414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3514474 : List Nat := [3, 1, 3, 2, 3, 1, 2, 1, 3, 3]
def baseStart_3514474 : Nat := 118140960795 + 3514474 * 2 ^ 59
def prefixEnd_3514474 : Nat := 4983230072969 + 3 ^ 40 * 3514474 * 2
def baseEnd_3514474 : Nat := 1203076273153058558674823

theorem tailTrace_3514474 : CollatzResearch.WordTrace tailWord_3514474 prefixEnd_3514474 1203076273153058558674823 := by
  unfold tailWord_3514474
  simp only [CollatzResearch.WordTrace]
  refine ⟨32045849367417099304501619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85455598313112264812004317 32045849367417099304501619)
  ·
    refine ⟨48068774051125648956752429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32045849367417099304501619 48068774051125648956752429)
    ·
      refine ⟨18025790269172118358782161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48068774051125648956752429 18025790269172118358782161)
      ·
        refine ⟨13519342701879088769086621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18025790269172118358782161 13519342701879088769086621)
        ·
          refine ⟨5069753513204658288407483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13519342701879088769086621 5069753513204658288407483)
          ·
            refine ⟨7604630269806987432611225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5069753513204658288407483 7604630269806987432611225)
            ·
              refine ⟨5703472702355240574458419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7604630269806987432611225 5703472702355240574458419)
              ·
                refine ⟨8555209053532860861687629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5703472702355240574458419 8555209053532860861687629)
                ·
                  refine ⟨3208203395074822823132861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8555209053532860861687629 3208203395074822823132861)
                  ·
                    refine ⟨1203076273153058558674823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3208203395074822823132861 1203076273153058558674823)
                    ·
                      rfl

theorem cell22_3514474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 2, 1, 3, 3].length) (baseStart_3514474 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3514474 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3514474 prefixEnd_3514474 := by exact prefixLift 3514474
  have htrace : WordTrace (prefixWord ++ tailWord_3514474) baseStart_3514474 baseEnd_3514474 := by
    simpa [prefixWord, tailWord_3514474, baseEnd_3514474] using wordTrace_append hprefix tailTrace_3514474
  have hstable : (prefixWord ++ tailWord_3514474).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3514474).length < 2 ^ (prefixWord ++ tailWord_3514474).sum := by decide
  have hdescent : baseEnd_3514474 < baseStart_3514474 := by decide
  rcases family_descends (prefixWord ++ tailWord_3514474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3514487 : List Nat := [1, 1, 3, 1, 1, 6, 3, 1, 5]
def baseStart_3514487 : Nat := 118140960795 + 3514487 * 2 ^ 59
def prefixEnd_3514487 : Nat := 4983230072969 + 3 ^ 40 * 3514487 * 2
def baseEnd_3514487 : Nat := 401026907772910286033261

theorem tailTrace_3514487 : CollatzResearch.WordTrace tailWord_3514487 prefixEnd_3514487 401026907772910286033261 := by
  unfold tailWord_3514487
  simp only [CollatzResearch.WordTrace]
  refine ⟨128183871618621300438229715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85455914412414200292153143 128183871618621300438229715)
  ·
    refine ⟨192275807427931950657344573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128183871618621300438229715 192275807427931950657344573)
    ·
      refine ⟨72103427785474481496504215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 192275807427931950657344573 72103427785474481496504215)
      ·
        refine ⟨108155141678211722244756323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72103427785474481496504215 108155141678211722244756323)
        ·
          refine ⟨162232712517317583367134485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108155141678211722244756323 162232712517317583367134485)
          ·
            refine ⟨7604658399249261720334429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 162232712517317583367134485 7604658399249261720334429)
            ·
              refine ⟨2851746899718473145125411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7604658399249261720334429 2851746899718473145125411)
              ·
                refine ⟨4277620349577709717688117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2851746899718473145125411 4277620349577709717688117)
                ·
                  refine ⟨401026907772910286033261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4277620349577709717688117 401026907772910286033261)
                  ·
                    rfl

theorem cell22_3514487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 3, 1, 5].length) (baseStart_3514487 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3514487 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3514487 prefixEnd_3514487 := by exact prefixLift 3514487
  have htrace : WordTrace (prefixWord ++ tailWord_3514487) baseStart_3514487 baseEnd_3514487 := by
    simpa [prefixWord, tailWord_3514487, baseEnd_3514487] using wordTrace_append hprefix tailTrace_3514487
  have hstable : (prefixWord ++ tailWord_3514487).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3514487).length < 2 ^ (prefixWord ++ tailWord_3514487).sum := by decide
  have hdescent : baseEnd_3514487 < baseStart_3514487 := by decide
  rcases family_descends (prefixWord ++ tailWord_3514487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3514538 : List Nat := [3, 1, 5, 1, 3, 1, 2, 1, 5]
def baseStart_3514538 : Nat := 118140960795 + 3514538 * 2 ^ 59
def prefixEnd_3514538 : Nat := 4983230072969 + 3 ^ 40 * 3514538 * 2
def baseEnd_3514538 : Nat := 401032727220327908358209

theorem tailTrace_3514538 : CollatzResearch.WordTrace tailWord_3514538 prefixEnd_3514538 401032727220327908358209 := by
  unfold tailWord_3514538
  simp only [CollatzResearch.WordTrace]
  refine ⟨32046432935359134037084067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85457154494291024098890845 32046432935359134037084067)
  ·
    refine ⟨48069649403038701055626101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32046432935359134037084067 48069649403038701055626101)
    ·
      refine ⟨4506529631534878223964947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 48069649403038701055626101 4506529631534878223964947)
      ·
        refine ⟨6759794447302317335947421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4506529631534878223964947 6759794447302317335947421)
        ·
          refine ⟨2534922917738369000980283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6759794447302317335947421 2534922917738369000980283)
          ·
            refine ⟨3802384376607553501470425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2534922917738369000980283 3802384376607553501470425)
            ·
              refine ⟨2851788282455665126102819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3802384376607553501470425 2851788282455665126102819)
              ·
                refine ⟨4277682423683497689154229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2851788282455665126102819 4277682423683497689154229)
                ·
                  refine ⟨401032727220327908358209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4277682423683497689154229 401032727220327908358209)
                  ·
                    rfl

theorem cell22_3514538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 2, 1, 5].length) (baseStart_3514538 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3514538 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3514538 prefixEnd_3514538 := by exact prefixLift 3514538
  have htrace : WordTrace (prefixWord ++ tailWord_3514538) baseStart_3514538 baseEnd_3514538 := by
    simpa [prefixWord, tailWord_3514538, baseEnd_3514538] using wordTrace_append hprefix tailTrace_3514538
  have hstable : (prefixWord ++ tailWord_3514538).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3514538).length < 2 ^ (prefixWord ++ tailWord_3514538).sum := by decide
  have hdescent : baseEnd_3514538 < baseStart_3514538 := by decide
  rcases family_descends (prefixWord ++ tailWord_3514538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3514560 : List Nat := [2, 1, 1, 2, 5, 1, 2, 8]
def baseStart_3514560 : Nat := 118140960795 + 3514560 * 2 ^ 59
def prefixEnd_3514560 : Nat := 4983230072969 + 3 ^ 40 * 3514560 * 2
def baseEnd_3514560 : Nat := 133678412523398111224951

theorem tailTrace_3514560 : CollatzResearch.WordTrace tailWord_3514560 prefixEnd_3514560 133678412523398111224951 := by
  unfold tailWord_3514560
  simp only [CollatzResearch.WordTrace]
  refine ⟨64093267073678416952818567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85457689431571222603758089 64093267073678416952818567)
  ·
    refine ⟨96139900610517625429227851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64093267073678416952818567 96139900610517625429227851)
    ·
      refine ⟨144209850915776438143841777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96139900610517625429227851 144209850915776438143841777)
      ·
        refine ⟨108157388186832328607881333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144209850915776438143841777 108157388186832328607881333)
        ·
          refine ⟨10139755142515530806988875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 108157388186832328607881333 10139755142515530806988875)
          ·
            refine ⟨15209632713773296210483313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10139755142515530806988875 15209632713773296210483313)
            ·
              refine ⟨11407224535329972157862485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15209632713773296210483313 11407224535329972157862485)
              ·
                refine ⟨133678412523398111224951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11407224535329972157862485 133678412523398111224951)
                ·
                  rfl

theorem cell22_3514560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 8].length) (baseStart_3514560 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3514560 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3514560 prefixEnd_3514560 := by exact prefixLift 3514560
  have htrace : WordTrace (prefixWord ++ tailWord_3514560) baseStart_3514560 baseEnd_3514560 := by
    simpa [prefixWord, tailWord_3514560, baseEnd_3514560] using wordTrace_append hprefix tailTrace_3514560
  have hstable : (prefixWord ++ tailWord_3514560).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3514560).length < 2 ^ (prefixWord ++ tailWord_3514560).sum := by decide
  have hdescent : baseEnd_3514560 < baseStart_3514560 := by decide
  rcases family_descends (prefixWord ++ tailWord_3514560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3514581 : List Nat := [1, 3, 2, 4, 2, 1, 2, 2, 2, 3]
def baseStart_3514581 : Nat := 118140960795 + 3514581 * 2 ^ 59
def prefixEnd_3514581 : Nat := 4983230072969 + 3 ^ 40 * 3514581 * 2
def baseEnd_3514581 : Nat := 1203112901439745946249495

theorem tailTrace_3514581 : CollatzResearch.WordTrace tailWord_3514581 prefixEnd_3514581 1203112901439745946249495 := by
  unfold tailWord_3514581
  simp only [CollatzResearch.WordTrace]
  refine ⟨128187300080280754492151597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85458200053520502994767731 128187300080280754492151597)
  ·
    refine ⟨48070237530105282934556849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128187300080280754492151597 48070237530105282934556849)
    ·
      refine ⟨36052678147578962200917637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48070237530105282934556849 36052678147578962200917637)
      ·
        refine ⟨6759877152671055412672057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36052678147578962200917637 6759877152671055412672057)
        ·
          refine ⟨5069907864503291559504043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6759877152671055412672057 5069907864503291559504043)
          ·
            refine ⟨7604861796754937339256065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5069907864503291559504043 7604861796754937339256065)
            ·
              refine ⟨5703646347566203004442049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7604861796754937339256065 5703646347566203004442049)
              ·
                refine ⟨4277734760674652253331537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5703646347566203004442049 4277734760674652253331537)
                ·
                  refine ⟨3208301070505989189998653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4277734760674652253331537 3208301070505989189998653)
                  ·
                    refine ⟨1203112901439745946249495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3208301070505989189998653 1203112901439745946249495)
                    ·
                      rfl

theorem cell22_3514581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 2, 2, 2, 3].length) (baseStart_3514581 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3514581 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3514581 prefixEnd_3514581 := by exact prefixLift 3514581
  have htrace : WordTrace (prefixWord ++ tailWord_3514581) baseStart_3514581 baseEnd_3514581 := by
    simpa [prefixWord, tailWord_3514581, baseEnd_3514581] using wordTrace_append hprefix tailTrace_3514581
  have hstable : (prefixWord ++ tailWord_3514581).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3514581).length < 2 ^ (prefixWord ++ tailWord_3514581).sum := by decide
  have hdescent : baseEnd_3514581 < baseStart_3514581 := by decide
  rcases family_descends (prefixWord ++ tailWord_3514581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3514592 : List Nat := [2, 1, 1, 3, 1, 3, 2, 3, 3, 3]
def baseStart_3514592 : Nat := 118140960795 + 3514592 * 2 ^ 59
def prefixEnd_3514592 : Nat := 4983230072969 + 3 ^ 40 * 3514592 * 2
def baseEnd_3514592 : Nat := 1203116666964545584224461

theorem tailTrace_3514592 : CollatzResearch.WordTrace tailWord_3514592 prefixEnd_3514592 1203116666964545584224461 := by
  unfold tailWord_3514592
  simp only [CollatzResearch.WordTrace]
  refine ⟨64093850641620451685401015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85458467522160602247201353 64093850641620451685401015)
  ·
    refine ⟨96140775962430677528101523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64093850641620451685401015 96140775962430677528101523)
    ·
      refine ⟨144211163943646016292152285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96140775962430677528101523 144211163943646016292152285)
      ·
        refine ⟨54079186478867256109557107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144211163943646016292152285 54079186478867256109557107)
        ·
          refine ⟨81118779718300884164335661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54079186478867256109557107 81118779718300884164335661)
          ·
            refine ⟨30419542394362831561625873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81118779718300884164335661 30419542394362831561625873)
            ·
              refine ⟨22814656795772123671219405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30419542394362831561625873 22814656795772123671219405)
              ·
                refine ⟨8555496298414546376707277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22814656795772123671219405 8555496298414546376707277)
                ·
                  refine ⟨3208311111905454891265229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8555496298414546376707277 3208311111905454891265229)
                  ·
                    refine ⟨1203116666964545584224461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3208311111905454891265229 1203116666964545584224461)
                    ·
                      rfl

theorem cell22_3514592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 3, 3, 3].length) (baseStart_3514592 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3514592 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3514592 prefixEnd_3514592 := by exact prefixLift 3514592
  have htrace : WordTrace (prefixWord ++ tailWord_3514592) baseStart_3514592 baseEnd_3514592 := by
    simpa [prefixWord, tailWord_3514592, baseEnd_3514592] using wordTrace_append hprefix tailTrace_3514592
  have hstable : (prefixWord ++ tailWord_3514592).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3514592).length < 2 ^ (prefixWord ++ tailWord_3514592).sum := by decide
  have hdescent : baseEnd_3514592 < baseStart_3514592 := by decide
  rcases family_descends (prefixWord ++ tailWord_3514592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3514622 : List Nat := [4, 2, 2, 1, 1, 1, 2, 2, 7]
def baseStart_3514622 : Nat := 118140960795 + 3514622 * 2 ^ 59
def prefixEnd_3514622 : Nat := 4983230072969 + 3 ^ 40 * 3514622 * 2
def baseEnd_3514622 : Nat := 401042312192545168658123

theorem tailTrace_3514622 : CollatzResearch.WordTrace tailWord_3514622 prefixEnd_3514622 401042312192545168658123 := by
  unfold tailWord_3514622
  simp only [CollatzResearch.WordTrace]
  refine ⟨16023599434141527311799265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85459196982088145662929413 16023599434141527311799265)
  ·
    refine ⟨12017699575606145483849449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16023599434141527311799265 12017699575606145483849449)
    ·
      refine ⟨9013274681704609112887087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12017699575606145483849449 9013274681704609112887087)
      ·
        refine ⟨13519912022556913669330631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9013274681704609112887087 13519912022556913669330631)
        ·
          refine ⟨20279868033835370503995947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13519912022556913669330631 20279868033835370503995947)
          ·
            refine ⟨30419802050753055755993921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20279868033835370503995947 30419802050753055755993921)
            ·
              refine ⟨22814851538064791816995441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30419802050753055755993921 22814851538064791816995441)
              ·
                refine ⟨17111138653548593862746581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22814851538064791816995441 17111138653548593862746581)
                ·
                  refine ⟨401042312192545168658123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17111138653548593862746581 401042312192545168658123)
                  ·
                    rfl

theorem cell22_3514622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 2, 7].length) (baseStart_3514622 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3514622 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3514622 prefixEnd_3514622 := by exact prefixLift 3514622
  have htrace : WordTrace (prefixWord ++ tailWord_3514622) baseStart_3514622 baseEnd_3514622 := by
    simpa [prefixWord, tailWord_3514622, baseEnd_3514622] using wordTrace_append hprefix tailTrace_3514622
  have hstable : (prefixWord ++ tailWord_3514622).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3514622).length < 2 ^ (prefixWord ++ tailWord_3514622).sum := by decide
  have hdescent : baseEnd_3514622 < baseStart_3514622 := by decide
  rcases family_descends (prefixWord ++ tailWord_3514622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3514802 : List Nat := [3, 2, 1, 1, 1, 1, 3, 2, 8]
def baseStart_3514802 : Nat := 118140960795 + 3514802 * 2 ^ 59
def prefixEnd_3514802 : Nat := 4983230072969 + 3 ^ 40 * 3514802 * 2
def baseEnd_3514802 : Nat := 401062851418725012157939

theorem tailTrace_3514802 : CollatzResearch.WordTrace tailWord_3514802 prefixEnd_3514802 401062851418725012157939 := by
  unfold tailWord_3514802
  simp only [CollatzResearch.WordTrace]
  refine ⟨32048840153120027308986665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85463573741653406157297773 32048840153120027308986665)
  ·
    refine ⟨24036630114840020481739999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32048840153120027308986665 24036630114840020481739999)
    ·
      refine ⟨36054945172260030722609999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24036630114840020481739999 36054945172260030722609999)
      ·
        refine ⟨54082417758390046083914999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36054945172260030722609999 54082417758390046083914999)
        ·
          refine ⟨81123626637585069125872499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54082417758390046083914999 81123626637585069125872499)
          ·
            refine ⟨121685439956377603688808749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81123626637585069125872499 121685439956377603688808749)
            ·
              refine ⟨45632039983641601383303281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 121685439956377603688808749 45632039983641601383303281)
              ·
                refine ⟨34224029987731201037477461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45632039983641601383303281 34224029987731201037477461)
                ·
                  refine ⟨401062851418725012157939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34224029987731201037477461 401062851418725012157939)
                  ·
                    rfl

theorem cell22_3514802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 2, 8].length) (baseStart_3514802 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3514802 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3514802 prefixEnd_3514802 := by exact prefixLift 3514802
  have htrace : WordTrace (prefixWord ++ tailWord_3514802) baseStart_3514802 baseEnd_3514802 := by
    simpa [prefixWord, tailWord_3514802, baseEnd_3514802] using wordTrace_append hprefix tailTrace_3514802
  have hstable : (prefixWord ++ tailWord_3514802).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3514802).length < 2 ^ (prefixWord ++ tailWord_3514802).sum := by decide
  have hdescent : baseEnd_3514802 < baseStart_3514802 := by decide
  rcases family_descends (prefixWord ++ tailWord_3514802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3514838 : List Nat := [5, 2, 1, 1, 1, 1, 4, 2, 1, 4]
def baseStart_3514838 : Nat := 118140960795 + 3514838 * 2 ^ 59
def prefixEnd_3514838 : Nat := 4983230072969 + 3 ^ 40 * 3514838 * 2
def baseEnd_3514838 : Nat := 1203200877791882942573707

theorem tailTrace_3514838 : CollatzResearch.WordTrace tailWord_3514838 prefixEnd_3514838 1203200877791882942573707 := by
  unfold tailWord_3514838
  simp only [CollatzResearch.WordTrace]
  refine ⟨8012292102521855461516073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 85464449093566458256171445 8012292102521855461516073)
  ·
    refine ⟨6009219076891391596137055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8012292102521855461516073 6009219076891391596137055)
    ·
      refine ⟨9013828615337087394205583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6009219076891391596137055 9013828615337087394205583)
      ·
        refine ⟨13520742923005631091308375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9013828615337087394205583 13520742923005631091308375)
        ·
          refine ⟨20281114384508446636962563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13520742923005631091308375 20281114384508446636962563)
          ·
            refine ⟨30421671576762669955443845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20281114384508446636962563 30421671576762669955443845)
            ·
              refine ⟨5704063420643000616645721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30421671576762669955443845 5704063420643000616645721)
              ·
                refine ⟨4278047565482250462484291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5704063420643000616645721 4278047565482250462484291)
                ·
                  refine ⟨6417071348223375693726437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4278047565482250462484291 6417071348223375693726437)
                  ·
                    refine ⟨1203200877791882942573707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6417071348223375693726437 1203200877791882942573707)
                    ·
                      rfl

theorem cell22_3514838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 4, 2, 1, 4].length) (baseStart_3514838 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3514838 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3514838 prefixEnd_3514838 := by exact prefixLift 3514838
  have htrace : WordTrace (prefixWord ++ tailWord_3514838) baseStart_3514838 baseEnd_3514838 := by
    simpa [prefixWord, tailWord_3514838, baseEnd_3514838] using wordTrace_append hprefix tailTrace_3514838
  have hstable : (prefixWord ++ tailWord_3514838).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3514838).length < 2 ^ (prefixWord ++ tailWord_3514838).sum := by decide
  have hdescent : baseEnd_3514838 < baseStart_3514838 := by decide
  rcases family_descends (prefixWord ++ tailWord_3514838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3514849 : List Nat := [1, 2, 3, 1, 2, 2, 2, 3, 2, 4]
def baseStart_3514849 : Nat := 118140960795 + 3514849 * 2 ^ 59
def prefixEnd_3514849 : Nat := 4983230072969 + 3 ^ 40 * 3514849 * 2
def baseEnd_3514849 : Nat := 1203204643316682580548673

theorem tailTrace_3514849 : CollatzResearch.WordTrace tailWord_3514849 prefixEnd_3514849 1203204643316682580548673 := by
  unfold tailWord_3514849
  simp only [CollatzResearch.WordTrace]
  refine ⟨128197074843309836262907601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85464716562206557508605067 128197074843309836262907601)
  ·
    refine ⟨96147806132482377197180701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128197074843309836262907601 96147806132482377197180701)
    ·
      refine ⟨36055427299680891448942763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96147806132482377197180701 36055427299680891448942763)
      ·
        refine ⟨54083140949521337173414145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36055427299680891448942763 54083140949521337173414145)
        ·
          refine ⟨40562355712141002880060609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54083140949521337173414145 40562355712141002880060609)
          ·
            refine ⟨30421766784105752160045457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40562355712141002880060609 30421766784105752160045457)
            ·
              refine ⟨22816325088079314120034093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30421766784105752160045457 22816325088079314120034093)
              ·
                refine ⟨8556121908029742795012785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22816325088079314120034093 8556121908029742795012785)
                ·
                  refine ⟨6417091431022307096259589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8556121908029742795012785 6417091431022307096259589)
                  ·
                    refine ⟨1203204643316682580548673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6417091431022307096259589 1203204643316682580548673)
                    ·
                      rfl

theorem cell22_3514849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 3, 2, 4].length) (baseStart_3514849 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3514849 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3514849 prefixEnd_3514849 := by exact prefixLift 3514849
  have htrace : WordTrace (prefixWord ++ tailWord_3514849) baseStart_3514849 baseEnd_3514849 := by
    simpa [prefixWord, tailWord_3514849, baseEnd_3514849] using wordTrace_append hprefix tailTrace_3514849
  have hstable : (prefixWord ++ tailWord_3514849).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3514849).length < 2 ^ (prefixWord ++ tailWord_3514849).sum := by decide
  have hdescent : baseEnd_3514849 < baseStart_3514849 := by decide
  rcases family_descends (prefixWord ++ tailWord_3514849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3514913 : List Nat := [1, 2, 3, 2, 2, 1, 2, 5, 1, 3]
def baseStart_3514913 : Nat := 118140960795 + 3514913 * 2 ^ 59
def prefixEnd_3514913 : Nat := 4983230072969 + 3 ^ 40 * 3514913 * 2
def baseEnd_3514913 : Nat := 1203226551824607746948477

theorem tailTrace_3514913 : CollatzResearch.WordTrace tailWord_3514913 prefixEnd_3514913 1203226551824607746948477 := by
  unfold tailWord_3514913
  simp only [CollatzResearch.WordTrace]
  refine ⟨128199409115077975193237393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85466272743385316795491595 128199409115077975193237393)
  ·
    refine ⟨96149556836308481394928045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128199409115077975193237393 96149556836308481394928045)
    ·
      refine ⟨36056083813615680523098017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96149556836308481394928045 36056083813615680523098017)
      ·
        refine ⟨27042062860211760392323513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36056083813615680523098017 27042062860211760392323513)
        ·
          refine ⟨20281547145158820294242635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27042062860211760392323513 20281547145158820294242635)
          ·
            refine ⟨30422320717738230441363953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20281547145158820294242635 30422320717738230441363953)
            ·
              refine ⟨22816740538303672831022965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30422320717738230441363953 22816740538303672831022965)
              ·
                refine ⟨2139069425465969327908403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22816740538303672831022965 2139069425465969327908403)
                ·
                  refine ⟨3208604138198953991862605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2139069425465969327908403 3208604138198953991862605)
                  ·
                    refine ⟨1203226551824607746948477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3208604138198953991862605 1203226551824607746948477)
                    ·
                      rfl

theorem cell22_3514913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 5, 1, 3].length) (baseStart_3514913 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3514913 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3514913 prefixEnd_3514913 := by exact prefixLift 3514913
  have htrace : WordTrace (prefixWord ++ tailWord_3514913) baseStart_3514913 baseEnd_3514913 := by
    simpa [prefixWord, tailWord_3514913, baseEnd_3514913] using wordTrace_append hprefix tailTrace_3514913
  have hstable : (prefixWord ++ tailWord_3514913).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3514913).length < 2 ^ (prefixWord ++ tailWord_3514913).sum := by decide
  have hdescent : baseEnd_3514913 < baseStart_3514913 := by decide
  rcases family_descends (prefixWord ++ tailWord_3514913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
