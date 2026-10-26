import V185TrunkScan23Chunk1371

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_8125815 : List Nat := [1, 1, 3, 1, 1, 2, 4, 3, 1, 4, 2]
def baseStart_8125815 : Nat := 118140960795 + 8125815 * 2 ^ 59
def prefixEnd_8125815 : Nat := 4983230072969 + 3 ^ 40 * 8125815 * 2
def baseEnd_8125815 : Nat := 4172448804514230445142563

theorem tailTrace_8125815 : CollatzResearch.WordTrace tailWord_8125815 prefixEnd_8125815 4172448804514230445142563 := by
  unfold tailWord_8125815
  simp only [CollatzResearch.WordTrace]
  refine ⟨296372821056567508560402899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197581880704378339040268599 296372821056567508560402899)
  ·
    refine ⟨444559231584851262840604349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296372821056567508560402899 444559231584851262840604349)
    ·
      refine ⟨166709711844319223565226631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 444559231584851262840604349 166709711844319223565226631)
      ·
        refine ⟨250064567766478835347839947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166709711844319223565226631 250064567766478835347839947)
        ·
          refine ⟨375096851649718253021759921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250064567766478835347839947 375096851649718253021759921)
          ·
            refine ⟨281322638737288689766319941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 375096851649718253021759921 281322638737288689766319941)
            ·
              refine ⟨52747994763241629331184989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 281322638737288689766319941 52747994763241629331184989)
              ·
                refine ⟨19780498036215610999194371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52747994763241629331184989 19780498036215610999194371)
                ·
                  refine ⟨29670747054323416498791557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19780498036215610999194371 29670747054323416498791557)
                  ·
                    refine ⟨5563265072685640593523417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29670747054323416498791557 5563265072685640593523417)
                    ·
                      refine ⟨4172448804514230445142563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5563265072685640593523417 4172448804514230445142563)
                      ·
                        rfl

theorem cell23_8125815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 4, 2].length) (baseStart_8125815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8125815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8125815 prefixEnd_8125815 := by exact prefixLift 8125815
  have htrace : WordTrace (prefixWord ++ tailWord_8125815) baseStart_8125815 baseEnd_8125815 := by
    simpa [prefixWord, tailWord_8125815, baseEnd_8125815] using wordTrace_append hprefix tailTrace_8125815
  have hstable : (prefixWord ++ tailWord_8125815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8125815).length < 2 ^ (prefixWord ++ tailWord_8125815).sum := by decide
  have hdescent : baseEnd_8125815 < baseStart_8125815 := by decide
  rcases family_descends (prefixWord ++ tailWord_8125815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8125818 : List Nat := [3, 1, 1, 1, 1, 1, 2, 4, 2, 4, 3]
def baseStart_8125818 : Nat := 118140960795 + 8125818 * 2 ^ 59
def prefixEnd_8125818 : Nat := 4983230072969 + 3 ^ 40 * 8125818 * 2
def baseEnd_8125818 : Nat := 4172450344956193933405049

theorem tailTrace_8125818 : CollatzResearch.WordTrace tailWord_8125818 prefixEnd_8125818 4172450344956193933405049 := by
  unfold tailWord_8125818
  simp only [CollatzResearch.WordTrace]
  refine ⟨74093232618889160018190527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197581953650371093381841405 74093232618889160018190527)
  ·
    refine ⟨111139848928333740027285791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74093232618889160018190527 111139848928333740027285791)
    ·
      refine ⟨166709773392500610040928687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111139848928333740027285791 166709773392500610040928687)
      ·
        refine ⟨250064660088750915061393031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166709773392500610040928687 250064660088750915061393031)
        ·
          refine ⟨375096990133126372592089547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250064660088750915061393031 375096990133126372592089547)
          ·
            refine ⟨562645485199689558888134321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 375096990133126372592089547 562645485199689558888134321)
            ·
              refine ⟨421984113899767169166100741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 562645485199689558888134321 421984113899767169166100741)
              ·
                refine ⟨79122021356206344218643889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 421984113899767169166100741 79122021356206344218643889)
                ·
                  refine ⟨59341516017154758163982917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79122021356206344218643889 59341516017154758163982917)
                  ·
                    refine ⟨11126534253216517155746797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59341516017154758163982917 11126534253216517155746797)
                    ·
                      refine ⟨4172450344956193933405049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11126534253216517155746797 4172450344956193933405049)
                      ·
                        rfl

theorem cell23_8125818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 4, 2, 4, 3].length) (baseStart_8125818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8125818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8125818 prefixEnd_8125818 := by exact prefixLift 8125818
  have htrace : WordTrace (prefixWord ++ tailWord_8125818) baseStart_8125818 baseEnd_8125818 := by
    simpa [prefixWord, tailWord_8125818, baseEnd_8125818] using wordTrace_append hprefix tailTrace_8125818
  have hstable : (prefixWord ++ tailWord_8125818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8125818).length < 2 ^ (prefixWord ++ tailWord_8125818).sum := by decide
  have hdescent : baseEnd_8125818 < baseStart_8125818 := by decide
  rcases family_descends (prefixWord ++ tailWord_8125818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8125832 : List Nat := [2, 1, 3, 3, 1, 3, 1, 2, 1, 4, 2]
def baseStart_8125832 : Nat := 118140960795 + 8125832 * 2 ^ 59
def prefixEnd_8125832 : Nat := 4983230072969 + 3 ^ 40 * 8125832 * 2
def baseEnd_8125832 : Nat := 4172457533685356878629985

theorem tailTrace_8125832 : CollatzResearch.WordTrace tailWord_8125832 prefixEnd_8125832 4172457533685356878629985 := by
  unfold tailWord_8125832
  simp only [CollatzResearch.WordTrace]
  refine ⟨148186720548752960231885875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197582294065003946975847833 148186720548752960231885875)
  ·
    refine ⟨222280080823129440347828813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148186720548752960231885875 222280080823129440347828813)
    ·
      refine ⟨83355030308673540130435805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 222280080823129440347828813 83355030308673540130435805)
      ·
        refine ⟨31258136365752577548913427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83355030308673540130435805 31258136365752577548913427)
        ·
          refine ⟨46887204548628866323370141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31258136365752577548913427 46887204548628866323370141)
          ·
            refine ⟨17582701705735824871263803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46887204548628866323370141 17582701705735824871263803)
            ·
              refine ⟨26374052558603737306895705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17582701705735824871263803 26374052558603737306895705)
              ·
                refine ⟨19780539418952802980171779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26374052558603737306895705 19780539418952802980171779)
                ·
                  refine ⟨29670809128429204470257669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19780539418952802980171779 29670809128429204470257669)
                  ·
                    refine ⟨5563276711580475838173313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29670809128429204470257669 5563276711580475838173313)
                    ·
                      refine ⟨4172457533685356878629985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5563276711580475838173313 4172457533685356878629985)
                      ·
                        rfl

theorem cell23_8125832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 2, 1, 4, 2].length) (baseStart_8125832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8125832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8125832 prefixEnd_8125832 := by exact prefixLift 8125832
  have htrace : WordTrace (prefixWord ++ tailWord_8125832) baseStart_8125832 baseEnd_8125832 := by
    simpa [prefixWord, tailWord_8125832, baseEnd_8125832] using wordTrace_append hprefix tailTrace_8125832
  have hstable : (prefixWord ++ tailWord_8125832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8125832).length < 2 ^ (prefixWord ++ tailWord_8125832).sum := by decide
  have hdescent : baseEnd_8125832 < baseStart_8125832 := by decide
  rcases family_descends (prefixWord ++ tailWord_8125832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8125849 : List Nat := [1, 2, 1, 2, 1, 6, 2, 2, 2, 2, 2]
def baseStart_8125849 : Nat := 118140960795 + 8125849 * 2 ^ 59
def prefixEnd_8125849 : Nat := 4983230072969 + 3 ^ 40 * 8125849 * 2
def baseEnd_8125849 : Nat := 4172466262856483312117407

theorem tailTrace_8125849 : CollatzResearch.WordTrace tailWord_8125849 prefixEnd_8125849 4172466262856483312117407 := by
  unfold tailWord_8125849
  simp only [CollatzResearch.WordTrace]
  refine ⟨296374061138444332367140601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197582707425629554911427067 296374061138444332367140601)
  ·
    refine ⟨222280545853833249275355451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296374061138444332367140601 222280545853833249275355451)
    ·
      refine ⟨333420818780749873913033177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222280545853833249275355451 333420818780749873913033177)
      ·
        refine ⟨250065614085562405434774883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 333420818780749873913033177 250065614085562405434774883)
        ·
          refine ⟨375098421128343608152162325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250065614085562405434774883 375098421128343608152162325)
          ·
            refine ⟨17582738490391106632132609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 375098421128343608152162325 17582738490391106632132609)
            ·
              refine ⟨13187053867793329974099457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17582738490391106632132609 13187053867793329974099457)
              ·
                refine ⟨9890290400844997480574593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13187053867793329974099457 9890290400844997480574593)
                ·
                  refine ⟨7417717800633748110430945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9890290400844997480574593 7417717800633748110430945)
                  ·
                    refine ⟨5563288350475311082823209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7417717800633748110430945 5563288350475311082823209)
                    ·
                      refine ⟨4172466262856483312117407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5563288350475311082823209 4172466262856483312117407)
                      ·
                        rfl

theorem cell23_8125849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 2, 2, 2, 2, 2].length) (baseStart_8125849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8125849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8125849 prefixEnd_8125849 := by exact prefixLift 8125849
  have htrace : WordTrace (prefixWord ++ tailWord_8125849) baseStart_8125849 baseEnd_8125849 := by
    simpa [prefixWord, tailWord_8125849, baseEnd_8125849] using wordTrace_append hprefix tailTrace_8125849
  have hstable : (prefixWord ++ tailWord_8125849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8125849).length < 2 ^ (prefixWord ++ tailWord_8125849).sum := by decide
  have hdescent : baseEnd_8125849 < baseStart_8125849 := by decide
  rcases family_descends (prefixWord ++ tailWord_8125849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8125868 : List Nat := [2, 2, 1, 1, 1, 1, 4, 2, 4, 5]
def baseStart_8125868 : Nat := 118140960795 + 8125868 * 2 ^ 59
def prefixEnd_8125868 : Nat := 4983230072969 + 3 ^ 40 * 8125868 * 2
def baseEnd_8125868 : Nat := 1390825339662972912593273

theorem tailTrace_8125868 : CollatzResearch.WordTrace tailWord_8125868 prefixEnd_8125868 1390825339662972912593273 := by
  unfold tailWord_8125868
  simp only [CollatzResearch.WordTrace]
  refine ⟨148187377062687749306041129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197583169416916999074721505 148187377062687749306041129)
  ·
    refine ⟨111140532797015811979530847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148187377062687749306041129 111140532797015811979530847)
    ·
      refine ⟨166710799195523717969296271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111140532797015811979530847 166710799195523717969296271)
      ·
        refine ⟨250066198793285576953944407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166710799195523717969296271 250066198793285576953944407)
        ·
          refine ⟨375099298189928365430916611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250066198793285576953944407 375099298189928365430916611)
          ·
            refine ⟨562648947284892548146374917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 375099298189928365430916611 562648947284892548146374917)
            ·
              refine ⟨105496677615917352777445297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 562648947284892548146374917 105496677615917352777445297)
              ·
                refine ⟨79122508211938014583083973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105496677615917352777445297 79122508211938014583083973)
                ·
                  refine ⟨14835470289738377734328245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79122508211938014583083973 14835470289738377734328245)
                  ·
                    refine ⟨1390825339662972912593273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14835470289738377734328245 1390825339662972912593273)
                    ·
                      rfl

theorem cell23_8125868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 5].length) (baseStart_8125868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8125868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8125868 prefixEnd_8125868 := by exact prefixLift 8125868
  have htrace : WordTrace (prefixWord ++ tailWord_8125868) baseStart_8125868 baseEnd_8125868 := by
    simpa [prefixWord, tailWord_8125868, baseEnd_8125868] using wordTrace_append hprefix tailTrace_8125868
  have hstable : (prefixWord ++ tailWord_8125868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8125868).length < 2 ^ (prefixWord ++ tailWord_8125868).sum := by decide
  have hdescent : baseEnd_8125868 < baseStart_8125868 := by decide
  rcases family_descends (prefixWord ++ tailWord_8125868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8125942 : List Nat := [5, 1, 1, 1, 2, 2, 2, 1, 1, 4, 3]
def baseStart_8125942 : Nat := 118140960795 + 8125942 * 2 ^ 59
def prefixEnd_8125942 : Nat := 4983230072969 + 3 ^ 40 * 8125942 * 2
def baseEnd_8125942 : Nat := 4172514016557351448254479

theorem tailTrace_8125942 : CollatzResearch.WordTrace tailWord_8125942 prefixEnd_8125942 4172514016557351448254479 := by
  unfold tailWord_8125942
  simp only [CollatzResearch.WordTrace]
  refine ⟨18523590820444213078142255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 197584968751404939500184053 18523590820444213078142255)
  ·
    refine ⟨27785386230666319617213383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18523590820444213078142255 27785386230666319617213383)
    ·
      refine ⟨41678079345999479425820075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27785386230666319617213383 41678079345999479425820075)
      ·
        refine ⟨62517119018999219138730113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41678079345999479425820075 62517119018999219138730113)
        ·
          refine ⟨46887839264249414354047585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62517119018999219138730113 46887839264249414354047585)
          ·
            refine ⟨35165879448187060765535689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46887839264249414354047585 35165879448187060765535689)
            ·
              refine ⟨26374409586140295574151767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35165879448187060765535689 26374409586140295574151767)
              ·
                refine ⟨39561614379210443361227651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26374409586140295574151767 39561614379210443361227651)
                ·
                  refine ⟨59342421568815665041841477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39561614379210443361227651 59342421568815665041841477)
                  ·
                    refine ⟨11126704044152937195345277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59342421568815665041841477 11126704044152937195345277)
                    ·
                      refine ⟨4172514016557351448254479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11126704044152937195345277 4172514016557351448254479)
                      ·
                        rfl

theorem cell23_8125942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 1, 1, 4, 3].length) (baseStart_8125942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8125942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8125942 prefixEnd_8125942 := by exact prefixLift 8125942
  have htrace : WordTrace (prefixWord ++ tailWord_8125942) baseStart_8125942 baseEnd_8125942 := by
    simpa [prefixWord, tailWord_8125942, baseEnd_8125942] using wordTrace_append hprefix tailTrace_8125942
  have hstable : (prefixWord ++ tailWord_8125942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8125942).length < 2 ^ (prefixWord ++ tailWord_8125942).sum := by decide
  have hdescent : baseEnd_8125942 < baseStart_8125942 := by decide
  rcases family_descends (prefixWord ++ tailWord_8125942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8125949 : List Nat := [1, 4, 1, 1, 1, 4, 3, 3, 1, 4]
def baseStart_8125949 : Nat := 118140960795 + 8125949 * 2 ^ 59
def prefixEnd_8125949 : Nat := 4983230072969 + 3 ^ 40 * 8125949 * 2
def baseEnd_8125949 : Nat := 1390839203640644306955649

theorem tailTrace_8125949 : CollatzResearch.WordTrace tailWord_8125949 prefixEnd_8125949 1390839203640644306955649 := by
  unfold tailWord_8125949
  simp only [CollatzResearch.WordTrace]
  refine ⟨296377708438082049445780901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197585138958721366297187267 296377708438082049445780901)
  ·
    refine ⟨55570820332140384271083919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 296377708438082049445780901 55570820332140384271083919)
    ·
      refine ⟨83356230498210576406625879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55570820332140384271083919 83356230498210576406625879)
      ·
        refine ⟨125034345747315864609938819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83356230498210576406625879 125034345747315864609938819)
        ·
          refine ⟨187551518620973796914908229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125034345747315864609938819 187551518620973796914908229)
          ·
            refine ⟨35165909741432586921545293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 187551518620973796914908229 35165909741432586921545293)
            ·
              refine ⟨13187216153037220095579485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35165909741432586921545293 13187216153037220095579485)
              ·
                refine ⟨4945206057388957535842307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13187216153037220095579485 4945206057388957535842307)
                ·
                  refine ⟨7417809086083436303763461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4945206057388957535842307 7417809086083436303763461)
                  ·
                    refine ⟨1390839203640644306955649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7417809086083436303763461 1390839203640644306955649)
                    ·
                      rfl

theorem cell23_8125949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 3, 3, 1, 4].length) (baseStart_8125949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8125949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8125949 prefixEnd_8125949 := by exact prefixLift 8125949
  have htrace : WordTrace (prefixWord ++ tailWord_8125949) baseStart_8125949 baseEnd_8125949 := by
    simpa [prefixWord, tailWord_8125949, baseEnd_8125949] using wordTrace_append hprefix tailTrace_8125949
  have hstable : (prefixWord ++ tailWord_8125949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8125949).length < 2 ^ (prefixWord ++ tailWord_8125949).sum := by decide
  have hdescent : baseEnd_8125949 < baseStart_8125949 := by decide
  rcases family_descends (prefixWord ++ tailWord_8125949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8125966 : List Nat := [4, 1, 1, 2, 5, 1, 1, 1, 3, 4]
def baseStart_8125966 : Nat := 118140960795 + 8125966 * 2 ^ 59
def prefixEnd_8125966 : Nat := 4983230072969 + 3 ^ 40 * 8125966 * 2
def baseEnd_8125966 : Nat := 1390842113364353118118123

theorem tailTrace_8125966 : CollatzResearch.WordTrace tailWord_8125966 prefixEnd_8125966 1390842113364353118118123 := by
  unfold tailWord_8125966
  simp only [CollatzResearch.WordTrace]
  refine ⟨37047291059877557668643719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 197585552319346974232766501 37047291059877557668643719)
  ·
    refine ⟨55570936589816336502965579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37047291059877557668643719 55570936589816336502965579)
    ·
      refine ⟨83356404884724504754448369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55570936589816336502965579 83356404884724504754448369)
      ·
        refine ⟨62517303663543378565836277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83356404884724504754448369 62517303663543378565836277)
        ·
          refine ⟨5860997218457191740547151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 62517303663543378565836277 5860997218457191740547151)
          ·
            refine ⟨8791495827685787610820727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5860997218457191740547151 8791495827685787610820727)
            ·
              refine ⟨13187243741528681416231091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8791495827685787610820727 13187243741528681416231091)
              ·
                refine ⟨19780865612293022124346637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13187243741528681416231091 19780865612293022124346637)
                ·
                  refine ⟨7417824604609883296629989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19780865612293022124346637 7417824604609883296629989)
                  ·
                    refine ⟨1390842113364353118118123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7417824604609883296629989 1390842113364353118118123)
                    ·
                      rfl

theorem cell23_8125966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 1, 1, 3, 4].length) (baseStart_8125966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8125966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8125966 prefixEnd_8125966 := by exact prefixLift 8125966
  have htrace : WordTrace (prefixWord ++ tailWord_8125966) baseStart_8125966 baseEnd_8125966 := by
    simpa [prefixWord, tailWord_8125966, baseEnd_8125966] using wordTrace_append hprefix tailTrace_8125966
  have hstable : (prefixWord ++ tailWord_8125966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8125966).length < 2 ^ (prefixWord ++ tailWord_8125966).sum := by decide
  have hdescent : baseEnd_8125966 < baseStart_8125966 := by decide
  rcases family_descends (prefixWord ++ tailWord_8125966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8126005 : List Nat := [1, 3, 3, 1, 1, 3, 1, 1, 3, 6]
def baseStart_8126005 : Nat := 118140960795 + 8126005 * 2 ^ 59
def prefixEnd_8126005 : Nat := 4983230072969 + 3 ^ 40 * 8126005 * 2
def baseEnd_8126005 : Nat := 1390848788612861567255563

theorem tailTrace_8126005 : CollatzResearch.WordTrace tailWord_8126005 prefixEnd_8126005 1390848788612861567255563 := by
  unfold tailWord_8126005
  simp only [CollatzResearch.WordTrace]
  refine ⟨296379750925879171009819469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197586500617252780673212979 296379750925879171009819469)
  ·
    refine ⟨111142406597204689128682301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 296379750925879171009819469 111142406597204689128682301)
    ·
      refine ⟨41678402473951758423255863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111142406597204689128682301 41678402473951758423255863)
      ·
        refine ⟨62517603710927637634883795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41678402473951758423255863 62517603710927637634883795)
        ·
          refine ⟨93776405566391456452325693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62517603710927637634883795 93776405566391456452325693)
          ·
            refine ⟨35166152087396796169622135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93776405566391456452325693 35166152087396796169622135)
            ·
              refine ⟨52749228131095194254433203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35166152087396796169622135 52749228131095194254433203)
              ·
                refine ⟨79123842196642791381649805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52749228131095194254433203 79123842196642791381649805)
                ·
                  refine ⟨29671440823741046768118677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79123842196642791381649805 29671440823741046768118677)
                  ·
                    refine ⟨1390848788612861567255563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29671440823741046768118677 1390848788612861567255563)
                    ·
                      rfl

theorem cell23_8126005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 1, 3, 6].length) (baseStart_8126005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8126005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8126005 prefixEnd_8126005 := by exact prefixLift 8126005
  have htrace : WordTrace (prefixWord ++ tailWord_8126005) baseStart_8126005 baseEnd_8126005 := by
    simpa [prefixWord, tailWord_8126005, baseEnd_8126005] using wordTrace_append hprefix tailTrace_8126005
  have hstable : (prefixWord ++ tailWord_8126005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8126005).length < 2 ^ (prefixWord ++ tailWord_8126005).sum := by decide
  have hdescent : baseEnd_8126005 < baseStart_8126005 := by decide
  rcases family_descends (prefixWord ++ tailWord_8126005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8126009 : List Nat := [1, 2, 1, 5, 1, 3, 3, 1, 1, 5]
def baseStart_8126009 : Nat := 118140960795 + 8126009 * 2 ^ 59
def prefixEnd_8126009 : Nat := 4983230072969 + 3 ^ 40 * 8126009 * 2
def baseEnd_8126009 : Nat := 1390849473253734228705557

theorem tailTrace_8126009 : CollatzResearch.WordTrace tailWord_8126009 prefixEnd_8126009 1390849473253734228705557 := by
  unfold tailWord_8126009
  simp only [CollatzResearch.WordTrace]
  refine ⟨296379896817864679692965081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197586597878576453128643387 296379896817864679692965081)
  ·
    refine ⟨222284922613398509769723811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296379896817864679692965081 222284922613398509769723811)
    ·
      refine ⟨333427383920097764654585717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222284922613398509769723811 333427383920097764654585717)
      ·
        refine ⟨31258817242509165436367411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 333427383920097764654585717 31258817242509165436367411)
        ·
          refine ⟨46888225863763748154551117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31258817242509165436367411 46888225863763748154551117)
          ·
            refine ⟨17583084698911405557956669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46888225863763748154551117 17583084698911405557956669)
            ·
              refine ⟨6593656762091777084233751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17583084698911405557956669 6593656762091777084233751)
              ·
                refine ⟨9890485143137665626350627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6593656762091777084233751 9890485143137665626350627)
                ·
                  refine ⟨14835727714706498439525941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9890485143137665626350627 14835727714706498439525941)
                  ·
                    refine ⟨1390849473253734228705557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14835727714706498439525941 1390849473253734228705557)
                    ·
                      rfl

theorem cell23_8126009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 3, 1, 1, 5].length) (baseStart_8126009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8126009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8126009 prefixEnd_8126009 := by exact prefixLift 8126009
  have htrace : WordTrace (prefixWord ++ tailWord_8126009) baseStart_8126009 baseEnd_8126009 := by
    simpa [prefixWord, tailWord_8126009, baseEnd_8126009] using wordTrace_append hprefix tailTrace_8126009
  have hstable : (prefixWord ++ tailWord_8126009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8126009).length < 2 ^ (prefixWord ++ tailWord_8126009).sum := by decide
  have hdescent : baseEnd_8126009 < baseStart_8126009 := by decide
  rcases family_descends (prefixWord ++ tailWord_8126009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8126052 : List Nat := [2, 3, 1, 1, 2, 4, 3, 7]
def baseStart_8126052 : Nat := 118140960795 + 8126052 * 2 ^ 59
def prefixEnd_8126052 : Nat := 4983230072969 + 3 ^ 40 * 8126052 * 2
def baseEnd_8126052 : Nat := 154539648127012815476999

theorem tailTrace_8126052 : CollatzResearch.WordTrace tailWord_8126052 prefixEnd_8126052 154539648127012815476999 := by
  unfold tailWord_8126052
  simp only [CollatzResearch.WordTrace]
  refine ⟨148190732578354449018390205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197587643437805932024520273 148190732578354449018390205)
  ·
    refine ⟨55571524716882918381896327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148190732578354449018390205 55571524716882918381896327)
    ·
      refine ⟨83357287075324377572844491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55571524716882918381896327 83357287075324377572844491)
      ·
        refine ⟨125035930612986566359266737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83357287075324377572844491 125035930612986566359266737)
        ·
          refine ⟨93776947959739924769450053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125035930612986566359266737 93776947959739924769450053)
          ·
            refine ⟨17583177742451235894271885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93776947959739924769450053 17583177742451235894271885)
            ·
              refine ⟨6593691653419213460351957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17583177742451235894271885 6593691653419213460351957)
              ·
                refine ⟨154539648127012815476999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6593691653419213460351957 154539648127012815476999)
                ·
                  rfl

theorem cell23_8126052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 3, 7].length) (baseStart_8126052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8126052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8126052 prefixEnd_8126052 := by exact prefixLift 8126052
  have htrace : WordTrace (prefixWord ++ tailWord_8126052) baseStart_8126052 baseEnd_8126052 := by
    simpa [prefixWord, tailWord_8126052, baseEnd_8126052] using wordTrace_append hprefix tailTrace_8126052
  have hstable : (prefixWord ++ tailWord_8126052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8126052).length < 2 ^ (prefixWord ++ tailWord_8126052).sum := by decide
  have hdescent : baseEnd_8126052 < baseStart_8126052 := by decide
  rcases family_descends (prefixWord ++ tailWord_8126052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8126066 : List Nat := [3, 2, 1, 2, 3, 1, 4, 1, 1, 2, 3]
def baseStart_8126066 : Nat := 118140960795 + 8126066 * 2 ^ 59
def prefixEnd_8126066 : Nat := 4983230072969 + 3 ^ 40 * 8126066 * 2
def baseEnd_8126066 : Nat := 4172577688158508963103909

theorem tailTrace_8126066 : CollatzResearch.WordTrace tailWord_8126066 prefixEnd_8126066 4172577688158508963103909 := by
  unfold tailWord_8126066
  simp only [CollatzResearch.WordTrace]
  refine ⟨74095493944664544606947513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197587983852438785618526701 74095493944664544606947513)
  ·
    refine ⟨55571620458498408455210635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74095493944664544606947513 55571620458498408455210635)
    ·
      refine ⟨83357430687747612682815953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55571620458498408455210635 83357430687747612682815953)
      ·
        refine ⟨62518073015810709512111965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83357430687747612682815953 62518073015810709512111965)
        ·
          refine ⟨23444277380929016067041987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62518073015810709512111965 23444277380929016067041987)
          ·
            refine ⟨35166416071393524100562981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23444277380929016067041987 35166416071393524100562981)
            ·
              refine ⟨6593703013386285768855559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35166416071393524100562981 6593703013386285768855559)
              ·
                refine ⟨9890554520079428653283339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6593703013386285768855559 9890554520079428653283339)
                ·
                  refine ⟨14835831780119142979925009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9890554520079428653283339 14835831780119142979925009)
                  ·
                    refine ⟨11126873835089357234943757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14835831780119142979925009 11126873835089357234943757)
                    ·
                      refine ⟨4172577688158508963103909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11126873835089357234943757 4172577688158508963103909)
                      ·
                        rfl

theorem cell23_8126066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 4, 1, 1, 2, 3].length) (baseStart_8126066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8126066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8126066 prefixEnd_8126066 := by exact prefixLift 8126066
  have htrace : WordTrace (prefixWord ++ tailWord_8126066) baseStart_8126066 baseEnd_8126066 := by
    simpa [prefixWord, tailWord_8126066, baseEnd_8126066] using wordTrace_append hprefix tailTrace_8126066
  have hstable : (prefixWord ++ tailWord_8126066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8126066).length < 2 ^ (prefixWord ++ tailWord_8126066).sum := by decide
  have hdescent : baseEnd_8126066 < baseStart_8126066 := by decide
  rcases family_descends (prefixWord ++ tailWord_8126066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8126114 : List Nat := [3, 3, 1, 4, 2, 1, 1, 3, 1, 2, 2]
def baseStart_8126114 : Nat := 118140960795 + 8126114 * 2 ^ 59
def prefixEnd_8126114 : Nat := 4983230072969 + 3 ^ 40 * 8126114 * 2
def baseEnd_8126114 : Nat := 4172602335229924775303689

theorem tailTrace_8126114 : CollatzResearch.WordTrace tailWord_8126114 prefixEnd_8126114 4172602335229924775303689 := by
  unfold tailWord_8126114
  simp only [CollatzResearch.WordTrace]
  refine ⟨74095931620621070656384349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197589150988322855083691597 74095931620621070656384349)
  ·
    refine ⟨27785974357732901496144131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74095931620621070656384349 27785974357732901496144131)
    ·
      refine ⟨41678961536599352244216197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27785974357732901496144131 41678961536599352244216197)
      ·
        refine ⟨7814805288112378545790537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41678961536599352244216197 7814805288112378545790537)
        ·
          refine ⟨5861103966084283909342903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7814805288112378545790537 5861103966084283909342903)
          ·
            refine ⟨8791655949126425864014355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5861103966084283909342903 8791655949126425864014355)
            ·
              refine ⟨13187483923689638796021533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8791655949126425864014355 13187483923689638796021533)
              ·
                refine ⟨4945306471383614548508075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13187483923689638796021533 4945306471383614548508075)
                ·
                  refine ⟨7417959707075421822762113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4945306471383614548508075 7417959707075421822762113)
                  ·
                    refine ⟨5563469780306566367071585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7417959707075421822762113 5563469780306566367071585)
                    ·
                      refine ⟨4172602335229924775303689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5563469780306566367071585 4172602335229924775303689)
                      ·
                        rfl

theorem cell23_8126114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 1, 3, 1, 2, 2].length) (baseStart_8126114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8126114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8126114 prefixEnd_8126114 := by exact prefixLift 8126114
  have htrace : WordTrace (prefixWord ++ tailWord_8126114) baseStart_8126114 baseEnd_8126114 := by
    simpa [prefixWord, tailWord_8126114, baseEnd_8126114] using wordTrace_append hprefix tailTrace_8126114
  have hstable : (prefixWord ++ tailWord_8126114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8126114).length < 2 ^ (prefixWord ++ tailWord_8126114).sum := by decide
  have hdescent : baseEnd_8126114 < baseStart_8126114 := by decide
  rcases family_descends (prefixWord ++ tailWord_8126114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8126152 : List Nat := [2, 1, 3, 1, 2, 2, 2, 1, 1, 5, 3]
def baseStart_8126152 : Nat := 118140960795 + 8126152 * 2 ^ 59
def prefixEnd_8126152 : Nat := 4983230072969 + 3 ^ 40 * 8126152 * 2
def baseEnd_8126152 : Nat := 4172621847494795626628513

theorem tailTrace_8126152 : CollatzResearch.WordTrace tailWord_8126152 prefixEnd_8126152 4172621847494795626628513 := by
  unfold tailWord_8126152
  simp only [CollatzResearch.WordTrace]
  refine ⟨148192556228173307557710355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197590074970897743410280473 148192556228173307557710355)
  ·
    refine ⟨222288834342259961336565533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148192556228173307557710355 222288834342259961336565533)
    ·
      refine ⟨83358312878347485501212075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 222288834342259961336565533 83358312878347485501212075)
      ·
        refine ⟨125037469317521228251818113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83358312878347485501212075 125037469317521228251818113)
        ·
          refine ⟨93778101988140921188863585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125037469317521228251818113 93778101988140921188863585)
          ·
            refine ⟨70333576491105690891647689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93778101988140921188863585 70333576491105690891647689)
            ·
              refine ⟨52750182368329268168735767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70333576491105690891647689 52750182368329268168735767)
              ·
                refine ⟨79125273552493902253103651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52750182368329268168735767 79125273552493902253103651)
                ·
                  refine ⟨118687910328740853379655477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79125273552493902253103651 118687910328740853379655477)
                  ·
                    refine ⟨11126991593319455004342701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 118687910328740853379655477 11126991593319455004342701)
                    ·
                      refine ⟨4172621847494795626628513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11126991593319455004342701 4172621847494795626628513)
                      ·
                        rfl

theorem cell23_8126152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 1, 1, 5, 3].length) (baseStart_8126152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8126152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8126152 prefixEnd_8126152 := by exact prefixLift 8126152
  have htrace : WordTrace (prefixWord ++ tailWord_8126152) baseStart_8126152 baseEnd_8126152 := by
    simpa [prefixWord, tailWord_8126152, baseEnd_8126152] using wordTrace_append hprefix tailTrace_8126152
  have hstable : (prefixWord ++ tailWord_8126152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8126152).length < 2 ^ (prefixWord ++ tailWord_8126152).sum := by decide
  have hdescent : baseEnd_8126152 < baseStart_8126152 := by decide
  rcases family_descends (prefixWord ++ tailWord_8126152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8126155 : List Nat := [1, 1, 1, 1, 3, 2, 1, 3, 3, 7]
def baseStart_8126155 : Nat := 118140960795 + 8126155 * 2 ^ 59
def prefixEnd_8126155 : Nat := 4983230072969 + 3 ^ 40 * 8126155 * 2
def baseEnd_8126155 : Nat := 1390874462645586371630333

theorem tailTrace_8126155 : CollatzResearch.WordTrace tailWord_8126155 prefixEnd_8126155 1390874462645586371630333 := by
  unfold tailWord_8126155
  simp only [CollatzResearch.WordTrace]
  refine ⟨296385221875335746627779919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197590147916890497751853279 296385221875335746627779919)
  ·
    refine ⟨444577832813003619941669879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296385221875335746627779919 444577832813003619941669879)
    ·
      refine ⟨666866749219505429912504819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 444577832813003619941669879 666866749219505429912504819)
      ·
        refine ⟨1000300123829258144868757229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 666866749219505429912504819 1000300123829258144868757229)
        ·
          refine ⟨375112546435971804325783961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1000300123829258144868757229 375112546435971804325783961)
          ·
            refine ⟨281334409826978853244337971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 375112546435971804325783961 281334409826978853244337971)
            ·
              refine ⟨422001614740468279866506957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 281334409826978853244337971 422001614740468279866506957)
              ·
                refine ⟨158250605527675604949940109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 422001614740468279866506957 158250605527675604949940109)
                ·
                  refine ⟨59343977072878351856227541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 158250605527675604949940109 59343977072878351856227541)
                  ·
                    refine ⟨1390874462645586371630333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59343977072878351856227541 1390874462645586371630333)
                    ·
                      rfl

theorem cell23_8126155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 3, 3, 7].length) (baseStart_8126155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8126155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8126155 prefixEnd_8126155 := by exact prefixLift 8126155
  have htrace : WordTrace (prefixWord ++ tailWord_8126155) baseStart_8126155 baseEnd_8126155 := by
    simpa [prefixWord, tailWord_8126155, baseEnd_8126155] using wordTrace_append hprefix tailTrace_8126155
  have hstable : (prefixWord ++ tailWord_8126155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8126155).length < 2 ^ (prefixWord ++ tailWord_8126155).sum := by decide
  have hdescent : baseEnd_8126155 < baseStart_8126155 := by decide
  rcases family_descends (prefixWord ++ tailWord_8126155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8126189 : List Nat := [1, 5, 1, 2, 1, 2, 2, 2, 2, 5]
def baseStart_8126189 : Nat := 118140960795 + 8126189 * 2 ^ 59
def prefixEnd_8126189 : Nat := 4983230072969 + 3 ^ 40 * 8126189 * 2
def baseEnd_8126189 : Nat := 1390880282093003993955281

theorem tailTrace_8126189 : CollatzResearch.WordTrace tailWord_8126189 prefixEnd_8126189 1390880282093003993955281 := by
  unfold tailWord_8126189
  simp only [CollatzResearch.WordTrace]
  refine ⟨296386461957212570434517621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197590974638141713623011747 296386461957212570434517621)
  ·
    refine ⟨27786230808488678478236027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 296386461957212570434517621 27786230808488678478236027)
    ·
      refine ⟨41679346212733017717354041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27786230808488678478236027 41679346212733017717354041)
      ·
        refine ⟨31259509659549763288015531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41679346212733017717354041 31259509659549763288015531)
        ·
          refine ⟨46889264489324644932023297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31259509659549763288015531 46889264489324644932023297)
          ·
            refine ⟨35166948366993483699017473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46889264489324644932023297 35166948366993483699017473)
            ·
              refine ⟨26375211275245112774263105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35166948366993483699017473 26375211275245112774263105)
              ·
                refine ⟨19781408456433834580697329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26375211275245112774263105 19781408456433834580697329)
                ·
                  refine ⟨14836056342325375935522997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19781408456433834580697329 14836056342325375935522997)
                  ·
                    refine ⟨1390880282093003993955281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14836056342325375935522997 1390880282093003993955281)
                    ·
                      rfl

theorem cell23_8126189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 2, 2, 5].length) (baseStart_8126189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8126189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8126189 prefixEnd_8126189 := by exact prefixLift 8126189
  have htrace : WordTrace (prefixWord ++ tailWord_8126189) baseStart_8126189 baseEnd_8126189 := by
    simpa [prefixWord, tailWord_8126189, baseEnd_8126189] using wordTrace_append hprefix tailTrace_8126189
  have hstable : (prefixWord ++ tailWord_8126189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8126189).length < 2 ^ (prefixWord ++ tailWord_8126189).sum := by decide
  have hdescent : baseEnd_8126189 < baseStart_8126189 := by decide
  rcases family_descends (prefixWord ++ tailWord_8126189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8126192 : List Nat := [2, 1, 1, 1, 3, 1, 2, 3, 4, 1, 4]
def baseStart_8126192 : Nat := 118140960795 + 8126192 * 2 ^ 59
def prefixEnd_8126192 : Nat := 4983230072969 + 3 ^ 40 * 8126192 * 2
def baseEnd_8126192 : Nat := 4172642386720975470128329

theorem tailTrace_8126192 : CollatzResearch.WordTrace tailWord_8126192 prefixEnd_8126192 4172642386720975470128329 := by
  unfold tailWord_8126192
  simp only [CollatzResearch.WordTrace]
  refine ⟨148193285688100850973438415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197591047584134467964584553 148193285688100850973438415)
  ·
    refine ⟨222289928532151276460157623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148193285688100850973438415 222289928532151276460157623)
    ·
      refine ⟨333434892798226914690236435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222289928532151276460157623 333434892798226914690236435)
      ·
        refine ⟨500152339197340372035354653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 333434892798226914690236435 500152339197340372035354653)
        ·
          refine ⟨187557127199002639513257995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 500152339197340372035354653 187557127199002639513257995)
          ·
            refine ⟨281335690798503959269886993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187557127199002639513257995 281335690798503959269886993)
            ·
              refine ⟨211001768098877969452415245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 281335690798503959269886993 211001768098877969452415245)
              ·
                refine ⟨79125663037079238544655717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 211001768098877969452415245 79125663037079238544655717)
                ·
                  refine ⟨14836061819452357227122947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79125663037079238544655717 14836061819452357227122947)
                  ·
                    refine ⟨22254092729178535840684421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14836061819452357227122947 22254092729178535840684421)
                    ·
                      refine ⟨4172642386720975470128329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22254092729178535840684421 4172642386720975470128329)
                      ·
                        rfl

theorem cell23_8126192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 3, 4, 1, 4].length) (baseStart_8126192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8126192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8126192 prefixEnd_8126192 := by exact prefixLift 8126192
  have htrace : WordTrace (prefixWord ++ tailWord_8126192) baseStart_8126192 baseEnd_8126192 := by
    simpa [prefixWord, tailWord_8126192, baseEnd_8126192] using wordTrace_append hprefix tailTrace_8126192
  have hstable : (prefixWord ++ tailWord_8126192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8126192).length < 2 ^ (prefixWord ++ tailWord_8126192).sum := by decide
  have hdescent : baseEnd_8126192 < baseStart_8126192 := by decide
  rcases family_descends (prefixWord ++ tailWord_8126192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8126209 : List Nat := [1, 2, 4, 1, 1, 1, 3, 1, 1, 6, 2]
def baseStart_8126209 : Nat := 118140960795 + 8126209 * 2 ^ 59
def prefixEnd_8126209 : Nat := 4983230072969 + 3 ^ 40 * 8126209 * 2
def baseEnd_8126209 : Nat := 4172651115892101903615751

theorem tailTrace_8126209 : CollatzResearch.WordTrace tailWord_8126209 prefixEnd_8126209 4172651115892101903615751 := by
  unfold tailWord_8126209
  simp only [CollatzResearch.WordTrace]
  refine ⟨296387191417140113850245681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197591460944760075900163787 296387191417140113850245681)
  ·
    refine ⟨222290393562855085387684261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296387191417140113850245681 222290393562855085387684261)
    ·
      refine ⟨41679448793035328510190799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 222290393562855085387684261 41679448793035328510190799)
      ·
        refine ⟨62519173189552992765286199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41679448793035328510190799 62519173189552992765286199)
        ·
          refine ⟨93778759784329489147929299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62519173189552992765286199 93778759784329489147929299)
          ·
            refine ⟨140668139676494233721893949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93778759784329489147929299 140668139676494233721893949)
            ·
              refine ⟨52750552378685337645710231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 140668139676494233721893949 52750552378685337645710231)
              ·
                refine ⟨79125828568028006468565347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52750552378685337645710231 79125828568028006468565347)
                ·
                  refine ⟨118688742852042009702848021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79125828568028006468565347 118688742852042009702848021)
                  ·
                    refine ⟨5563534821189469204821001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 118688742852042009702848021 5563534821189469204821001)
                    ·
                      refine ⟨4172651115892101903615751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5563534821189469204821001 4172651115892101903615751)
                      ·
                        rfl

theorem cell23_8126209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 1, 1, 6, 2].length) (baseStart_8126209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8126209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8126209 prefixEnd_8126209 := by exact prefixLift 8126209
  have htrace : WordTrace (prefixWord ++ tailWord_8126209) baseStart_8126209 baseEnd_8126209 := by
    simpa [prefixWord, tailWord_8126209, baseEnd_8126209] using wordTrace_append hprefix tailTrace_8126209
  have hstable : (prefixWord ++ tailWord_8126209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8126209).length < 2 ^ (prefixWord ++ tailWord_8126209).sum := by decide
  have hdescent : baseEnd_8126209 < baseStart_8126209 := by decide
  rcases family_descends (prefixWord ++ tailWord_8126209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8126226 : List Nat := [3, 2, 4, 1, 1, 2, 1, 1, 1, 3, 4]
def baseStart_8126226 : Nat := 118140960795 + 8126226 * 2 ^ 59
def prefixEnd_8126226 : Nat := 4983230072969 + 3 ^ 40 * 8126226 * 2
def baseEnd_8126226 : Nat := 4172659845063228337103173

theorem tailTrace_8126226 : CollatzResearch.WordTrace tailWord_8126226 prefixEnd_8126226 4172659845063228337103173 := by
  unfold tailWord_8126226
  simp only [CollatzResearch.WordTrace]
  refine ⟨74096952864519631438403633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197591874305385683835743021 74096952864519631438403633)
  ·
    refine ⟨55572714648389723578802725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74096952864519631438403633 55572714648389723578802725)
    ·
      refine ⟨10419883996573073171025511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55572714648389723578802725 10419883996573073171025511)
      ·
        refine ⟨15629825994859609756538267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10419883996573073171025511 15629825994859609756538267)
        ·
          refine ⟨23444738992289414634807401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15629825994859609756538267 23444738992289414634807401)
          ·
            refine ⟨17583554244217060976105551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23444738992289414634807401 17583554244217060976105551)
            ·
              refine ⟨26375331366325591464158327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17583554244217060976105551 26375331366325591464158327)
              ·
                refine ⟨39562997049488387196237491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26375331366325591464158327 39562997049488387196237491)
                ·
                  refine ⟨59344495574232580794356237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39562997049488387196237491 59344495574232580794356237)
                  ·
                    refine ⟨22254185840337217797883589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59344495574232580794356237 22254185840337217797883589)
                    ·
                      refine ⟨4172659845063228337103173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22254185840337217797883589 4172659845063228337103173)
                      ·
                        rfl

theorem cell23_8126226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_8126226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8126226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8126226 prefixEnd_8126226 := by exact prefixLift 8126226
  have htrace : WordTrace (prefixWord ++ tailWord_8126226) baseStart_8126226 baseEnd_8126226 := by
    simpa [prefixWord, tailWord_8126226, baseEnd_8126226] using wordTrace_append hprefix tailTrace_8126226
  have hstable : (prefixWord ++ tailWord_8126226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8126226).length < 2 ^ (prefixWord ++ tailWord_8126226).sum := by decide
  have hdescent : baseEnd_8126226 < baseStart_8126226 := by decide
  rcases family_descends (prefixWord ++ tailWord_8126226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8126229 : List Nat := [1, 3, 2, 1, 2, 4, 1, 1, 1, 4, 3]
def baseStart_8126229 : Nat := 118140960795 + 8126229 * 2 ^ 59
def prefixEnd_8126229 : Nat := 4983230072969 + 3 ^ 40 * 8126229 * 2
def baseEnd_8126229 : Nat := 4172661385505191825365659

theorem tailTrace_8126229 : CollatzResearch.WordTrace tailWord_8126229 prefixEnd_8126229 4172661385505191825365659 := by
  unfold tailWord_8126229
  simp only [CollatzResearch.WordTrace]
  refine ⟨296387920877067657265973741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197591947251378438177315827 296387920877067657265973741)
  ·
    refine ⟨111145470328900371474740153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 296387920877067657265973741 111145470328900371474740153)
    ·
      refine ⟨83359102746675278606055115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111145470328900371474740153 83359102746675278606055115)
      ·
        refine ⟨125038654120012917909082673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83359102746675278606055115 125038654120012917909082673)
        ·
          refine ⟨93778990590009688431812005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125038654120012917909082673 93778990590009688431812005)
          ·
            refine ⟨17583560735626816580964751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93778990590009688431812005 17583560735626816580964751)
            ·
              refine ⟨26375341103440224871447127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17583560735626816580964751 26375341103440224871447127)
              ·
                refine ⟨39563011655160337307170691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26375341103440224871447127 39563011655160337307170691)
                ·
                  refine ⟨59344517482740505960756037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39563011655160337307170691 59344517482740505960756037)
                  ·
                    refine ⟨11127097028013844867641757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59344517482740505960756037 11127097028013844867641757)
                    ·
                      refine ⟨4172661385505191825365659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11127097028013844867641757 4172661385505191825365659)
                      ·
                        rfl

theorem cell23_8126229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 1, 1, 4, 3].length) (baseStart_8126229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8126229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8126229 prefixEnd_8126229 := by exact prefixLift 8126229
  have htrace : WordTrace (prefixWord ++ tailWord_8126229) baseStart_8126229 baseEnd_8126229 := by
    simpa [prefixWord, tailWord_8126229, baseEnd_8126229] using wordTrace_append hprefix tailTrace_8126229
  have hstable : (prefixWord ++ tailWord_8126229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8126229).length < 2 ^ (prefixWord ++ tailWord_8126229).sum := by decide
  have hdescent : baseEnd_8126229 < baseStart_8126229 := by decide
  rcases family_descends (prefixWord ++ tailWord_8126229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8126252 : List Nat := [2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 6]
def baseStart_8126252 : Nat := 118140960795 + 8126252 * 2 ^ 59
def prefixEnd_8126252 : Nat := 4983230072969 + 3 ^ 40 * 8126252 * 2
def baseEnd_8126252 : Nat := 4172673195560245235378053

theorem tailTrace_8126252 : CollatzResearch.WordTrace tailWord_8126252 prefixEnd_8126252 4172673195560245235378053 := by
  unfold tailWord_8126252
  simp only [CollatzResearch.WordTrace]
  refine ⟨148194379877992166097030505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197592506503989554796040673 148194379877992166097030505)
  ·
    refine ⟨111145784908494124572772879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148194379877992166097030505 111145784908494124572772879)
    ·
      refine ⟨166718677362741186859159319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111145784908494124572772879 166718677362741186859159319)
      ·
        refine ⟨250078016044111780288738979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166718677362741186859159319 250078016044111780288738979)
        ·
          refine ⟨375117024066167670433108469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250078016044111780288738979 375117024066167670433108469)
          ·
            refine ⟨35167221006203219103103919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 375117024066167670433108469 35167221006203219103103919)
            ·
              refine ⟨52750831509304828654655879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35167221006203219103103919 52750831509304828654655879)
              ·
                refine ⟨79126247263957242981983819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52750831509304828654655879 79126247263957242981983819)
                ·
                  refine ⟨118689370895935864472975729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79126247263957242981983819 118689370895935864472975729)
                  ·
                    refine ⟨89017028171951898354731797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 118689370895935864472975729 89017028171951898354731797)
                    ·
                      refine ⟨4172673195560245235378053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 89017028171951898354731797 4172673195560245235378053)
                      ·
                        rfl

theorem cell23_8126252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 6].length) (baseStart_8126252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8126252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8126252 prefixEnd_8126252 := by exact prefixLift 8126252
  have htrace : WordTrace (prefixWord ++ tailWord_8126252) baseStart_8126252 baseEnd_8126252 := by
    simpa [prefixWord, tailWord_8126252, baseEnd_8126252] using wordTrace_append hprefix tailTrace_8126252
  have hstable : (prefixWord ++ tailWord_8126252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8126252).length < 2 ^ (prefixWord ++ tailWord_8126252).sum := by decide
  have hdescent : baseEnd_8126252 < baseStart_8126252 := by decide
  rcases family_descends (prefixWord ++ tailWord_8126252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8126266 : List Nat := [3, 1, 1, 1, 5, 2, 3, 1, 6]
def baseStart_8126266 : Nat := 118140960795 + 8126266 * 2 ^ 59
def prefixEnd_8126266 : Nat := 4983230072969 + 3 ^ 40 * 8126266 * 2
def baseEnd_8126266 : Nat := 463631153809934242289221

theorem tailTrace_8126266 : CollatzResearch.WordTrace tailWord_8126266 prefixEnd_8126266 463631153809934242289221 := by
  unfold tailWord_8126266
  simp only [CollatzResearch.WordTrace]
  refine ⟨74097317594483403146267663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197592846918622408390047101 74097317594483403146267663)
  ·
    refine ⟨111145976391725104719401495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74097317594483403146267663 111145976391725104719401495)
    ·
      refine ⟨166718964587587657079102243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111145976391725104719401495 166718964587587657079102243)
      ·
        refine ⟨250078446881381485618653365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166718964587587657079102243 250078446881381485618653365)
        ·
          refine ⟨23444854395129514276748753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 250078446881381485618653365 23444854395129514276748753)
          ·
            refine ⟨17583640796347135707561565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23444854395129514276748753 17583640796347135707561565)
            ·
              refine ⟨6593865298630175890335587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17583640796347135707561565 6593865298630175890335587)
              ·
                refine ⟨9890797947945263835503381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6593865298630175890335587 9890797947945263835503381)
                ·
                  refine ⟨463631153809934242289221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9890797947945263835503381 463631153809934242289221)
                  ·
                    rfl

theorem cell23_8126266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 3, 1, 6].length) (baseStart_8126266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8126266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8126266 prefixEnd_8126266 := by exact prefixLift 8126266
  have htrace : WordTrace (prefixWord ++ tailWord_8126266) baseStart_8126266 baseEnd_8126266 := by
    simpa [prefixWord, tailWord_8126266, baseEnd_8126266] using wordTrace_append hprefix tailTrace_8126266
  have hstable : (prefixWord ++ tailWord_8126266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8126266).length < 2 ^ (prefixWord ++ tailWord_8126266).sum := by decide
  have hdescent : baseEnd_8126266 < baseStart_8126266 := by decide
  rcases family_descends (prefixWord ++ tailWord_8126266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8126279 : List Nat := [1, 1, 4, 1, 2, 1, 3, 4, 1, 5]
def baseStart_8126279 : Nat := 118140960795 + 8126279 * 2 ^ 59
def prefixEnd_8126279 : Nat := 4983230072969 + 3 ^ 40 * 8126279 * 2
def baseEnd_8126279 : Nat := 1390895686512638876580143

theorem tailTrace_8126279 : CollatzResearch.WordTrace tailWord_8126279 prefixEnd_8126279 1390895686512638876580143 := by
  unfold tailWord_8126279
  simp only [CollatzResearch.WordTrace]
  refine ⟨296389744526886515805293891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197593163017924343870195927 296389744526886515805293891)
  ·
    refine ⟨444584616790329773707940837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296389744526886515805293891 444584616790329773707940837)
    ·
      refine ⟨83359615648186832570238907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 444584616790329773707940837 83359615648186832570238907)
      ·
        refine ⟨125039423472280248855358361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83359615648186832570238907 125039423472280248855358361)
        ·
          refine ⟨93779567604210186641518771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125039423472280248855358361 93779567604210186641518771)
          ·
            refine ⟨140669351406315279962278157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93779567604210186641518771 140669351406315279962278157)
            ·
              refine ⟨52751006777368229985854309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 140669351406315279962278157 52751006777368229985854309)
              ·
                refine ⟨9890813770756543122347683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52751006777368229985854309 9890813770756543122347683)
                ·
                  refine ⟨14836220656134814683521525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9890813770756543122347683 14836220656134814683521525)
                  ·
                    refine ⟨1390895686512638876580143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14836220656134814683521525 1390895686512638876580143)
                    ·
                      rfl

theorem cell23_8126279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 4, 1, 5].length) (baseStart_8126279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8126279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8126279 prefixEnd_8126279 := by exact prefixLift 8126279
  have htrace : WordTrace (prefixWord ++ tailWord_8126279) baseStart_8126279 baseEnd_8126279 := by
    simpa [prefixWord, tailWord_8126279, baseEnd_8126279] using wordTrace_append hprefix tailTrace_8126279
  have hstable : (prefixWord ++ tailWord_8126279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8126279).length < 2 ^ (prefixWord ++ tailWord_8126279).sum := by decide
  have hdescent : baseEnd_8126279 < baseStart_8126279 := by decide
  rcases family_descends (prefixWord ++ tailWord_8126279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8126329 : List Nat := [1, 2, 1, 3, 2, 2, 2, 3, 1, 2, 4]
def baseStart_8126329 : Nat := 118140960795 + 8126329 * 2 ^ 59
def prefixEnd_8126329 : Nat := 4983230072969 + 3 ^ 40 * 8126329 * 2
def baseEnd_8126329 : Nat := 4172712733570641434115199

theorem tailTrace_8126329 : CollatzResearch.WordTrace tailWord_8126329 prefixEnd_8126329 4172712733570641434115199 := by
  unfold tailWord_8126329
  simp only [CollatzResearch.WordTrace]
  refine ⟨296391568176705374344614041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197594378784470249563076027 296391568176705374344614041)
  ·
    refine ⟨222293676132529030758460531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296391568176705374344614041 222293676132529030758460531)
    ·
      refine ⟨333440514198793546137690797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222293676132529030758460531 333440514198793546137690797)
      ·
        refine ⟨125040192824547579801634049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 333440514198793546137690797 125040192824547579801634049)
        ·
          refine ⟨93780144618410684851225537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125040192824547579801634049 93780144618410684851225537)
          ·
            refine ⟨70335108463808013638419153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93780144618410684851225537 70335108463808013638419153)
            ·
              refine ⟨52751331347856010228814365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70335108463808013638419153 52751331347856010228814365)
              ·
                refine ⟨19781749255446003835805387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52751331347856010228814365 19781749255446003835805387)
                ·
                  refine ⟨29672623883169005753708081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19781749255446003835805387 29672623883169005753708081)
                  ·
                    refine ⟨22254467912376754315281061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29672623883169005753708081 22254467912376754315281061)
                    ·
                      refine ⟨4172712733570641434115199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22254467912376754315281061 4172712733570641434115199)
                      ·
                        rfl

theorem cell23_8126329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 3, 1, 2, 4].length) (baseStart_8126329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8126329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8126329 prefixEnd_8126329 := by exact prefixLift 8126329
  have htrace : WordTrace (prefixWord ++ tailWord_8126329) baseStart_8126329 baseEnd_8126329 := by
    simpa [prefixWord, tailWord_8126329, baseEnd_8126329] using wordTrace_append hprefix tailTrace_8126329
  have hstable : (prefixWord ++ tailWord_8126329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8126329).length < 2 ^ (prefixWord ++ tailWord_8126329).sum := by decide
  have hdescent : baseEnd_8126329 < baseStart_8126329 := by decide
  rcases family_descends (prefixWord ++ tailWord_8126329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8126352 : List Nat := [2, 1, 1, 1, 1, 1, 2, 4, 1, 9]
def baseStart_8126352 : Nat := 118140960795 + 8126352 * 2 ^ 59
def prefixEnd_8126352 : Nat := 4983230072969 + 3 ^ 40 * 8126352 * 2
def baseEnd_8126352 : Nat := 1390908181208564948042531

theorem tailTrace_8126352 : CollatzResearch.WordTrace tailWord_8126352 prefixEnd_8126352 1390908181208564948042531 := by
  unfold tailWord_8126352
  simp only [CollatzResearch.WordTrace]
  refine ⟨148196203527811024636350655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197594938037081366181800873 148196203527811024636350655)
  ·
    refine ⟨222294305291716536954525983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148196203527811024636350655 222294305291716536954525983)
    ·
      refine ⟨333441457937574805431788975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222294305291716536954525983 333441457937574805431788975)
      ·
        refine ⟨500162186906362208147683463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 333441457937574805431788975 500162186906362208147683463)
        ·
          refine ⟨750243280359543312221525195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 500162186906362208147683463 750243280359543312221525195)
          ·
            refine ⟨1125364920539314968332287793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 750243280359543312221525195 1125364920539314968332287793)
            ·
              refine ⟨844023690404486226249215845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1125364920539314968332287793 844023690404486226249215845)
              ·
                refine ⟨158254441950841167421727971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 844023690404486226249215845 158254441950841167421727971)
                ·
                  refine ⟨237381662926261751132591957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 158254441950841167421727971 237381662926261751132591957)
                  ·
                    refine ⟨1390908181208564948042531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 237381662926261751132591957 1390908181208564948042531)
                    ·
                      rfl

theorem cell23_8126352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 4, 1, 9].length) (baseStart_8126352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8126352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8126352 prefixEnd_8126352 := by exact prefixLift 8126352
  have htrace : WordTrace (prefixWord ++ tailWord_8126352) baseStart_8126352 baseEnd_8126352 := by
    simpa [prefixWord, tailWord_8126352, baseEnd_8126352] using wordTrace_append hprefix tailTrace_8126352
  have hstable : (prefixWord ++ tailWord_8126352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8126352).length < 2 ^ (prefixWord ++ tailWord_8126352).sum := by decide
  have hdescent : baseEnd_8126352 < baseStart_8126352 := by decide
  rcases family_descends (prefixWord ++ tailWord_8126352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8126360 : List Nat := [2, 1, 2, 6, 1, 1, 2, 2, 2, 4]
def baseStart_8126360 : Nat := 118140960795 + 8126360 * 2 ^ 59
def prefixEnd_8126360 : Nat := 4983230072969 + 3 ^ 40 * 8126360 * 2
def baseEnd_8126360 : Nat := 1390909550490310270942519

theorem tailTrace_8126360 : CollatzResearch.WordTrace tailWord_8126360 prefixEnd_8126360 1390909550490310270942519 := by
  unfold tailWord_8126360
  simp only [CollatzResearch.WordTrace]
  refine ⟨148196349419796533319496267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197595132559728711092661689 148196349419796533319496267)
  ·
    refine ⟨222294524129694799979244401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148196349419796533319496267 222294524129694799979244401)
    ·
      refine ⟨166720893097271099984433301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222294524129694799979244401 166720893097271099984433301)
      ·
        refine ⟨7815041863934582811770311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 166720893097271099984433301 7815041863934582811770311)
        ·
          refine ⟨11722562795901874217655467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7815041863934582811770311 11722562795901874217655467)
          ·
            refine ⟨17583844193852811326483201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11722562795901874217655467 17583844193852811326483201)
            ·
              refine ⟨13187883145389608494862401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17583844193852811326483201 13187883145389608494862401)
              ·
                refine ⟨9890912359042206371146801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13187883145389608494862401 9890912359042206371146801)
                ·
                  refine ⟨7418184269281654778360101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9890912359042206371146801 7418184269281654778360101)
                  ·
                    refine ⟨1390909550490310270942519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7418184269281654778360101 1390909550490310270942519)
                    ·
                      rfl

theorem cell23_8126360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 2, 2, 2, 4].length) (baseStart_8126360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8126360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8126360 prefixEnd_8126360 := by exact prefixLift 8126360
  have htrace : WordTrace (prefixWord ++ tailWord_8126360) baseStart_8126360 baseEnd_8126360 := by
    simpa [prefixWord, tailWord_8126360, baseEnd_8126360] using wordTrace_append hprefix tailTrace_8126360
  have hstable : (prefixWord ++ tailWord_8126360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8126360).length < 2 ^ (prefixWord ++ tailWord_8126360).sum := by decide
  have hdescent : baseEnd_8126360 < baseStart_8126360 := by decide
  rcases family_descends (prefixWord ++ tailWord_8126360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8126367 : List Nat := [1, 1, 2, 5, 3, 1, 1, 4, 1, 2, 2]
def baseStart_8126367 : Nat := 118140960795 + 8126367 * 2 ^ 59
def prefixEnd_8126367 : Nat := 4983230072969 + 3 ^ 40 * 8126367 * 2
def baseEnd_8126367 : Nat := 4172732245835512285440025

theorem tailTrace_8126367 : CollatzResearch.WordTrace tailWord_8126367 prefixEnd_8126367 4172732245835512285440025 := by
  unfold tailWord_8126367
  simp only [CollatzResearch.WordTrace]
  refine ⟨296392954150567706834497355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197595302767045137889664903 296392954150567706834497355)
  ·
    refine ⟨444589431225851560251746033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296392954150567706834497355 444589431225851560251746033)
    ·
      refine ⟨333442073419388670188809525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 444589431225851560251746033 333442073419388670188809525)
      ·
        refine ⟨31260194383067687830200893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 333442073419388670188809525 31260194383067687830200893)
        ·
          refine ⟨11722572893650382936325335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31260194383067687830200893 11722572893650382936325335)
          ·
            refine ⟨17583859340475574404488003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11722572893650382936325335 17583859340475574404488003)
            ·
              refine ⟨26375789010713361606732005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17583859340475574404488003 26375789010713361606732005)
              ·
                refine ⟨4945460439508755301262251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26375789010713361606732005 4945460439508755301262251)
                ·
                  refine ⟨7418190659263132951893377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4945460439508755301262251 7418190659263132951893377)
                  ·
                    refine ⟨5563642994447349713920033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7418190659263132951893377 5563642994447349713920033)
                    ·
                      refine ⟨4172732245835512285440025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5563642994447349713920033 4172732245835512285440025)
                      ·
                        rfl

theorem cell23_8126367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 4, 1, 2, 2].length) (baseStart_8126367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8126367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8126367 prefixEnd_8126367 := by exact prefixLift 8126367
  have htrace : WordTrace (prefixWord ++ tailWord_8126367) baseStart_8126367 baseEnd_8126367 := by
    simpa [prefixWord, tailWord_8126367, baseEnd_8126367] using wordTrace_append hprefix tailTrace_8126367
  have hstable : (prefixWord ++ tailWord_8126367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8126367).length < 2 ^ (prefixWord ++ tailWord_8126367).sum := by decide
  have hdescent : baseEnd_8126367 < baseStart_8126367 := by decide
  rcases family_descends (prefixWord ++ tailWord_8126367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8126393 : List Nat := [1, 2, 1, 4, 2, 1, 2, 4, 1, 3, 2]
def baseStart_8126393 : Nat := 118140960795 + 8126393 * 2 ^ 59
def prefixEnd_8126393 : Nat := 4983230072969 + 3 ^ 40 * 8126393 * 2
def baseEnd_8126393 : Nat := 4172745596332529183714905

theorem tailTrace_8126393 : CollatzResearch.WordTrace tailWord_8126393 prefixEnd_8126393 4172745596332529183714905 := by
  unfold tailWord_8126393
  simp only [CollatzResearch.WordTrace]
  refine ⟨296393902448473513274943833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197595934965649008849962555 296393902448473513274943833)
  ·
    refine ⟨222295426836355134956207875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296393902448473513274943833 222295426836355134956207875)
    ·
      refine ⟨333443140254532702434311813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222295426836355134956207875 333443140254532702434311813)
      ·
        refine ⟨62520588797724881706433465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 333443140254532702434311813 62520588797724881706433465)
        ·
          refine ⟨46890441598293661279825099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62520588797724881706433465 46890441598293661279825099)
          ·
            refine ⟨70335662397440491919737649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46890441598293661279825099 70335662397440491919737649)
            ·
              refine ⟨52751746798080368939803237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70335662397440491919737649 52751746798080368939803237)
              ·
                refine ⟨9890952524640069176213107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52751746798080368939803237 9890952524640069176213107)
                ·
                  refine ⟨14836428786960103764319661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9890952524640069176213107 14836428786960103764319661)
                  ·
                    refine ⟨5563660795110038911619873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14836428786960103764319661 5563660795110038911619873)
                    ·
                      refine ⟨4172745596332529183714905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5563660795110038911619873 4172745596332529183714905)
                      ·
                        rfl

theorem cell23_8126393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 4, 1, 3, 2].length) (baseStart_8126393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8126393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8126393 prefixEnd_8126393 := by exact prefixLift 8126393
  have htrace : WordTrace (prefixWord ++ tailWord_8126393) baseStart_8126393 baseEnd_8126393 := by
    simpa [prefixWord, tailWord_8126393, baseEnd_8126393] using wordTrace_append hprefix tailTrace_8126393
  have hstable : (prefixWord ++ tailWord_8126393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8126393).length < 2 ^ (prefixWord ++ tailWord_8126393).sum := by decide
  have hdescent : baseEnd_8126393 < baseStart_8126393 := by decide
  rcases family_descends (prefixWord ++ tailWord_8126393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8126409 : List Nat := [1, 2, 1, 1, 2, 1, 2, 2, 4, 4, 3]
def baseStart_8126409 : Nat := 118140960795 + 8126409 * 2 ^ 59
def prefixEnd_8126409 : Nat := 4983230072969 + 3 ^ 40 * 8126409 * 2
def baseEnd_8126409 : Nat := 4172753812023001121114831

theorem tailTrace_8126409 : CollatzResearch.WordTrace tailWord_8126409 prefixEnd_8126409 4172753812023001121114831 := by
  unfold tailWord_8126409
  simp only [CollatzResearch.WordTrace]
  refine ⟨296394486016415548007526281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197596324010943698671684187 296394486016415548007526281)
  ·
    refine ⟨222295864512311661005644711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296394486016415548007526281 222295864512311661005644711)
    ·
      refine ⟨333443796768467491508467067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222295864512311661005644711 333443796768467491508467067)
      ·
        refine ⟨500165695152701237262700601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 333443796768467491508467067 500165695152701237262700601)
        ·
          refine ⟨375124271364525927947025451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 500165695152701237262700601 375124271364525927947025451)
          ·
            refine ⟨562686407046788891920538177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 375124271364525927947025451 562686407046788891920538177)
            ·
              refine ⟨422014805285091668940403633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 562686407046788891920538177 422014805285091668940403633)
              ·
                refine ⟨316511103963818751705302725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 422014805285091668940403633 316511103963818751705302725)
                ·
                  refine ⟨59345831993216015944744261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 316511103963818751705302725 59345831993216015944744261)
                  ·
                    refine ⟨11127343498728002989639549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59345831993216015944744261 11127343498728002989639549)
                    ·
                      refine ⟨4172753812023001121114831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11127343498728002989639549 4172753812023001121114831)
                      ·
                        rfl

theorem cell23_8126409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 4, 4, 3].length) (baseStart_8126409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8126409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8126409 prefixEnd_8126409 := by exact prefixLift 8126409
  have htrace : WordTrace (prefixWord ++ tailWord_8126409) baseStart_8126409 baseEnd_8126409 := by
    simpa [prefixWord, tailWord_8126409, baseEnd_8126409] using wordTrace_append hprefix tailTrace_8126409
  have hstable : (prefixWord ++ tailWord_8126409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8126409).length < 2 ^ (prefixWord ++ tailWord_8126409).sum := by decide
  have hdescent : baseEnd_8126409 < baseStart_8126409 := by decide
  rcases family_descends (prefixWord ++ tailWord_8126409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8126410 : List Nat := [3, 1, 2, 1, 2, 1, 6, 1, 1, 3, 2]
def baseStart_8126410 : Nat := 118140960795 + 8126410 * 2 ^ 59
def prefixEnd_8126410 : Nat := 4983230072969 + 3 ^ 40 * 8126410 * 2
def baseEnd_8126410 : Nat := 4172754325503655617202327

theorem tailTrace_8126410 : CollatzResearch.WordTrace tailWord_8126410 prefixEnd_8126410 4172754325503655617202327 := by
  unfold tailWord_8126410
  simp only [CollatzResearch.WordTrace]
  refine ⟨74098630622352981294578171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197596348326274616785541789 74098630622352981294578171)
  ·
    refine ⟨111147945933529471941867257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74098630622352981294578171 111147945933529471941867257)
    ·
      refine ⟨83360959450147103956400443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111147945933529471941867257 83360959450147103956400443)
      ·
        refine ⟨125041439175220655934600665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83360959450147103956400443 125041439175220655934600665)
        ·
          refine ⟨93781079381415491950950499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125041439175220655934600665 93781079381415491950950499)
          ·
            refine ⟨140671619072123237926425749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93781079381415491950950499 140671619072123237926425749)
            ·
              refine ⟨6593982144005776777801207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 140671619072123237926425749 6593982144005776777801207)
              ·
                refine ⟨9890973216008665166701811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6593982144005776777801207 9890973216008665166701811)
                ·
                  refine ⟨14836459824012997750052717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9890973216008665166701811 14836459824012997750052717)
                  ·
                    refine ⟨5563672434004874156269769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14836459824012997750052717 5563672434004874156269769)
                    ·
                      refine ⟨4172754325503655617202327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5563672434004874156269769 4172754325503655617202327)
                      ·
                        rfl

theorem cell23_8126410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 6, 1, 1, 3, 2].length) (baseStart_8126410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8126410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8126410 prefixEnd_8126410 := by exact prefixLift 8126410
  have htrace : WordTrace (prefixWord ++ tailWord_8126410) baseStart_8126410 baseEnd_8126410 := by
    simpa [prefixWord, tailWord_8126410, baseEnd_8126410] using wordTrace_append hprefix tailTrace_8126410
  have hstable : (prefixWord ++ tailWord_8126410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8126410).length < 2 ^ (prefixWord ++ tailWord_8126410).sum := by decide
  have hdescent : baseEnd_8126410 < baseStart_8126410 := by decide
  rcases family_descends (prefixWord ++ tailWord_8126410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8126423 : List Nat := [1, 1, 3, 2, 1, 1, 5, 1, 4, 2, 2]
def baseStart_8126423 : Nat := 118140960795 + 8126423 * 2 ^ 59
def prefixEnd_8126423 : Nat := 4983230072969 + 3 ^ 40 * 8126423 * 2
def baseEnd_8126423 : Nat := 4172761000752164066339767

theorem tailTrace_8126423 : CollatzResearch.WordTrace tailWord_8126423 prefixEnd_8126423 4172761000752164066339767 := by
  unfold tailWord_8126423
  simp only [CollatzResearch.WordTrace]
  refine ⟨296394996638364828398535923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197596664425576552265690615 296394996638364828398535923)
  ·
    refine ⟨444592494957547242597803885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296394996638364828398535923 444592494957547242597803885)
    ·
      refine ⟨166722185609080215974176457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 444592494957547242597803885 166722185609080215974176457)
      ·
        refine ⟨125041639206810161980632343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166722185609080215974176457 125041639206810161980632343)
        ·
          refine ⟨187562458810215242970948515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125041639206810161980632343 187562458810215242970948515)
          ·
            refine ⟨281343688215322864456422773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187562458810215242970948515 281343688215322864456422773)
            ·
              refine ⟨26375970770186518542789635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 281343688215322864456422773 26375970770186518542789635)
              ·
                refine ⟨39563956155279777814184453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26375970770186518542789635 39563956155279777814184453)
                ·
                  refine ⟨7418241779114958340159585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39563956155279777814184453 7418241779114958340159585)
                  ·
                    refine ⟨5563681334336218755119689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7418241779114958340159585 5563681334336218755119689)
                    ·
                      refine ⟨4172761000752164066339767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5563681334336218755119689 4172761000752164066339767)
                      ·
                        rfl

theorem cell23_8126423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 1, 4, 2, 2].length) (baseStart_8126423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8126423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8126423 prefixEnd_8126423 := by exact prefixLift 8126423
  have htrace : WordTrace (prefixWord ++ tailWord_8126423) baseStart_8126423 baseEnd_8126423 := by
    simpa [prefixWord, tailWord_8126423, baseEnd_8126423] using wordTrace_append hprefix tailTrace_8126423
  have hstable : (prefixWord ++ tailWord_8126423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8126423).length < 2 ^ (prefixWord ++ tailWord_8126423).sum := by decide
  have hdescent : baseEnd_8126423 < baseStart_8126423 := by decide
  rcases family_descends (prefixWord ++ tailWord_8126423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8126434 : List Nat := [3, 3, 3, 1, 2, 1, 3, 1, 2, 1, 3]
def baseStart_8126434 : Nat := 118140960795 + 8126434 * 2 ^ 59
def prefixEnd_8126434 : Nat := 4983230072969 + 3 ^ 40 * 8126434 * 2
def baseEnd_8126434 : Nat := 4172766649039363523302217

theorem tailTrace_8126434 : CollatzResearch.WordTrace tailWord_8126434 prefixEnd_8126434 4172766649039363523302217 := by
  unfold tailWord_8126434
  simp only [CollatzResearch.WordTrace]
  refine ⟨74098849460331244319296589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197596931894216651518124237 74098849460331244319296589)
  ·
    refine ⟨27787068547624216619736221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74098849460331244319296589 27787068547624216619736221)
    ·
      refine ⟨10420150705359081232401083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27787068547624216619736221 10420150705359081232401083)
      ·
        refine ⟨15630226058038621848601625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10420150705359081232401083 15630226058038621848601625)
        ·
          refine ⟨11722669543528966386451219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15630226058038621848601625 11722669543528966386451219)
          ·
            refine ⟨17584004315293449579676829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11722669543528966386451219 17584004315293449579676829)
            ·
              refine ⟨6594001618235043592378811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17584004315293449579676829 6594001618235043592378811)
              ·
                refine ⟨9891002427352565388568217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6594001618235043592378811 9891002427352565388568217)
                ·
                  refine ⟨7418251820514424041426163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9891002427352565388568217 7418251820514424041426163)
                  ·
                    refine ⟨11127377730771636062139245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7418251820514424041426163 11127377730771636062139245)
                    ·
                      refine ⟨4172766649039363523302217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11127377730771636062139245 4172766649039363523302217)
                      ·
                        rfl

theorem cell23_8126434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 3, 1, 2, 1, 3].length) (baseStart_8126434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8126434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8126434 prefixEnd_8126434 := by exact prefixLift 8126434
  have htrace : WordTrace (prefixWord ++ tailWord_8126434) baseStart_8126434 baseEnd_8126434 := by
    simpa [prefixWord, tailWord_8126434, baseEnd_8126434] using wordTrace_append hprefix tailTrace_8126434
  have hstable : (prefixWord ++ tailWord_8126434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8126434).length < 2 ^ (prefixWord ++ tailWord_8126434).sum := by decide
  have hdescent : baseEnd_8126434 < baseStart_8126434 := by decide
  rcases family_descends (prefixWord ++ tailWord_8126434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8126446 : List Nat := [4, 1, 2, 1, 3, 1, 2, 2, 7]
def baseStart_8126446 : Nat := 118140960795 + 8126446 * 2 ^ 59
def prefixEnd_8126446 : Nat := 4983230072969 + 3 ^ 40 * 8126446 * 2
def baseEnd_8126446 : Nat := 463641423423024164039129

theorem tailTrace_8126446 : CollatzResearch.WordTrace tailWord_8126446 prefixEnd_8126446 463641423423024164039129 := by
  unfold tailWord_8126446
  simp only [CollatzResearch.WordTrace]
  refine ⟨37049479439660187915827899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 197597223678187668884415461 37049479439660187915827899)
  ·
    refine ⟨55574219159490281873741849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37049479439660187915827899 55574219159490281873741849)
    ·
      refine ⟨41680664369617711405306387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55574219159490281873741849 41680664369617711405306387)
      ·
        refine ⟨62520996554426567107959581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41680664369617711405306387 62520996554426567107959581)
        ·
          refine ⟨23445373707909962665484843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62520996554426567107959581 23445373707909962665484843)
          ·
            refine ⟨35168060561864943998227265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23445373707909962665484843 35168060561864943998227265)
            ·
              refine ⟨26376045421398707998670449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35168060561864943998227265 26376045421398707998670449)
              ·
                refine ⟨19782034066049030999002837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26376045421398707998670449 19782034066049030999002837)
                ·
                  refine ⟨463641423423024164039129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19782034066049030999002837 463641423423024164039129)
                  ·
                    rfl

theorem cell23_8126446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 2, 7].length) (baseStart_8126446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8126446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8126446 prefixEnd_8126446 := by exact prefixLift 8126446
  have htrace : WordTrace (prefixWord ++ tailWord_8126446) baseStart_8126446 baseEnd_8126446 := by
    simpa [prefixWord, tailWord_8126446, baseEnd_8126446] using wordTrace_append hprefix tailTrace_8126446
  have hstable : (prefixWord ++ tailWord_8126446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8126446).length < 2 ^ (prefixWord ++ tailWord_8126446).sum := by decide
  have hdescent : baseEnd_8126446 < baseStart_8126446 := by decide
  rcases family_descends (prefixWord ++ tailWord_8126446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8126459 : List Nat := [1, 1, 1, 1, 1, 3, 6, 1, 1, 7]
def baseStart_8126459 : Nat := 118140960795 + 8126459 * 2 ^ 59
def prefixEnd_8126459 : Nat := 4983230072969 + 3 ^ 40 * 8126459 * 2
def baseEnd_8126459 : Nat := 1390926495351908641829867

theorem tailTrace_8126459 : CollatzResearch.WordTrace tailWord_8126459 prefixEnd_8126459 1390926495351908641829867 := by
  unfold tailWord_8126459
  simp only [CollatzResearch.WordTrace]
  refine ⟨296396309666234406546846431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197597539777489604364564287 296396309666234406546846431)
  ·
    refine ⟨444594464499351609820269647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296396309666234406546846431 444594464499351609820269647)
    ·
      refine ⟨666891696749027414730404471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 444594464499351609820269647 666891696749027414730404471)
      ·
        refine ⟨1000337545123541122095606707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 666891696749027414730404471 1000337545123541122095606707)
        ·
          refine ⟨1500506317685311683143410061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1000337545123541122095606707 1500506317685311683143410061)
          ·
            refine ⟨562689869131991881178778773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1500506317685311683143410061 562689869131991881178778773)
            ·
              refine ⟨26376087615562119430255255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 562689869131991881178778773 26376087615562119430255255)
              ·
                refine ⟨39564131423343179145382883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26376087615562119430255255 39564131423343179145382883)
                ·
                  refine ⟨59346197135014768718074325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39564131423343179145382883 59346197135014768718074325)
                  ·
                    refine ⟨1390926495351908641829867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59346197135014768718074325 1390926495351908641829867)
                    ·
                      rfl

theorem cell23_8126459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 1, 1, 7].length) (baseStart_8126459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8126459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8126459 prefixEnd_8126459 := by exact prefixLift 8126459
  have htrace : WordTrace (prefixWord ++ tailWord_8126459) baseStart_8126459 baseEnd_8126459 := by
    simpa [prefixWord, tailWord_8126459, baseEnd_8126459] using wordTrace_append hprefix tailTrace_8126459
  have hstable : (prefixWord ++ tailWord_8126459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8126459).length < 2 ^ (prefixWord ++ tailWord_8126459).sum := by decide
  have hdescent : baseEnd_8126459 < baseStart_8126459 := by decide
  rcases family_descends (prefixWord ++ tailWord_8126459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8126476 : List Nat := [2, 2, 1, 2, 3, 1, 3, 2, 2, 5]
def baseStart_8126476 : Nat := 118140960795 + 8126476 * 2 ^ 59
def prefixEnd_8126476 : Nat := 4983230072969 + 3 ^ 40 * 8126476 * 2
def baseEnd_8126476 : Nat := 1390929405075617452992341

theorem tailTrace_8126476 : CollatzResearch.WordTrace tailWord_8126476 prefixEnd_8126476 1390929405075617452992341 := by
  unfold tailWord_8126476
  simp only [CollatzResearch.WordTrace]
  refine ⟨148198464853586409225107641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197597953138115212300143521 148198464853586409225107641)
  ·
    refine ⟨111148848640189806918830731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148198464853586409225107641 111148848640189806918830731)
    ·
      refine ⟨166723272960284710378246097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111148848640189806918830731 166723272960284710378246097)
      ·
        refine ⟨125042454720213532783684573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166723272960284710378246097 125042454720213532783684573)
        ·
          refine ⟨46890920520080074793881715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125042454720213532783684573 46890920520080074793881715)
          ·
            refine ⟨70336380780120112190822573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46890920520080074793881715 70336380780120112190822573)
            ·
              refine ⟨26376142792545042071558465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70336380780120112190822573 26376142792545042071558465)
              ·
                refine ⟨19782107094408781553668849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26376142792545042071558465 19782107094408781553668849)
                ·
                  refine ⟨14836580320806586165251637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19782107094408781553668849 14836580320806586165251637)
                  ·
                    refine ⟨1390929405075617452992341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14836580320806586165251637 1390929405075617452992341)
                    ·
                      rfl

theorem cell23_8126476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 2, 2, 5].length) (baseStart_8126476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8126476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8126476 prefixEnd_8126476 := by exact prefixLift 8126476
  have htrace : WordTrace (prefixWord ++ tailWord_8126476) baseStart_8126476 baseEnd_8126476 := by
    simpa [prefixWord, tailWord_8126476, baseEnd_8126476] using wordTrace_append hprefix tailTrace_8126476
  have hstable : (prefixWord ++ tailWord_8126476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8126476).length < 2 ^ (prefixWord ++ tailWord_8126476).sum := by decide
  have hdescent : baseEnd_8126476 < baseStart_8126476 := by decide
  rcases family_descends (prefixWord ++ tailWord_8126476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8126513 : List Nat := [1, 2, 2, 3, 1, 4, 2, 1, 2, 1, 4]
def baseStart_8126513 : Nat := 118140960795 + 8126513 * 2 ^ 59
def prefixEnd_8126513 : Nat := 4983230072969 + 3 ^ 40 * 8126513 * 2
def baseEnd_8126513 : Nat := 4172807214011068714214353

theorem tailTrace_8126513 : CollatzResearch.WordTrace tailWord_8126513 prefixEnd_8126513 4172807214011068714214353 := by
  unfold tailWord_8126513
  simp only [CollatzResearch.WordTrace]
  refine ⟨296398279208038773769312193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197598852805359182512874795 296398279208038773769312193)
  ·
    refine ⟨222298709406029080326984145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296398279208038773769312193 222298709406029080326984145)
    ·
      refine ⟨166724032054521810245238109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222298709406029080326984145 166724032054521810245238109)
      ·
        refine ⟨62521512020445678841964291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166724032054521810245238109 62521512020445678841964291)
        ·
          refine ⟨93782268030668518262946437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62521512020445678841964291 93782268030668518262946437)
          ·
            refine ⟨17584175255750347174302457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93782268030668518262946437 17584175255750347174302457)
            ·
              refine ⟨13188131441812760380726843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17584175255750347174302457 13188131441812760380726843)
              ·
                refine ⟨19782197162719140571090265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13188131441812760380726843 19782197162719140571090265)
                ·
                  refine ⟨14836647872039355428317699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19782197162719140571090265 14836647872039355428317699)
                  ·
                    refine ⟨22254971808059033142476549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14836647872039355428317699 22254971808059033142476549)
                    ·
                      refine ⟨4172807214011068714214353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22254971808059033142476549 4172807214011068714214353)
                      ·
                        rfl

theorem cell23_8126513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 2, 1, 2, 1, 4].length) (baseStart_8126513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8126513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8126513 prefixEnd_8126513 := by exact prefixLift 8126513
  have htrace : WordTrace (prefixWord ++ tailWord_8126513) baseStart_8126513 baseEnd_8126513 := by
    simpa [prefixWord, tailWord_8126513, baseEnd_8126513] using wordTrace_append hprefix tailTrace_8126513
  have hstable : (prefixWord ++ tailWord_8126513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8126513).length < 2 ^ (prefixWord ++ tailWord_8126513).sum := by decide
  have hdescent : baseEnd_8126513 < baseStart_8126513 := by decide
  rcases family_descends (prefixWord ++ tailWord_8126513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8126519 : List Nat := [1, 1, 3, 1, 2, 2, 2, 1, 10]
def baseStart_8126519 : Nat := 118140960795 + 8126519 * 2 ^ 59
def prefixEnd_8126519 : Nat := 4983230072969 + 3 ^ 40 * 8126519 * 2
def baseEnd_8126519 : Nat := 463645588321666187859925

theorem tailTrace_8126519 : CollatzResearch.WordTrace tailWord_8126519 prefixEnd_8126519 463645588321666187859925 := by
  unfold tailWord_8126519
  simp only [CollatzResearch.WordTrace]
  refine ⟨296398498046017036794030611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197598998697344691196020407 296398498046017036794030611)
  ·
    refine ⟨444597747069025555191045917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296398498046017036794030611 444597747069025555191045917)
    ·
      refine ⟨166724155150884583196642219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 444597747069025555191045917 166724155150884583196642219)
      ·
        refine ⟨250086232726326874794963329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166724155150884583196642219 250086232726326874794963329)
        ·
          refine ⟨187564674544745156096222497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 250086232726326874794963329 187564674544745156096222497)
          ·
            refine ⟨140673505908558867072166873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 187564674544745156096222497 140673505908558867072166873)
            ·
              refine ⟨105505129431419150304125155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140673505908558867072166873 105505129431419150304125155)
              ·
                refine ⟨158257694147128725456187733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105505129431419150304125155 158257694147128725456187733)
                ·
                  refine ⟨463645588321666187859925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 158257694147128725456187733 463645588321666187859925)
                  ·
                    rfl

theorem cell23_8126519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 1, 10].length) (baseStart_8126519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8126519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8126519 prefixEnd_8126519 := by exact prefixLift 8126519
  have htrace : WordTrace (prefixWord ++ tailWord_8126519) baseStart_8126519 baseEnd_8126519 := by
    simpa [prefixWord, tailWord_8126519, baseEnd_8126519] using wordTrace_append hprefix tailTrace_8126519
  have hstable : (prefixWord ++ tailWord_8126519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8126519).length < 2 ^ (prefixWord ++ tailWord_8126519).sum := by decide
  have hdescent : baseEnd_8126519 < baseStart_8126519 := by decide
  rcases family_descends (prefixWord ++ tailWord_8126519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8126539 : List Nat := [1, 1, 1, 1, 3, 1, 2, 3, 1, 1, 8]
def baseStart_8126539 : Nat := 118140960795 + 8126539 * 2 ^ 59
def prefixEnd_8126539 : Nat := 4983230072969 + 3 ^ 40 * 8126539 * 2
def baseEnd_8126539 : Nat := 4172820564508085612489233

theorem tailTrace_8126539 : CollatzResearch.WordTrace tailWord_8126539 prefixEnd_8126539 4172820564508085612489233 := by
  unfold tailWord_8126539
  simp only [CollatzResearch.WordTrace]
  refine ⟨296399227505944580209758671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197599485003963053473172447 296399227505944580209758671)
  ·
    refine ⟨444598841258916870314638007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296399227505944580209758671 444598841258916870314638007)
    ·
      refine ⟨666898261888375305471957011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 444598841258916870314638007 666898261888375305471957011)
      ·
        refine ⟨1000347392832562958207935517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 666898261888375305471957011 1000347392832562958207935517)
        ·
          refine ⟨375130272312211109327975819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1000347392832562958207935517 375130272312211109327975819)
          ·
            refine ⟨562695408468316663991963729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 375130272312211109327975819 562695408468316663991963729)
            ·
              refine ⟨422021556351237497993972797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 562695408468316663991963729 422021556351237497993972797)
              ·
                refine ⟨158258083631714061747739799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 422021556351237497993972797 158258083631714061747739799)
                ·
                  refine ⟨237387125447571092621609699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 158258083631714061747739799 237387125447571092621609699)
                  ·
                    refine ⟨356080688171356638932414549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 237387125447571092621609699 356080688171356638932414549)
                    ·
                      refine ⟨4172820564508085612489233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 356080688171356638932414549 4172820564508085612489233)
                      ·
                        rfl

theorem cell23_8126539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 3, 1, 1, 8].length) (baseStart_8126539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8126539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8126539 prefixEnd_8126539 := by exact prefixLift 8126539
  have htrace : WordTrace (prefixWord ++ tailWord_8126539) baseStart_8126539 baseEnd_8126539 := by
    simpa [prefixWord, tailWord_8126539, baseEnd_8126539] using wordTrace_append hprefix tailTrace_8126539
  have hstable : (prefixWord ++ tailWord_8126539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8126539).length < 2 ^ (prefixWord ++ tailWord_8126539).sum := by decide
  have hdescent : baseEnd_8126539 < baseStart_8126539 := by decide
  rcases family_descends (prefixWord ++ tailWord_8126539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8126563 : List Nat := [1, 1, 1, 5, 1, 1, 3, 1, 5, 1, 3]
def baseStart_8126563 : Nat := 118140960795 + 8126563 * 2 ^ 59
def prefixEnd_8126563 : Nat := 4983230072969 + 3 ^ 40 * 8126563 * 2
def baseEnd_8126563 : Nat := 4172832888043793518589123

theorem tailTrace_8126563 : CollatzResearch.WordTrace tailWord_8126563 prefixEnd_8126563 4172832888043793518589123 := by
  unfold tailWord_8126563
  simp only [CollatzResearch.WordTrace]
  refine ⟨296400102857857632308632343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197600068571905088205754895 296400102857857632308632343)
  ·
    refine ⟨444600154286786448462948515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296400102857857632308632343 444600154286786448462948515)
    ·
      refine ⟨666900231430179672694422773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 444600154286786448462948515 666900231430179672694422773)
      ·
        refine ⟨62521896696579344315102135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 666900231430179672694422773 62521896696579344315102135)
        ·
          refine ⟨93782845044869016472653203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62521896696579344315102135 93782845044869016472653203)
          ·
            refine ⟨140674267567303524708979805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93782845044869016472653203 140674267567303524708979805)
            ·
              refine ⟨52752850337738821765867427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 140674267567303524708979805 52752850337738821765867427)
              ·
                refine ⟨79129275506608232648801141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52752850337738821765867427 79129275506608232648801141)
                ·
                  refine ⟨7418369578744521810825107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 79129275506608232648801141 7418369578744521810825107)
                  ·
                    refine ⟨11127554368116782716237661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7418369578744521810825107 11127554368116782716237661)
                    ·
                      refine ⟨4172832888043793518589123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11127554368116782716237661 4172832888043793518589123)
                      ·
                        rfl

theorem cell23_8126563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 1, 5, 1, 3].length) (baseStart_8126563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8126563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8126563 prefixEnd_8126563 := by exact prefixLift 8126563
  have htrace : WordTrace (prefixWord ++ tailWord_8126563) baseStart_8126563 baseEnd_8126563 := by
    simpa [prefixWord, tailWord_8126563, baseEnd_8126563] using wordTrace_append hprefix tailTrace_8126563
  have hstable : (prefixWord ++ tailWord_8126563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8126563).length < 2 ^ (prefixWord ++ tailWord_8126563).sum := by decide
  have hdescent : baseEnd_8126563 < baseStart_8126563 := by decide
  rcases family_descends (prefixWord ++ tailWord_8126563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8126583 : List Nat := [1, 1, 3, 1, 1, 6, 1, 3, 1, 5]
def baseStart_8126583 : Nat := 118140960795 + 8126583 * 2 ^ 59
def prefixEnd_8126583 : Nat := 4983230072969 + 3 ^ 40 * 8126583 * 2
def baseEnd_8126583 : Nat := 1390947719218961146779677

theorem tailTrace_8126583 : CollatzResearch.WordTrace tailWord_8126583 prefixEnd_8126583 1390947719218961146779677 := by
  unfold tailWord_8126583
  simp only [CollatzResearch.WordTrace]
  refine ⟨296400832317785175724360403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197600554878523450482906935 296400832317785175724360403)
  ·
    refine ⟨444601248476677763586540605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296400832317785175724360403 444601248476677763586540605)
    ·
      refine ⟨166725468178754161344952727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 444601248476677763586540605 166725468178754161344952727)
      ·
        refine ⟨250088202268131242017429091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166725468178754161344952727 250088202268131242017429091)
        ·
          refine ⟨375132303402196863026143637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250088202268131242017429091 375132303402196863026143637)
          ·
            refine ⟨17584326721977977954350483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 375132303402196863026143637 17584326721977977954350483)
            ·
              refine ⟨26376490082966966931525725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17584326721977977954350483 26376490082966966931525725)
              ·
                refine ⟨9891183781112612599322147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26376490082966966931525725 9891183781112612599322147)
                ·
                  refine ⟨14836775671668918898983221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9891183781112612599322147 14836775671668918898983221)
                  ·
                    refine ⟨1390947719218961146779677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14836775671668918898983221 1390947719218961146779677)
                    ·
                      rfl

theorem cell23_8126583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 3, 1, 5].length) (baseStart_8126583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8126583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8126583 prefixEnd_8126583 := by exact prefixLift 8126583
  have htrace : WordTrace (prefixWord ++ tailWord_8126583) baseStart_8126583 baseEnd_8126583 := by
    simpa [prefixWord, tailWord_8126583, baseEnd_8126583] using wordTrace_append hprefix tailTrace_8126583
  have hstable : (prefixWord ++ tailWord_8126583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8126583).length < 2 ^ (prefixWord ++ tailWord_8126583).sum := by decide
  have hdescent : baseEnd_8126583 < baseStart_8126583 := by decide
  rcases family_descends (prefixWord ++ tailWord_8126583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8126597 : List Nat := [1, 3, 1, 1, 5, 1, 2, 4, 1, 1, 3]
def baseStart_8126597 : Nat := 118140960795 + 8126597 * 2 ^ 59
def prefixEnd_8126597 : Nat := 4983230072969 + 3 ^ 40 * 8126597 * 2
def baseEnd_8126597 : Nat := 4172850346386046385563967

theorem tailTrace_8126597 : CollatzResearch.WordTrace tailWord_8126597 prefixEnd_8126597 4172850346386046385563967 := by
  unfold tailWord_8126597
  simp only [CollatzResearch.WordTrace]
  refine ⟨296401342939734456115370045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197600895293156304076913363 296401342939734456115370045)
  ·
    refine ⟨111150503602400421043263767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 296401342939734456115370045 111150503602400421043263767)
    ·
      refine ⟨166725755403600631564895651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111150503602400421043263767 166725755403600631564895651)
      ·
        refine ⟨250088633105400947347343477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166725755403600631564895651 250088633105400947347343477)
        ·
          refine ⟨23445809353631338813813451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 250088633105400947347343477 23445809353631338813813451)
          ·
            refine ⟨35168714030447008220720177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23445809353631338813813451 35168714030447008220720177)
            ·
              refine ⟨26376535522835256165540133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35168714030447008220720177 26376535522835256165540133)
              ·
                refine ⟨4945600410531610531038775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26376535522835256165540133 4945600410531610531038775)
                ·
                  refine ⟨7418400615797415796558163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4945600410531610531038775 7418400615797415796558163)
                  ·
                    refine ⟨11127600923696123694837245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7418400615797415796558163 11127600923696123694837245)
                    ·
                      refine ⟨4172850346386046385563967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11127600923696123694837245 4172850346386046385563967)
                      ·
                        rfl

theorem cell23_8126597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 4, 1, 1, 3].length) (baseStart_8126597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8126597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8126597 prefixEnd_8126597 := by exact prefixLift 8126597
  have htrace : WordTrace (prefixWord ++ tailWord_8126597) baseStart_8126597 baseEnd_8126597 := by
    simpa [prefixWord, tailWord_8126597, baseEnd_8126597] using wordTrace_append hprefix tailTrace_8126597
  have hstable : (prefixWord ++ tailWord_8126597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8126597).length < 2 ^ (prefixWord ++ tailWord_8126597).sum := by decide
  have hdescent : baseEnd_8126597 < baseStart_8126597 := by decide
  rcases family_descends (prefixWord ++ tailWord_8126597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8126620 : List Nat := [2, 2, 3, 2, 1, 1, 4, 2, 1, 1, 4]
def baseStart_8126620 : Nat := 118140960795 + 8126620 * 2 ^ 59
def prefixEnd_8126620 : Nat := 4983230072969 + 3 ^ 40 * 8126620 * 2
def baseEnd_8126620 : Nat := 4172862156441099795576361

theorem tailTrace_8126620 : CollatzResearch.WordTrace tailWord_8126620 prefixEnd_8126620 4172862156441099795576361 := by
  unfold tailWord_8126620
  simp only [CollatzResearch.WordTrace]
  refine ⟨148201090909325565521728657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197601454545767420695638209 148201090909325565521728657)
  ·
    refine ⟨111150818181994174141296493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148201090909325565521728657 111150818181994174141296493)
    ·
      refine ⟨41681556818247815302986185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111150818181994174141296493 41681556818247815302986185)
      ·
        refine ⟨31261167613685861477239639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41681556818247815302986185 31261167613685861477239639)
        ·
          refine ⟨46891751420528792215859459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31261167613685861477239639 46891751420528792215859459)
          ·
            refine ⟨70337627130793188323789189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46891751420528792215859459 70337627130793188323789189)
            ·
              refine ⟨13188305087023722810710473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70337627130793188323789189 13188305087023722810710473)
              ·
                refine ⟨9891228815267792108032855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13188305087023722810710473 9891228815267792108032855)
                ·
                  refine ⟨14836843222901688162049283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9891228815267792108032855 14836843222901688162049283)
                  ·
                    refine ⟨22255264834352532243073925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14836843222901688162049283 22255264834352532243073925)
                    ·
                      refine ⟨4172862156441099795576361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22255264834352532243073925 4172862156441099795576361)
                      ·
                        rfl

theorem cell23_8126620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 4, 2, 1, 1, 4].length) (baseStart_8126620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8126620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8126620 prefixEnd_8126620 := by exact prefixLift 8126620
  have htrace : WordTrace (prefixWord ++ tailWord_8126620) baseStart_8126620 baseEnd_8126620 := by
    simpa [prefixWord, tailWord_8126620, baseEnd_8126620] using wordTrace_append hprefix tailTrace_8126620
  have hstable : (prefixWord ++ tailWord_8126620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8126620).length < 2 ^ (prefixWord ++ tailWord_8126620).sum := by decide
  have hdescent : baseEnd_8126620 < baseStart_8126620 := by decide
  rcases family_descends (prefixWord ++ tailWord_8126620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8126631 : List Nat := [1, 1, 6, 2, 2, 2, 1, 3, 1, 1, 3]
def baseStart_8126631 : Nat := 118140960795 + 8126631 * 2 ^ 59
def prefixEnd_8126631 : Nat := 4983230072969 + 3 ^ 40 * 8126631 * 2
def baseEnd_8126631 : Nat := 4172867804728299252538811

theorem tailTrace_8126631 : CollatzResearch.WordTrace tailWord_8126631 prefixEnd_8126631 4172867804728299252538811 := by
  unfold tailWord_8126631
  simp only [CollatzResearch.WordTrace]
  refine ⟨296402583021611279922107747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197601722014407519948071831 296402583021611279922107747)
  ·
    refine ⟨444603874532416919883161621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296402583021611279922107747 444603874532416919883161621)
    ·
      refine ⟨20840806618707043119523201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 444603874532416919883161621 20840806618707043119523201)
      ·
        refine ⟨15630604964030282339642401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20840806618707043119523201 15630604964030282339642401)
        ·
          refine ⟨11722953723022711754731801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15630604964030282339642401 11722953723022711754731801)
          ·
            refine ⟨8792215292267033816048851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11722953723022711754731801 8792215292267033816048851)
            ·
              refine ⟨13188322938400550724073277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8792215292267033816048851 13188322938400550724073277)
              ·
                refine ⟨4945621101900206521527479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13188322938400550724073277 4945621101900206521527479)
                ·
                  refine ⟨7418431652850309782291219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4945621101900206521527479 7418431652850309782291219)
                  ·
                    refine ⟨11127647479275464673436829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7418431652850309782291219 11127647479275464673436829)
                    ·
                      refine ⟨4172867804728299252538811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11127647479275464673436829 4172867804728299252538811)
                      ·
                        rfl

theorem cell23_8126631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 1, 3, 1, 1, 3].length) (baseStart_8126631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8126631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8126631 prefixEnd_8126631 := by exact prefixLift 8126631
  have htrace : WordTrace (prefixWord ++ tailWord_8126631) baseStart_8126631 baseEnd_8126631 := by
    simpa [prefixWord, tailWord_8126631, baseEnd_8126631] using wordTrace_append hprefix tailTrace_8126631
  have hstable : (prefixWord ++ tailWord_8126631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8126631).length < 2 ^ (prefixWord ++ tailWord_8126631).sum := by decide
  have hdescent : baseEnd_8126631 < baseStart_8126631 := by decide
  rcases family_descends (prefixWord ++ tailWord_8126631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8126663 : List Nat := [1, 1, 4, 1, 1, 1, 1, 1, 1, 9, 2]
def baseStart_8126663 : Nat := 118140960795 + 8126663 * 2 ^ 59
def prefixEnd_8126663 : Nat := 4983230072969 + 3 ^ 40 * 8126663 * 2
def baseEnd_8126663 : Nat := 4172884236109243127338663

theorem tailTrace_8126663 : CollatzResearch.WordTrace tailWord_8126663 prefixEnd_8126663 4172884236109243127338663 := by
  unfold tailWord_8126663
  simp only [CollatzResearch.WordTrace]
  refine ⟨296403750157495349387272643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197602500104996899591515095 296403750157495349387272643)
  ·
    refine ⟨444605625236243024080908965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296403750157495349387272643 444605625236243024080908965)
    ·
      refine ⟨83363554731795567015170431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 444605625236243024080908965 83363554731795567015170431)
      ·
        refine ⟨125045332097693350522755647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83363554731795567015170431 125045332097693350522755647)
        ·
          refine ⟨187567998146540025784133471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125045332097693350522755647 187567998146540025784133471)
          ·
            refine ⟨281351997219810038676200207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187567998146540025784133471 281351997219810038676200207)
            ·
              refine ⟨422027995829715058014300311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 281351997219810038676200207 422027995829715058014300311)
              ·
                refine ⟨633041993744572587021450467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 422027995829715058014300311 633041993744572587021450467)
                ·
                  refine ⟨949562990616858880532175701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 633041993744572587021450467 949562990616858880532175701)
                  ·
                    refine ⟨5563845648145657503118217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 949562990616858880532175701 5563845648145657503118217)
                    ·
                      refine ⟨4172884236109243127338663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5563845648145657503118217 4172884236109243127338663)
                      ·
                        rfl

theorem cell23_8126663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 9, 2].length) (baseStart_8126663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8126663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8126663 prefixEnd_8126663 := by exact prefixLift 8126663
  have htrace : WordTrace (prefixWord ++ tailWord_8126663) baseStart_8126663 baseEnd_8126663 := by
    simpa [prefixWord, tailWord_8126663, baseEnd_8126663] using wordTrace_append hprefix tailTrace_8126663
  have hstable : (prefixWord ++ tailWord_8126663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8126663).length < 2 ^ (prefixWord ++ tailWord_8126663).sum := by decide
  have hdescent : baseEnd_8126663 < baseStart_8126663 := by decide
  rcases family_descends (prefixWord ++ tailWord_8126663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8126723 : List Nat := [1, 1, 1, 3, 2, 3, 3, 1, 2, 2, 4]
def baseStart_8126723 : Nat := 118140960795 + 8126723 * 2 ^ 59
def prefixEnd_8126723 : Nat := 4983230072969 + 3 ^ 40 * 8126723 * 2
def baseEnd_8126723 : Nat := 4172915044948512892588387

theorem tailTrace_8126723 : CollatzResearch.WordTrace tailWord_8126723 prefixEnd_8126723 4172915044948512892588387 := by
  unfold tailWord_8126723
  simp only [CollatzResearch.WordTrace]
  refine ⟨296405938537277979634456823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197603959024851986422971215 296405938537277979634456823)
  ·
    refine ⟨444608907805916969451685235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296405938537277979634456823 444608907805916969451685235)
    ·
      refine ⟨666913361708875454177527853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 444608907805916969451685235 666913361708875454177527853)
      ·
        refine ⟨250092510640828295316572945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 666913361708875454177527853 250092510640828295316572945)
        ·
          refine ⟨187569382980621221487429709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 250092510640828295316572945 187569382980621221487429709)
          ·
            refine ⟨70338518617732958057786141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 187569382980621221487429709 70338518617732958057786141)
            ·
              refine ⟨26376944481649859271669803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70338518617732958057786141 26376944481649859271669803)
              ·
                refine ⟨39565416722474788907504705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26376944481649859271669803 39565416722474788907504705)
                ·
                  refine ⟨29674062541856091680628529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39565416722474788907504705 29674062541856091680628529)
                  ·
                    refine ⟨22255546906392068760471397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29674062541856091680628529 22255546906392068760471397)
                    ·
                      refine ⟨4172915044948512892588387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22255546906392068760471397 4172915044948512892588387)
                      ·
                        rfl

theorem cell23_8126723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 1, 2, 2, 4].length) (baseStart_8126723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8126723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8126723 prefixEnd_8126723 := by exact prefixLift 8126723
  have htrace : WordTrace (prefixWord ++ tailWord_8126723) baseStart_8126723 baseEnd_8126723 := by
    simpa [prefixWord, tailWord_8126723, baseEnd_8126723] using wordTrace_append hprefix tailTrace_8126723
  have hstable : (prefixWord ++ tailWord_8126723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8126723).length < 2 ^ (prefixWord ++ tailWord_8126723).sum := by decide
  have hdescent : baseEnd_8126723 < baseStart_8126723 := by decide
  rcases family_descends (prefixWord ++ tailWord_8126723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8126773 : List Nat := [1, 3, 3, 1, 2, 1, 2, 1, 1, 1, 7]
def baseStart_8126773 : Nat := 118140960795 + 8126773 * 2 ^ 59
def prefixEnd_8126773 : Nat := 4983230072969 + 3 ^ 40 * 8126773 * 2
def baseEnd_8126773 : Nat := 4172940718981237696963157

theorem tailTrace_8126773 : CollatzResearch.WordTrace tailWord_8126773 prefixEnd_8126773 4172940718981237696963157 := by
  unfold tailWord_8126773
  simp only [CollatzResearch.WordTrace]
  refine ⟨296407762187096838173776973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197605174791397892115851315 296407762187096838173776973)
  ·
    refine ⟨111152910820161314315166365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 296407762187096838173776973 111152910820161314315166365)
    ·
      refine ⟨41682341557560492868187387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111152910820161314315166365 41682341557560492868187387)
      ·
        refine ⟨62523512336340739302281081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41682341557560492868187387 62523512336340739302281081)
        ·
          refine ⟨46892634252255554476710811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62523512336340739302281081 46892634252255554476710811)
          ·
            refine ⟨70338951378383331715066217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46892634252255554476710811 70338951378383331715066217)
            ·
              refine ⟨52754213533787498786299663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70338951378383331715066217 52754213533787498786299663)
              ·
                refine ⟨79131320300681248179449495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52754213533787498786299663 79131320300681248179449495)
                ·
                  refine ⟨118696980451021872269174243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79131320300681248179449495 118696980451021872269174243)
                  ·
                    refine ⟨178045470676532808403761365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 118696980451021872269174243 178045470676532808403761365)
                    ·
                      refine ⟨4172940718981237696963157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 178045470676532808403761365 4172940718981237696963157)
                      ·
                        rfl

theorem cell23_8126773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 1, 1, 1, 7].length) (baseStart_8126773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8126773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8126773 prefixEnd_8126773 := by exact prefixLift 8126773
  have htrace : WordTrace (prefixWord ++ tailWord_8126773) baseStart_8126773 baseEnd_8126773 := by
    simpa [prefixWord, tailWord_8126773, baseEnd_8126773] using wordTrace_append hprefix tailTrace_8126773
  have hstable : (prefixWord ++ tailWord_8126773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8126773).length < 2 ^ (prefixWord ++ tailWord_8126773).sum := by decide
  have hdescent : baseEnd_8126773 < baseStart_8126773 := by decide
  rcases family_descends (prefixWord ++ tailWord_8126773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8126783 : List Nat := [1, 1, 2, 2, 4, 1, 1, 1, 3, 3, 4]
def baseStart_8126783 : Nat := 118140960795 + 8126783 * 2 ^ 59
def prefixEnd_8126783 : Nat := 4983230072969 + 3 ^ 40 * 8126783 * 2
def baseEnd_8126783 : Nat := 4172945853787782657838111

theorem tailTrace_8126783 : CollatzResearch.WordTrace tailWord_8126783 prefixEnd_8126783 4172945853787782657838111 := by
  unfold tailWord_8126783
  simp only [CollatzResearch.WordTrace]
  refine ⟨296408126917060609881641003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197605417944707073254427335 296408126917060609881641003)
  ·
    refine ⟨444612190375590914822461505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296408126917060609881641003 444612190375590914822461505)
    ·
      refine ⟨333459142781693186116846129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 444612190375590914822461505 333459142781693186116846129)
      ·
        refine ⟨250094357086269889587634597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 333459142781693186116846129 250094357086269889587634597)
        ·
          refine ⟨46892691953675604297681487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 250094357086269889587634597 46892691953675604297681487)
          ·
            refine ⟨70339037930513406446522231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46892691953675604297681487 70339037930513406446522231)
            ·
              refine ⟨105508556895770109669783347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70339037930513406446522231 105508556895770109669783347)
              ·
                refine ⟨158262835343655164504675021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105508556895770109669783347 158262835343655164504675021)
                ·
                  refine ⟨59348563253870686689253133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 158262835343655164504675021 59348563253870686689253133)
                  ·
                    refine ⟨22255711220201507508469925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59348563253870686689253133 22255711220201507508469925)
                    ·
                      refine ⟨4172945853787782657838111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22255711220201507508469925 4172945853787782657838111)
                      ·
                        rfl

theorem cell23_8126783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 1, 3, 3, 4].length) (baseStart_8126783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8126783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8126783 prefixEnd_8126783 := by exact prefixLift 8126783
  have htrace : WordTrace (prefixWord ++ tailWord_8126783) baseStart_8126783 baseEnd_8126783 := by
    simpa [prefixWord, tailWord_8126783, baseEnd_8126783] using wordTrace_append hprefix tailTrace_8126783
  have hstable : (prefixWord ++ tailWord_8126783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8126783).length < 2 ^ (prefixWord ++ tailWord_8126783).sum := by decide
  have hdescent : baseEnd_8126783 < baseStart_8126783 := by decide
  rcases family_descends (prefixWord ++ tailWord_8126783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8126878 : List Nat := [4, 3, 1, 2, 1, 1, 4, 2, 1, 4]
def baseStart_8126878 : Nat := 118140960795 + 8126878 * 2 ^ 59
def prefixEnd_8126878 : Nat := 4983230072969 + 3 ^ 40 * 8126878 * 2
def baseEnd_8126878 : Nat := 1390998211483319928716725

theorem tailTrace_8126878 : CollatzResearch.WordTrace tailWord_8126878 prefixEnd_8126878 1390998211483319928716725 := by
  unfold tailWord_8126878
  simp only [CollatzResearch.WordTrace]
  refine ⟨37051448981464555138293661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 197607727901144294070899525 37051448981464555138293661)
  ·
    refine ⟨13894293368049208176860123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37051448981464555138293661 13894293368049208176860123)
    ·
      refine ⟨20841440052073812265290185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13894293368049208176860123 20841440052073812265290185)
      ·
        refine ⟨15631080039055359198967639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20841440052073812265290185 15631080039055359198967639)
        ·
          refine ⟨23446620058583038798451459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15631080039055359198967639 23446620058583038798451459)
          ·
            refine ⟨35169930087874558197677189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23446620058583038798451459 35169930087874558197677189)
            ·
              refine ⟨6594361891476479662064473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35169930087874558197677189 6594361891476479662064473)
              ·
                refine ⟨4945771418607359746548355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6594361891476479662064473 4945771418607359746548355)
                ·
                  refine ⟨7418657127911039619822533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4945771418607359746548355 7418657127911039619822533)
                  ·
                    refine ⟨1390998211483319928716725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7418657127911039619822533 1390998211483319928716725)
                    ·
                      rfl

theorem cell23_8126878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 4, 2, 1, 4].length) (baseStart_8126878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8126878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8126878 prefixEnd_8126878 := by exact prefixLift 8126878
  have htrace : WordTrace (prefixWord ++ tailWord_8126878) baseStart_8126878 baseEnd_8126878 := by
    simpa [prefixWord, tailWord_8126878, baseEnd_8126878] using wordTrace_append hprefix tailTrace_8126878
  have hstable : (prefixWord ++ tailWord_8126878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8126878).length < 2 ^ (prefixWord ++ tailWord_8126878).sum := by decide
  have hdescent : baseEnd_8126878 < baseStart_8126878 := by decide
  rcases family_descends (prefixWord ++ tailWord_8126878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8126924 : List Nat := [2, 2, 1, 4, 3, 1, 1, 3, 1, 1, 4]
def baseStart_8126924 : Nat := 118140960795 + 8126924 * 2 ^ 59
def prefixEnd_8126924 : Nat := 4983230072969 + 3 ^ 40 * 8126924 * 2
def baseEnd_8126924 : Nat := 4173018254560066606174963

theorem tailTrace_8126924 : CollatzResearch.WordTrace tailWord_8126924 prefixEnd_8126924 4173018254560066606174963 := by
  unfold tailWord_8126924
  simp only [CollatzResearch.WordTrace]
  refine ⟨148206634804774895481261913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197608846406366527308349217 148206634804774895481261913)
  ·
    refine ⟨111154976103581171610946435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148206634804774895481261913 111154976103581171610946435)
    ·
      refine ⟨166732464155371757416419653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111154976103581171610946435 166732464155371757416419653)
      ·
        refine ⟨31262337029132204515578685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 166732464155371757416419653 31262337029132204515578685)
        ·
          refine ⟨11723376385924576693342007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31262337029132204515578685 11723376385924576693342007)
          ·
            refine ⟨17585064578886865040013011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11723376385924576693342007 17585064578886865040013011)
            ·
              refine ⟨26377596868330297560019517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17585064578886865040013011 26377596868330297560019517)
              ·
                refine ⟨9891598825623861585007319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26377596868330297560019517 9891598825623861585007319)
                ·
                  refine ⟨14837398238435792377510979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9891598825623861585007319 14837398238435792377510979)
                  ·
                    refine ⟨22256097357653688566266469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14837398238435792377510979 22256097357653688566266469)
                    ·
                      refine ⟨4173018254560066606174963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22256097357653688566266469 4173018254560066606174963)
                      ·
                        rfl

theorem cell23_8126924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 3, 1, 1, 4].length) (baseStart_8126924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8126924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8126924 prefixEnd_8126924 := by exact prefixLift 8126924
  have htrace : WordTrace (prefixWord ++ tailWord_8126924) baseStart_8126924 baseEnd_8126924 := by
    simpa [prefixWord, tailWord_8126924, baseEnd_8126924] using wordTrace_append hprefix tailTrace_8126924
  have hstable : (prefixWord ++ tailWord_8126924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8126924).length < 2 ^ (prefixWord ++ tailWord_8126924).sum := by decide
  have hdescent : baseEnd_8126924 < baseStart_8126924 := by decide
  rcases family_descends (prefixWord ++ tailWord_8126924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8126934 : List Nat := [5, 2, 1, 1, 1, 1, 3, 1, 4, 4]
def baseStart_8126934 : Nat := 118140960795 + 8126934 * 2 ^ 59
def prefixEnd_8126934 : Nat := 4983230072969 + 3 ^ 40 * 8126934 * 2
def baseEnd_8126934 : Nat := 1391007796455537189016639

theorem tailTrace_8126934 : CollatzResearch.WordTrace tailWord_8126934 prefixEnd_8126934 1391007796455537189016639 := by
  unfold tailWord_8126934
  simp only [CollatzResearch.WordTrace]
  refine ⟨18525852146219597666899241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 197609089559675708446925237 18525852146219597666899241)
  ·
    refine ⟨13894389109664698250174431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18525852146219597666899241 13894389109664698250174431)
    ·
      refine ⟨20841583664497047375261647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13894389109664698250174431 20841583664497047375261647)
      ·
        refine ⟨31262375496745571062892471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20841583664497047375261647 31262375496745571062892471)
        ·
          refine ⟨46893563245118356594338707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31262375496745571062892471 46893563245118356594338707)
          ·
            refine ⟨70340344867677534891508061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46893563245118356594338707 70340344867677534891508061)
            ·
              refine ⟨26377629325379075584315523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70340344867677534891508061 26377629325379075584315523)
              ·
                refine ⟨39566443988068613376473285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26377629325379075584315523 39566443988068613376473285)
                ·
                  refine ⟨7418708247762865008088741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39566443988068613376473285 7418708247762865008088741)
                  ·
                    refine ⟨1391007796455537189016639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7418708247762865008088741 1391007796455537189016639)
                    ·
                      rfl

theorem cell23_8126934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 1, 4, 4].length) (baseStart_8126934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8126934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8126934 prefixEnd_8126934 := by exact prefixLift 8126934
  have htrace : WordTrace (prefixWord ++ tailWord_8126934) baseStart_8126934 baseEnd_8126934 := by
    simpa [prefixWord, tailWord_8126934, baseEnd_8126934] using wordTrace_append hprefix tailTrace_8126934
  have hstable : (prefixWord ++ tailWord_8126934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8126934).length < 2 ^ (prefixWord ++ tailWord_8126934).sum := by decide
  have hdescent : baseEnd_8126934 < baseStart_8126934 := by decide
  rcases family_descends (prefixWord ++ tailWord_8126934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8126941 : List Nat := [1, 4, 3, 1, 1, 1, 4, 1, 3, 2, 2]
def baseStart_8126941 : Nat := 118140960795 + 8126941 * 2 ^ 59
def prefixEnd_8126941 : Nat := 4983230072969 + 3 ^ 40 * 8126941 * 2
def baseEnd_8126941 : Nat := 4173026983731193039662385

theorem tailTrace_8126941 : CollatzResearch.WordTrace tailWord_8126941 prefixEnd_8126941 4173026983731193039662385 := by
  unfold tailWord_8126941
  simp only [CollatzResearch.WordTrace]
  refine ⟨296413889650488202865892677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197609259766992135243928451 296413889650488202865892677)
  ·
    refine ⟨55577604309466538037354877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 296413889650488202865892677 55577604309466538037354877)
    ·
      refine ⟨20841601616049951764008079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55577604309466538037354877 20841601616049951764008079)
      ·
        refine ⟨31262402424074927646012119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20841601616049951764008079 31262402424074927646012119)
        ·
          refine ⟨46893603636112391469018179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31262402424074927646012119 46893603636112391469018179)
          ·
            refine ⟨70340405454168587203527269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46893603636112391469018179 70340405454168587203527269)
            ·
              refine ⟨13188826022656610100661363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70340405454168587203527269 13188826022656610100661363)
              ·
                refine ⟨19783239033984915150992045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13188826022656610100661363 19783239033984915150992045)
                ·
                  refine ⟨7418714637744343181622017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19783239033984915150992045 7418714637744343181622017)
                  ·
                    refine ⟨5564035978308257386216513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7418714637744343181622017 5564035978308257386216513)
                    ·
                      refine ⟨4173026983731193039662385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5564035978308257386216513 4173026983731193039662385)
                      ·
                        rfl

theorem cell23_8126941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 4, 1, 3, 2, 2].length) (baseStart_8126941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8126941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8126941 prefixEnd_8126941 := by exact prefixLift 8126941
  have htrace : WordTrace (prefixWord ++ tailWord_8126941) baseStart_8126941 baseEnd_8126941 := by
    simpa [prefixWord, tailWord_8126941, baseEnd_8126941] using wordTrace_append hprefix tailTrace_8126941
  have hstable : (prefixWord ++ tailWord_8126941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8126941).length < 2 ^ (prefixWord ++ tailWord_8126941).sum := by decide
  have hdescent : baseEnd_8126941 < baseStart_8126941 := by decide
  rcases family_descends (prefixWord ++ tailWord_8126941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8126954 : List Nat := [3, 1, 3, 1, 3, 3, 1, 1, 1, 2, 4]
def baseStart_8126954 : Nat := 118140960795 + 8126954 * 2 ^ 59
def prefixEnd_8126954 : Nat := 4983230072969 + 3 ^ 40 * 8126954 * 2
def baseEnd_8126954 : Nat := 4173033658979701488799825

theorem tailTrace_8126954 : CollatzResearch.WordTrace tailWord_8126954 prefixEnd_8126954 4173033658979701488799825 := by
  unfold tailWord_8126954
  simp only [CollatzResearch.WordTrace]
  refine ⟨74103590949860276521528979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197609575866294070724077277 74103590949860276521528979)
  ·
    refine ⟨111155386424790414782293469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74103590949860276521528979 111155386424790414782293469)
    ·
      refine ⟨41683269909296405543360051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111155386424790414782293469 41683269909296405543360051)
      ·
        refine ⟨62524904863944608315040077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41683269909296405543360051 62524904863944608315040077)
        ·
          refine ⟨23446839323979228118140029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62524904863944608315040077 23446839323979228118140029)
          ·
            refine ⟨8792564746492210544302511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23446839323979228118140029 8792564746492210544302511)
            ·
              refine ⟨13188847119738315816453767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8792564746492210544302511 13188847119738315816453767)
              ·
                refine ⟨19783270679607473724680651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13188847119738315816453767 19783270679607473724680651)
                ·
                  refine ⟨29674906019411210587020977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19783270679607473724680651 29674906019411210587020977)
                  ·
                    refine ⟨22256179514558407940265733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29674906019411210587020977 22256179514558407940265733)
                    ·
                      refine ⟨4173033658979701488799825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22256179514558407940265733 4173033658979701488799825)
                      ·
                        rfl

theorem cell23_8126954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 1, 1, 1, 2, 4].length) (baseStart_8126954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8126954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8126954 prefixEnd_8126954 := by exact prefixLift 8126954
  have htrace : WordTrace (prefixWord ++ tailWord_8126954) baseStart_8126954 baseEnd_8126954 := by
    simpa [prefixWord, tailWord_8126954, baseEnd_8126954] using wordTrace_append hprefix tailTrace_8126954
  have hstable : (prefixWord ++ tailWord_8126954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8126954).length < 2 ^ (prefixWord ++ tailWord_8126954).sum := by decide
  have hdescent : baseEnd_8126954 < baseStart_8126954 := by decide
  rcases family_descends (prefixWord ++ tailWord_8126954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8126967 : List Nat := [1, 1, 3, 1, 1, 1, 1, 2, 7, 3, 2]
def baseStart_8126967 : Nat := 118140960795 + 8126967 * 2 ^ 59
def prefixEnd_8126967 : Nat := 4983230072969 + 3 ^ 40 * 8126967 * 2
def baseEnd_8126967 : Nat := 4173040334228209937937265

theorem tailTrace_8126967 : CollatzResearch.WordTrace tailWord_8126967 prefixEnd_8126967 4173040334228209937937265 := by
  unfold tailWord_8126967
  simp only [CollatzResearch.WordTrace]
  refine ⟨296414837948394009306339155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197609891965596006204226103 296414837948394009306339155)
  ·
    refine ⟨444622256922591013959508733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296414837948394009306339155 444622256922591013959508733)
    ·
      refine ⟨166733346345971630234815775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 444622256922591013959508733 166733346345971630234815775)
      ·
        refine ⟨250100019518957445352223663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166733346345971630234815775 250100019518957445352223663)
        ·
          refine ⟨375150029278436168028335495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250100019518957445352223663 375150029278436168028335495)
          ·
            refine ⟨562725043917654252042503243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 375150029278436168028335495 562725043917654252042503243)
            ·
              refine ⟨844087565876481378063754865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 562725043917654252042503243 844087565876481378063754865)
              ·
                refine ⟨633065674407361033547816149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 844087565876481378063754865 633065674407361033547816149)
                ·
                  refine ⟨14837476743922524223776941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 633065674407361033547816149 14837476743922524223776941)
                  ·
                    refine ⟨5564053778970946583916353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14837476743922524223776941 5564053778970946583916353)
                    ·
                      refine ⟨4173040334228209937937265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5564053778970946583916353 4173040334228209937937265)
                      ·
                        rfl

theorem cell23_8126967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 7, 3, 2].length) (baseStart_8126967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8126967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8126967 prefixEnd_8126967 := by exact prefixLift 8126967
  have htrace : WordTrace (prefixWord ++ tailWord_8126967) baseStart_8126967 baseEnd_8126967 := by
    simpa [prefixWord, tailWord_8126967, baseEnd_8126967] using wordTrace_append hprefix tailTrace_8126967
  have hstable : (prefixWord ++ tailWord_8126967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8126967).length < 2 ^ (prefixWord ++ tailWord_8126967).sum := by decide
  have hdescent : baseEnd_8126967 < baseStart_8126967 := by decide
  rcases family_descends (prefixWord ++ tailWord_8126967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8127018 : List Nat := [3, 1, 4, 1, 1, 4, 1, 2, 1, 3, 2]
def baseStart_8127018 : Nat := 118140960795 + 8127018 * 2 ^ 59
def prefixEnd_8127018 : Nat := 4983230072969 + 3 ^ 40 * 8127018 * 2
def baseEnd_8127018 : Nat := 4173066521741589238399531

theorem tailTrace_8127018 : CollatzResearch.WordTrace tailWord_8127018 prefixEnd_8127018 4173066521741589238399531 := by
  unfold tailWord_8127018
  simp only [CollatzResearch.WordTrace]
  refine ⟨74104174517802311254111427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197611132047472830010963805 74104174517802311254111427)
  ·
    refine ⟨111156261776703466881167141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74104174517802311254111427 111156261776703466881167141)
    ·
      refine ⟨20841799083131900040218839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 111156261776703466881167141 20841799083131900040218839)
      ·
        refine ⟨31262698624697850060328259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20841799083131900040218839 31262698624697850060328259)
        ·
          refine ⟨46894047937046775090492389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31262698624697850060328259 46894047937046775090492389)
          ·
            refine ⟨8792633988196270329467323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46894047937046775090492389 8792633988196270329467323)
            ·
              refine ⟨13188950982294405494200985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8792633988196270329467323 13188950982294405494200985)
              ·
                refine ⟨9891713236720804120650739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13188950982294405494200985 9891713236720804120650739)
                ·
                  refine ⟨14837569855081206180976109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9891713236720804120650739 14837569855081206180976109)
                  ·
                    refine ⟨5564088695655452317866041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14837569855081206180976109 5564088695655452317866041)
                    ·
                      refine ⟨4173066521741589238399531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5564088695655452317866041 4173066521741589238399531)
                      ·
                        rfl

theorem cell23_8127018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 1, 2, 1, 3, 2].length) (baseStart_8127018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8127018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8127018 prefixEnd_8127018 := by exact prefixLift 8127018
  have htrace : WordTrace (prefixWord ++ tailWord_8127018) baseStart_8127018 baseEnd_8127018 := by
    simpa [prefixWord, tailWord_8127018, baseEnd_8127018] using wordTrace_append hprefix tailTrace_8127018
  have hstable : (prefixWord ++ tailWord_8127018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8127018).length < 2 ^ (prefixWord ++ tailWord_8127018).sum := by decide
  have hdescent : baseEnd_8127018 < baseStart_8127018 := by decide
  rcases family_descends (prefixWord ++ tailWord_8127018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8127020 : List Nat := [2, 2, 1, 1, 1, 2, 1, 6, 7]
def baseStart_8127020 : Nat := 118140960795 + 8127020 * 2 ^ 59
def prefixEnd_8127020 : Nat := 4983230072969 + 3 ^ 40 * 8127020 * 2
def baseEnd_8127020 : Nat := 463674172078099803397169

theorem tailTrace_8127020 : CollatzResearch.WordTrace tailWord_8127020 prefixEnd_8127020 463674172078099803397169 := by
  unfold tailWord_8127020
  simp only [CollatzResearch.WordTrace]
  refine ⟨148208385508600999679009257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197611180678134666238679009 148208385508600999679009257)
  ·
    refine ⟨111156289131450749759256943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148208385508600999679009257 111156289131450749759256943)
    ·
      refine ⟨166734433697176124638885415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111156289131450749759256943 166734433697176124638885415)
      ·
        refine ⟨250101650545764186958328123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166734433697176124638885415 250101650545764186958328123)
        ·
          refine ⟨375152475818646280437492185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250101650545764186958328123 375152475818646280437492185)
          ·
            refine ⟨281364356863984710328119139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 375152475818646280437492185 281364356863984710328119139)
            ·
              refine ⟨422046535295977065492178709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 281364356863984710328119139 422046535295977065492178709)
              ·
                refine ⟨19783431341998924944945877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 422046535295977065492178709 19783431341998924944945877)
                ·
                  refine ⟨463674172078099803397169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19783431341998924944945877 463674172078099803397169)
                  ·
                    rfl

theorem cell23_8127020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 7].length) (baseStart_8127020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8127020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8127020 prefixEnd_8127020 := by exact prefixLift 8127020
  have htrace : WordTrace (prefixWord ++ tailWord_8127020) baseStart_8127020 baseEnd_8127020 := by
    simpa [prefixWord, tailWord_8127020, baseEnd_8127020] using wordTrace_append hprefix tailTrace_8127020
  have hstable : (prefixWord ++ tailWord_8127020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8127020).length < 2 ^ (prefixWord ++ tailWord_8127020).sum := by decide
  have hdescent : baseEnd_8127020 < baseStart_8127020 := by decide
  rcases family_descends (prefixWord ++ tailWord_8127020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8127104 : List Nat := [2, 1, 1, 2, 1, 5, 1, 2, 2, 4, 2]
def baseStart_8127104 : Nat := 118140960795 + 8127104 * 2 ^ 59
def prefixEnd_8127104 : Nat := 4983230072969 + 3 ^ 40 * 8127104 * 2
def baseEnd_8127104 : Nat := 4173110681077875901924135

theorem tailTrace_8127104 : CollatzResearch.WordTrace tailWord_8127104 prefixEnd_8127104 4173110681077875901924135 := by
  unfold tailWord_8127104
  simp only [CollatzResearch.WordTrace]
  refine ⟨148209917374448840852038183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197613223165931787802717577 148209917374448840852038183)
  ·
    refine ⟨222314876061673261278057275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148209917374448840852038183 222314876061673261278057275)
    ·
      refine ⟨333472314092509891917085913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222314876061673261278057275 333472314092509891917085913)
      ·
        refine ⟨250104235569382418937814435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 333472314092509891917085913 250104235569382418937814435)
        ·
          refine ⟨375156353354073628406721653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250104235569382418937814435 375156353354073628406721653)
          ·
            refine ⟨35170908126944402663130155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 375156353354073628406721653 35170908126944402663130155)
            ·
              refine ⟨52756362190416603994695233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35170908126944402663130155 52756362190416603994695233)
              ·
                refine ⟨39567271642812452996021425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52756362190416603994695233 39567271642812452996021425)
                ·
                  refine ⟨29675453732109339747016069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39567271642812452996021425 29675453732109339747016069)
                  ·
                    refine ⟨5564147574770501202565513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29675453732109339747016069 5564147574770501202565513)
                    ·
                      refine ⟨4173110681077875901924135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5564147574770501202565513 4173110681077875901924135)
                      ·
                        rfl

theorem cell23_8127104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 2, 2, 4, 2].length) (baseStart_8127104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8127104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8127104 prefixEnd_8127104 := by exact prefixLift 8127104
  have htrace : WordTrace (prefixWord ++ tailWord_8127104) baseStart_8127104 baseEnd_8127104 := by
    simpa [prefixWord, tailWord_8127104, baseEnd_8127104] using wordTrace_append hprefix tailTrace_8127104
  have hstable : (prefixWord ++ tailWord_8127104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8127104).length < 2 ^ (prefixWord ++ tailWord_8127104).sum := by decide
  have hdescent : baseEnd_8127104 < baseStart_8127104 := by decide
  rcases family_descends (prefixWord ++ tailWord_8127104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8127134 : List Nat := [4, 3, 1, 1, 1, 1, 1, 1, 2, 4, 4]
def baseStart_8127134 : Nat := 118140960795 + 8127134 * 2 ^ 59
def prefixEnd_8127134 : Nat := 4983230072969 + 3 ^ 40 * 8127134 * 2
def baseEnd_8127134 : Nat := 4173126085497510784548997

theorem tailTrace_8127134 : CollatzResearch.WordTrace tailWord_8127134 prefixEnd_8127134 4173126085497510784548997 := by
  unfold tailWord_8127134
  simp only [CollatzResearch.WordTrace]
  refine ⟨37052616117348624603458557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 197613952625859331218445637 37052616117348624603458557)
  ·
    refine ⟨13894731044005734226296959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37052616117348624603458557 13894731044005734226296959)
    ·
      refine ⟨20842096566008601339445439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13894731044005734226296959 20842096566008601339445439)
      ·
        refine ⟨31263144849012902009168159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20842096566008601339445439 31263144849012902009168159)
        ·
          refine ⟨46894717273519353013752239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31263144849012902009168159 46894717273519353013752239)
          ·
            refine ⟨70342075910279029520628359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46894717273519353013752239 70342075910279029520628359)
            ·
              refine ⟨105513113865418544280942539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70342075910279029520628359 105513113865418544280942539)
              ·
                refine ⟨158269670798127816421413809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105513113865418544280942539 158269670798127816421413809)
                ·
                  refine ⟨118702253098595862316060357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 158269670798127816421413809 118702253098595862316060357)
                  ·
                    refine ⟨22256672455986724184261317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 118702253098595862316060357 22256672455986724184261317)
                    ·
                      refine ⟨4173126085497510784548997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22256672455986724184261317 4173126085497510784548997)
                      ·
                        rfl

theorem cell23_8127134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 1, 2, 4, 4].length) (baseStart_8127134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8127134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8127134 prefixEnd_8127134 := by exact prefixLift 8127134
  have htrace : WordTrace (prefixWord ++ tailWord_8127134) baseStart_8127134 baseEnd_8127134 := by
    simpa [prefixWord, tailWord_8127134, baseEnd_8127134] using wordTrace_append hprefix tailTrace_8127134
  have hstable : (prefixWord ++ tailWord_8127134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8127134).length < 2 ^ (prefixWord ++ tailWord_8127134).sum := by decide
  have hdescent : baseEnd_8127134 < baseStart_8127134 := by decide
  rcases family_descends (prefixWord ++ tailWord_8127134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8127191 : List Nat := [1, 1, 3, 2, 1, 6, 1, 2, 1, 5]
def baseStart_8127191 : Nat := 118140960795 + 8127191 * 2 ^ 59
def prefixEnd_8127191 : Nat := 4983230072969 + 3 ^ 40 * 8127191 * 2
def baseEnd_8127191 : Nat := 1391051784631605687178745

theorem tailTrace_8127191 : CollatzResearch.WordTrace tailWord_8127191 prefixEnd_8127191 1391051784631605687178745 := by
  unfold tailWord_8127191
  simp only [CollatzResearch.WordTrace]
  refine ⟨296423007899582495562493427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197615338599721663708328951 296423007899582495562493427)
  ·
    refine ⟨444634511849373743343740141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296423007899582495562493427 444634511849373743343740141)
    ·
      refine ⟨166737941943515153753902553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 444634511849373743343740141 166737941943515153753902553)
      ·
        refine ⟨125053456457636365315426915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166737941943515153753902553 125053456457636365315426915)
        ·
          refine ⟨187580184686454547973140373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125053456457636365315426915 187580184686454547973140373)
          ·
            refine ⟨8792821157177556936240955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 187580184686454547973140373 8792821157177556936240955)
            ·
              refine ⟨13189231735766335404361433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8792821157177556936240955 13189231735766335404361433)
              ·
                refine ⟨9891923801824751553271075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13189231735766335404361433 9891923801824751553271075)
                ·
                  refine ⟨14837885702737127329906613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9891923801824751553271075 14837885702737127329906613)
                  ·
                    refine ⟨1391051784631605687178745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14837885702737127329906613 1391051784631605687178745)
                    ·
                      rfl

theorem cell23_8127191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 1, 2, 1, 5].length) (baseStart_8127191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8127191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8127191 prefixEnd_8127191 := by exact prefixLift 8127191
  have htrace : WordTrace (prefixWord ++ tailWord_8127191) baseStart_8127191 baseEnd_8127191 := by
    simpa [prefixWord, tailWord_8127191, baseEnd_8127191] using wordTrace_append hprefix tailTrace_8127191
  have hstable : (prefixWord ++ tailWord_8127191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8127191).length < 2 ^ (prefixWord ++ tailWord_8127191).sum := by decide
  have hdescent : baseEnd_8127191 < baseStart_8127191 := by decide
  rcases family_descends (prefixWord ++ tailWord_8127191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8127194 : List Nat := [3, 1, 1, 2, 2, 2, 3, 1, 3, 1, 4]
def baseStart_8127194 : Nat := 118140960795 + 8127194 * 2 ^ 59
def prefixEnd_8127194 : Nat := 4983230072969 + 3 ^ 40 * 8127194 * 2
def baseEnd_8127194 : Nat := 4173156894336780549798721

theorem tailTrace_8127194 : CollatzResearch.WordTrace tailWord_8127194 prefixEnd_8127194 4173156894336780549798721 := by
  unfold tailWord_8127194
  simp only [CollatzResearch.WordTrace]
  refine ⟨74105779329642906768713159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197615411545714418049901757 74105779329642906768713159)
  ·
    refine ⟨111158668994464360153069739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74105779329642906768713159 111158668994464360153069739)
    ·
      refine ⟨166738003491696540229604609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111158668994464360153069739 166738003491696540229604609)
      ·
        refine ⟨125053502618772405172203457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166738003491696540229604609 125053502618772405172203457)
        ·
          refine ⟨93790126964079303879152593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125053502618772405172203457 93790126964079303879152593)
          ·
            refine ⟨70342595223059477909364445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93790126964079303879152593 70342595223059477909364445)
            ·
              refine ⟨26378473208647304216011667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70342595223059477909364445 26378473208647304216011667)
              ·
                refine ⟨39567709812970956324017501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26378473208647304216011667 39567709812970956324017501)
                ·
                  refine ⟨14837891179864108621506563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39567709812970956324017501 14837891179864108621506563)
                  ·
                    refine ⟨22256836769796162932259845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14837891179864108621506563 22256836769796162932259845)
                    ·
                      refine ⟨4173156894336780549798721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22256836769796162932259845 4173156894336780549798721)
                      ·
                        rfl

theorem cell23_8127194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 1, 3, 1, 4].length) (baseStart_8127194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8127194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8127194 prefixEnd_8127194 := by exact prefixLift 8127194
  have htrace : WordTrace (prefixWord ++ tailWord_8127194) baseStart_8127194 baseEnd_8127194 := by
    simpa [prefixWord, tailWord_8127194, baseEnd_8127194] using wordTrace_append hprefix tailTrace_8127194
  have hstable : (prefixWord ++ tailWord_8127194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8127194).length < 2 ^ (prefixWord ++ tailWord_8127194).sum := by decide
  have hdescent : baseEnd_8127194 < baseStart_8127194 := by decide
  rcases family_descends (prefixWord ++ tailWord_8127194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8127204 : List Nat := [2, 3, 1, 1, 1, 5, 1, 2, 1, 6]
def baseStart_8127204 : Nat := 118140960795 + 8127204 * 2 ^ 59
def prefixEnd_8127204 : Nat := 4983230072969 + 3 ^ 40 * 8127204 * 2
def baseEnd_8127204 : Nat := 1391054009714441836891225

theorem tailTrace_8127204 : CollatzResearch.WordTrace tailWord_8127204 prefixEnd_8127204 1391054009714441836891225 := by
  unfold tailWord_8127204
  simp only [CollatzResearch.WordTrace]
  refine ⟨148211741024267699391358333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197615654699023599188477777 148211741024267699391358333)
  ·
    refine ⟨55579402884100387271759375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148211741024267699391358333 55579402884100387271759375)
    ·
      refine ⟨83369104326150580907639063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55579402884100387271759375 83369104326150580907639063)
      ·
        refine ⟨125053656489225871361458595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83369104326150580907639063 125053656489225871361458595)
        ·
          refine ⟨187580484733838807042187893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125053656489225871361458595 187580484733838807042187893)
          ·
            refine ⟨17585670443797388160205115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 187580484733838807042187893 17585670443797388160205115)
            ·
              refine ⟨26378505665696082240307673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17585670443797388160205115 26378505665696082240307673)
              ·
                refine ⟨19783879249272061680230755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26378505665696082240307673 19783879249272061680230755)
                ·
                  refine ⟨29675818873908092520346133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19783879249272061680230755 29675818873908092520346133)
                  ·
                    refine ⟨1391054009714441836891225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29675818873908092520346133 1391054009714441836891225)
                    ·
                      rfl

theorem cell23_8127204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 2, 1, 6].length) (baseStart_8127204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8127204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8127204 prefixEnd_8127204 := by exact prefixLift 8127204
  have htrace : WordTrace (prefixWord ++ tailWord_8127204) baseStart_8127204 baseEnd_8127204 := by
    simpa [prefixWord, tailWord_8127204, baseEnd_8127204] using wordTrace_append hprefix tailTrace_8127204
  have hstable : (prefixWord ++ tailWord_8127204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8127204).length < 2 ^ (prefixWord ++ tailWord_8127204).sum := by decide
  have hdescent : baseEnd_8127204 < baseStart_8127204 := by decide
  rcases family_descends (prefixWord ++ tailWord_8127204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8127208 : List Nat := [2, 1, 4, 1, 4, 1, 3, 1, 1, 5]
def baseStart_8127208 : Nat := 118140960795 + 8127208 * 2 ^ 59
def prefixEnd_8127208 : Nat := 4983230072969 + 3 ^ 40 * 8127208 * 2
def baseEnd_8127208 : Nat := 1391054694355314498341219

theorem tailTrace_8127208 : CollatzResearch.WordTrace tailWord_8127208 prefixEnd_8127208 1391054694355314498341219 := by
  unfold tailWord_8127208
  simp only [CollatzResearch.WordTrace]
  refine ⟨148211813970260453732931139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197615751960347271643908185 148211813970260453732931139)
  ·
    refine ⟨222317720955390680599396709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148211813970260453732931139 222317720955390680599396709)
    ·
      refine ⟨41684572679135752612386883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 222317720955390680599396709 41684572679135752612386883)
      ·
        refine ⟨62526859018703628918580325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41684572679135752612386883 62526859018703628918580325)
        ·
          refine ⟨11723786066006930422233811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62526859018703628918580325 11723786066006930422233811)
          ·
            refine ⟨17585679099010395633350717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11723786066006930422233811 17585679099010395633350717)
            ·
              refine ⟨6594629662128898362506519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17585679099010395633350717 6594629662128898362506519)
              ·
                refine ⟨9891944493193347543759779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6594629662128898362506519 9891944493193347543759779)
                ·
                  refine ⟨14837916739790021315639669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9891944493193347543759779 14837916739790021315639669)
                  ·
                    refine ⟨1391054694355314498341219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14837916739790021315639669 1391054694355314498341219)
                    ·
                      rfl

theorem cell23_8127208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 3, 1, 1, 5].length) (baseStart_8127208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8127208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8127208 prefixEnd_8127208 := by exact prefixLift 8127208
  have htrace : WordTrace (prefixWord ++ tailWord_8127208) baseStart_8127208 baseEnd_8127208 := by
    simpa [prefixWord, tailWord_8127208, baseEnd_8127208] using wordTrace_append hprefix tailTrace_8127208
  have hstable : (prefixWord ++ tailWord_8127208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8127208).length < 2 ^ (prefixWord ++ tailWord_8127208).sum := by decide
  have hdescent : baseEnd_8127208 < baseStart_8127208 := by decide
  rcases family_descends (prefixWord ++ tailWord_8127208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8127237 : List Nat := [1, 3, 1, 1, 2, 1, 1, 3, 2, 2, 6]
def baseStart_8127237 : Nat := 118140960795 + 8127237 * 2 ^ 59
def prefixEnd_8127237 : Nat := 4983230072969 + 3 ^ 40 * 8127237 * 2
def baseEnd_8127237 : Nat := 4173178974004923881561023

theorem tailTrace_8127237 : CollatzResearch.WordTrace tailWord_8127237 prefixEnd_8127237 4173178974004923881561023 := by
  unfold tailWord_8127237
  simp only [CollatzResearch.WordTrace]
  refine ⟨296424685657415845418667965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197616457104943896945778643 296424685657415845418667965)
  ·
    refine ⟨111159257121530942032000487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 296424685657415845418667965 111159257121530942032000487)
    ·
      refine ⟨166738885682296413048000731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111159257121530942032000487 166738885682296413048000731)
      ·
        refine ⟨250108328523444619572001097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166738885682296413048000731 250108328523444619572001097)
        ·
          refine ⟨187581246392583464679000823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 250108328523444619572001097 187581246392583464679000823)
          ·
            refine ⟨281371869588875197018501235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187581246392583464679000823 281371869588875197018501235)
            ·
              refine ⟨422057804383312795527751853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 281371869588875197018501235 422057804383312795527751853)
              ·
                refine ⟨158271676643742298322906945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 422057804383312795527751853 158271676643742298322906945)
                ·
                  refine ⟨118703757482806723742180209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 158271676643742298322906945 118703757482806723742180209)
                  ·
                    refine ⟨89027818112105042806635157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 118703757482806723742180209 89027818112105042806635157)
                    ·
                      refine ⟨4173178974004923881561023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 89027818112105042806635157 4173178974004923881561023)
                      ·
                        rfl

theorem cell23_8127237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 3, 2, 2, 6].length) (baseStart_8127237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8127237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8127237 prefixEnd_8127237 := by exact prefixLift 8127237
  have htrace : WordTrace (prefixWord ++ tailWord_8127237) baseStart_8127237 baseEnd_8127237 := by
    simpa [prefixWord, tailWord_8127237, baseEnd_8127237] using wordTrace_append hprefix tailTrace_8127237
  have hstable : (prefixWord ++ tailWord_8127237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8127237).length < 2 ^ (prefixWord ++ tailWord_8127237).sum := by decide
  have hdescent : baseEnd_8127237 < baseStart_8127237 := by decide
  rcases family_descends (prefixWord ++ tailWord_8127237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8127247 : List Nat := [1, 1, 2, 1, 1, 1, 5, 2, 2, 7]
def baseStart_8127247 : Nat := 118140960795 + 8127247 * 2 ^ 59
def prefixEnd_8127247 : Nat := 4983230072969 + 3 ^ 40 * 8127247 * 2
def baseEnd_8127247 : Nat := 1391061369603822947478659

theorem tailTrace_8127247 : CollatzResearch.WordTrace tailWord_8127247 prefixEnd_8127247 1391061369603822947478659 := by
  unfold tailWord_8127247
  simp only [CollatzResearch.WordTrace]
  refine ⟨296425050387379617126531995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197616700258253078084354663 296425050387379617126531995)
  ·
    refine ⟨444637575581069425689797993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296425050387379617126531995 444637575581069425689797993)
    ·
      refine ⟨333478181685802069267348495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 444637575581069425689797993 333478181685802069267348495)
      ·
        refine ⟨500217272528703103901022743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 333478181685802069267348495 500217272528703103901022743)
        ·
          refine ⟨750325908793054655851534115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 500217272528703103901022743 750325908793054655851534115)
          ·
            refine ⟨1125488863189581983777301173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 750325908793054655851534115 1125488863189581983777301173)
            ·
              refine ⟨105514580924023310979121985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1125488863189581983777301173 105514580924023310979121985)
              ·
                refine ⟨79135935693017483234341489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105514580924023310979121985 79135935693017483234341489)
                ·
                  refine ⟨59351951769763112425756117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79135935693017483234341489 59351951769763112425756117)
                  ·
                    refine ⟨1391061369603822947478659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59351951769763112425756117 1391061369603822947478659)
                    ·
                      rfl

theorem cell23_8127247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 2, 2, 7].length) (baseStart_8127247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8127247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8127247 prefixEnd_8127247 := by exact prefixLift 8127247
  have htrace : WordTrace (prefixWord ++ tailWord_8127247) baseStart_8127247 baseEnd_8127247 := by
    simpa [prefixWord, tailWord_8127247, baseEnd_8127247] using wordTrace_append hprefix tailTrace_8127247
  have hstable : (prefixWord ++ tailWord_8127247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8127247).length < 2 ^ (prefixWord ++ tailWord_8127247).sum := by decide
  have hdescent : baseEnd_8127247 < baseStart_8127247 := by decide
  rcases family_descends (prefixWord ++ tailWord_8127247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8127295 : List Nat := [1, 1, 2, 2, 5, 2, 3, 1, 2, 1, 3]
def baseStart_8127295 : Nat := 118140960795 + 8127295 * 2 ^ 59
def prefixEnd_8127295 : Nat := 4983230072969 + 3 ^ 40 * 8127295 * 2
def baseEnd_8127295 : Nat := 4173208755882884654635757

theorem tailTrace_8127295 : CollatzResearch.WordTrace tailWord_8127295 prefixEnd_8127295 4173208755882884654635757 := by
  unfold tailWord_8127295
  simp only [CollatzResearch.WordTrace]
  refine ⟨296426801091205721324279339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197617867394137147549519559 296426801091205721324279339)
  ·
    refine ⟨444640201636808581986419009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296426801091205721324279339 444640201636808581986419009)
    ·
      refine ⟨333480151227606436489814257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 444640201636808581986419009 333480151227606436489814257)
      ·
        refine ⟨250110113420704827367360693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 333480151227606436489814257 250110113420704827367360693)
        ·
          refine ⟨23447823133191077565690065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 250110113420704827367360693 23447823133191077565690065)
          ·
            refine ⟨17585867349893308174267549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23447823133191077565690065 17585867349893308174267549)
            ·
              refine ⟨6594700256209990565350331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17585867349893308174267549 6594700256209990565350331)
              ·
                refine ⟨9892050384314985848025497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6594700256209990565350331 9892050384314985848025497)
                ·
                  refine ⟨7419037788236239386019123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9892050384314985848025497 7419037788236239386019123)
                  ·
                    refine ⟨11128556682354359079028685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7419037788236239386019123 11128556682354359079028685)
                    ·
                      refine ⟨4173208755882884654635757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11128556682354359079028685 4173208755882884654635757)
                      ·
                        rfl

theorem cell23_8127295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 3, 1, 2, 1, 3].length) (baseStart_8127295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8127295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8127295 prefixEnd_8127295 := by exact prefixLift 8127295
  have htrace : WordTrace (prefixWord ++ tailWord_8127295) baseStart_8127295 baseEnd_8127295 := by
    simpa [prefixWord, tailWord_8127295, baseEnd_8127295] using wordTrace_append hprefix tailTrace_8127295
  have hstable : (prefixWord ++ tailWord_8127295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8127295).length < 2 ^ (prefixWord ++ tailWord_8127295).sum := by decide
  have hdescent : baseEnd_8127295 < baseStart_8127295 := by decide
  rcases family_descends (prefixWord ++ tailWord_8127295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8127301 : List Nat := [1, 3, 1, 1, 1, 2, 2, 5, 1, 4, 2]
def baseStart_8127301 : Nat := 118140960795 + 8127301 * 2 ^ 59
def prefixEnd_8127301 : Nat := 4983230072969 + 3 ^ 40 * 8127301 * 2
def baseEnd_8127301 : Nat := 4173211836766811631160729

theorem tailTrace_8127301 : CollatzResearch.WordTrace tailWord_8127301 prefixEnd_8127301 4173211836766811631160729 := by
  unfold tailWord_8127301
  simp only [CollatzResearch.WordTrace]
  refine ⟨296427019929183984348997757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197618013286122656232665171 296427019929183984348997757)
  ·
    refine ⟨111160132473443994130874159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 296427019929183984348997757 111160132473443994130874159)
    ·
      refine ⟨166740198710165991196311239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111160132473443994130874159 166740198710165991196311239)
      ·
        refine ⟨250110298065248986794466859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166740198710165991196311239 250110298065248986794466859)
        ·
          refine ⟨375165447097873480191700289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250110298065248986794466859 375165447097873480191700289)
          ·
            refine ⟨281374085323405110143775217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 375165447097873480191700289 281374085323405110143775217)
            ·
              refine ⟨211030563992553832607831413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 281374085323405110143775217 211030563992553832607831413)
              ·
                refine ⟨19784115374301921806984195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 211030563992553832607831413 19784115374301921806984195)
                ·
                  refine ⟨29676173061452882710476293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19784115374301921806984195 29676173061452882710476293)
                  ·
                    refine ⟨5564282449022415508214305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29676173061452882710476293 5564282449022415508214305)
                    ·
                      refine ⟨4173211836766811631160729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5564282449022415508214305 4173211836766811631160729)
                      ·
                        rfl

theorem cell23_8127301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 5, 1, 4, 2].length) (baseStart_8127301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8127301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8127301 prefixEnd_8127301 := by exact prefixLift 8127301
  have htrace : WordTrace (prefixWord ++ tailWord_8127301) baseStart_8127301 baseEnd_8127301 := by
    simpa [prefixWord, tailWord_8127301, baseEnd_8127301] using wordTrace_append hprefix tailTrace_8127301
  have hstable : (prefixWord ++ tailWord_8127301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8127301).length < 2 ^ (prefixWord ++ tailWord_8127301).sum := by decide
  have hdescent : baseEnd_8127301 < baseStart_8127301 := by decide
  rcases family_descends (prefixWord ++ tailWord_8127301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8127302 : List Nat := [6, 1, 1, 2, 3, 1, 2, 7]
def baseStart_8127302 : Nat := 118140960795 + 8127302 * 2 ^ 59
def prefixEnd_8127302 : Nat := 4983230072969 + 3 ^ 40 * 8127302 * 2
def baseEnd_8127302 : Nat := 154563420379535782490675

theorem tailTrace_8127302 : CollatzResearch.WordTrace tailWord_8127302 prefixEnd_8127302 154563420379535782490675 := by
  unfold tailWord_8127302
  simp only [CollatzResearch.WordTrace]
  refine ⟨9263345512568136297493255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 197618037601453574346522773 9263345512568136297493255)
  ·
    refine ⟨13895018268852204446239883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9263345512568136297493255 13895018268852204446239883)
    ·
      refine ⟨20842527403278306669359825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13895018268852204446239883 20842527403278306669359825)
      ·
        refine ⟨15631895552458730002019869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20842527403278306669359825 15631895552458730002019869)
        ·
          refine ⟨5861960832172023750757451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15631895552458730002019869 5861960832172023750757451)
          ·
            refine ⟨8792941248258035626136177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5861960832172023750757451 8792941248258035626136177)
            ·
              refine ⟨6594705936193526719602133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8792941248258035626136177 6594705936193526719602133)
              ·
                refine ⟨154563420379535782490675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6594705936193526719602133 154563420379535782490675)
                ·
                  rfl

theorem cell23_8127302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 2, 7].length) (baseStart_8127302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8127302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8127302 prefixEnd_8127302 := by exact prefixLift 8127302
  have htrace : WordTrace (prefixWord ++ tailWord_8127302) baseStart_8127302 baseEnd_8127302 := by
    simpa [prefixWord, tailWord_8127302, baseEnd_8127302] using wordTrace_append hprefix tailTrace_8127302
  have hstable : (prefixWord ++ tailWord_8127302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8127302).length < 2 ^ (prefixWord ++ tailWord_8127302).sum := by decide
  have hdescent : baseEnd_8127302 < baseStart_8127302 := by decide
  rcases family_descends (prefixWord ++ tailWord_8127302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8127304 : List Nat := [2, 1, 3, 1, 1, 3, 2, 2, 2, 1, 5]
def baseStart_8127304 : Nat := 118140960795 + 8127304 * 2 ^ 59
def prefixEnd_8127304 : Nat := 4983230072969 + 3 ^ 40 * 8127304 * 2
def baseEnd_8127304 : Nat := 4173213377208775119423215

theorem tailTrace_8127304 : CollatzResearch.WordTrace tailWord_8127304 prefixEnd_8127304 4173213377208775119423215 := by
  unfold tailWord_8127304
  simp only [CollatzResearch.WordTrace]
  refine ⟨148213564674086557930678483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197618086232115410574237977 148213564674086557930678483)
  ·
    refine ⟨222320347011129836896017725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148213564674086557930678483 222320347011129836896017725)
    ·
      refine ⟨83370130129173688836006647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 222320347011129836896017725 83370130129173688836006647)
      ·
        refine ⟨125055195193760533254009971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83370130129173688836006647 125055195193760533254009971)
        ·
          refine ⟨187582792790640799881014957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125055195193760533254009971 187582792790640799881014957)
          ·
            refine ⟨70343547296490299955380609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 187582792790640799881014957 70343547296490299955380609)
            ·
              refine ⟨52757660472367724966535457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70343547296490299955380609 52757660472367724966535457)
              ·
                refine ⟨39568245354275793724901593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52757660472367724966535457 39568245354275793724901593)
                ·
                  refine ⟨29676184015706845293676195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39568245354275793724901593 29676184015706845293676195)
                  ·
                    refine ⟨44514276023560267940514293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29676184015706845293676195 44514276023560267940514293)
                    ·
                      refine ⟨4173213377208775119423215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44514276023560267940514293 4173213377208775119423215)
                      ·
                        rfl

theorem cell23_8127304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 2, 2, 1, 5].length) (baseStart_8127304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8127304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8127304 prefixEnd_8127304 := by exact prefixLift 8127304
  have htrace : WordTrace (prefixWord ++ tailWord_8127304) baseStart_8127304 baseEnd_8127304 := by
    simpa [prefixWord, tailWord_8127304, baseEnd_8127304] using wordTrace_append hprefix tailTrace_8127304
  have hstable : (prefixWord ++ tailWord_8127304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8127304).length < 2 ^ (prefixWord ++ tailWord_8127304).sum := by decide
  have hdescent : baseEnd_8127304 < baseStart_8127304 := by decide
  rcases family_descends (prefixWord ++ tailWord_8127304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8127354 : List Nat := [3, 1, 1, 1, 1, 1, 3, 1, 6, 5]
def baseStart_8127354 : Nat := 118140960795 + 8127354 * 2 ^ 59
def prefixEnd_8127354 : Nat := 4983230072969 + 3 ^ 40 * 8127354 * 2
def baseEnd_8127354 : Nat := 1391079683747166641265995

theorem tailTrace_8127354 : CollatzResearch.WordTrace tailWord_8127354 prefixEnd_8127354 1391079683747166641265995 := by
  unfold tailWord_8127354
  simp only [CollatzResearch.WordTrace]
  refine ⟨74107238249497993600169279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197619301998661316267118077 74107238249497993600169279)
  ·
    refine ⟨111160857374246990400253919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74107238249497993600169279 111160857374246990400253919)
    ·
      refine ⟨166741286061370485600380879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111160857374246990400253919 166741286061370485600380879)
      ·
        refine ⟨250111929092055728400571319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166741286061370485600380879 250111929092055728400571319)
        ·
          refine ⟨375167893638083592600856979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250111929092055728400571319 375167893638083592600856979)
          ·
            refine ⟨562751840457125388901285469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 375167893638083592600856979 562751840457125388901285469)
            ·
              refine ⟨211031940171422020837982051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 562751840457125388901285469 211031940171422020837982051)
              ·
                refine ⟨316547910257133031256973077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 211031940171422020837982051 316547910257133031256973077)
                ·
                  refine ⟨14838183293303110840170613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 316547910257133031256973077 14838183293303110840170613)
                  ·
                    refine ⟨1391079683747166641265995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14838183293303110840170613 1391079683747166641265995)
                    ·
                      rfl

theorem cell23_8127354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 1, 6, 5].length) (baseStart_8127354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8127354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8127354 prefixEnd_8127354 := by exact prefixLift 8127354
  have htrace : WordTrace (prefixWord ++ tailWord_8127354) baseStart_8127354 baseEnd_8127354 := by
    simpa [prefixWord, tailWord_8127354, baseEnd_8127354] using wordTrace_append hprefix tailTrace_8127354
  have hstable : (prefixWord ++ tailWord_8127354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8127354).length < 2 ^ (prefixWord ++ tailWord_8127354).sum := by decide
  have hdescent : baseEnd_8127354 < baseStart_8127354 := by decide
  rcases family_descends (prefixWord ++ tailWord_8127354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8127364 : List Nat := [2, 3, 2, 1, 1, 1, 1, 1, 3, 1, 7]
def baseStart_8127364 : Nat := 118140960795 + 8127364 * 2 ^ 59
def prefixEnd_8127364 : Nat := 4983230072969 + 3 ^ 40 * 8127364 * 2
def baseEnd_8127364 : Nat := 4173244186048044884672939

theorem tailTrace_8127364 : CollatzResearch.WordTrace tailWord_8127364 prefixEnd_8127364 4173244186048044884672939 := by
  unfold tailWord_8127364
  simp only [CollatzResearch.WordTrace]
  refine ⟨148214658863977873054270573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197619545151970497405694097 148214658863977873054270573)
  ·
    refine ⟨55580497073991702395351465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148214658863977873054270573 55580497073991702395351465)
    ·
      refine ⟨41685372805493776796513599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55580497073991702395351465 41685372805493776796513599)
      ·
        refine ⟨62528059208240665194770399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41685372805493776796513599 62528059208240665194770399)
        ·
          refine ⟨93792088812360997792155599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62528059208240665194770399 93792088812360997792155599)
          ·
            refine ⟨140688133218541496688233399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93792088812360997792155599 140688133218541496688233399)
            ·
              refine ⟨211032199827812245032350099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140688133218541496688233399 211032199827812245032350099)
              ·
                refine ⟨316548299741718367548525149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 211032199827812245032350099 316548299741718367548525149)
                ·
                  refine ⟨118705612403144387830696931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 316548299741718367548525149 118705612403144387830696931)
                  ·
                    refine ⟨178058418604716581746045397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 118705612403144387830696931 178058418604716581746045397)
                    ·
                      refine ⟨4173244186048044884672939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 178058418604716581746045397 4173244186048044884672939)
                      ·
                        rfl

theorem cell23_8127364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 1, 3, 1, 7].length) (baseStart_8127364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8127364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8127364 prefixEnd_8127364 := by exact prefixLift 8127364
  have htrace : WordTrace (prefixWord ++ tailWord_8127364) baseStart_8127364 baseEnd_8127364 := by
    simpa [prefixWord, tailWord_8127364, baseEnd_8127364] using wordTrace_append hprefix tailTrace_8127364
  have hstable : (prefixWord ++ tailWord_8127364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8127364).length < 2 ^ (prefixWord ++ tailWord_8127364).sum := by decide
  have hdescent : baseEnd_8127364 < baseStart_8127364 := by decide
  rcases family_descends (prefixWord ++ tailWord_8127364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8127401 : List Nat := [1, 2, 1, 1, 1, 1, 6, 3, 3, 4]
def baseStart_8127401 : Nat := 118140960795 + 8127401 * 2 ^ 59
def prefixEnd_8127401 : Nat := 4983230072969 + 3 ^ 40 * 8127401 * 2
def baseEnd_8127401 : Nat := 1391087728277420413303423

theorem tailTrace_8127401 : CollatzResearch.WordTrace tailWord_8127401 prefixEnd_8127401 1391087728277420413303423 := by
  unfold tailWord_8127401
  simp only [CollatzResearch.WordTrace]
  refine ⟨296430667228821701427638057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197620444819214467618425371 296430667228821701427638057)
  ·
    refine ⟨222323000421616276070728543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296430667228821701427638057 222323000421616276070728543)
    ·
      refine ⟨333484500632424414106092815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222323000421616276070728543 333484500632424414106092815)
      ·
        refine ⟨500226750948636621159139223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 333484500632424414106092815 500226750948636621159139223)
        ·
          refine ⟨750340126422954931738708835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 500226750948636621159139223 750340126422954931738708835)
          ·
            refine ⟨1125510189634432397608063253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 750340126422954931738708835 1125510189634432397608063253)
            ·
              refine ⟨52758290139114018637877965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1125510189634432397608063253 52758290139114018637877965)
              ·
                refine ⟨19784358802167756989204237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52758290139114018637877965 19784358802167756989204237)
                ·
                  refine ⟨7419134550812908870951589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19784358802167756989204237 7419134550812908870951589)
                  ·
                    refine ⟨1391087728277420413303423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7419134550812908870951589 1391087728277420413303423)
                    ·
                      rfl

theorem cell23_8127401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 3, 3, 4].length) (baseStart_8127401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8127401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8127401 prefixEnd_8127401 := by exact prefixLift 8127401
  have htrace : WordTrace (prefixWord ++ tailWord_8127401) baseStart_8127401 baseEnd_8127401 := by
    simpa [prefixWord, tailWord_8127401, baseEnd_8127401] using wordTrace_append hprefix tailTrace_8127401
  have hstable : (prefixWord ++ tailWord_8127401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8127401).length < 2 ^ (prefixWord ++ tailWord_8127401).sum := by decide
  have hdescent : baseEnd_8127401 < baseStart_8127401 := by decide
  rcases family_descends (prefixWord ++ tailWord_8127401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8127404 : List Nat := [2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 6]
def baseStart_8127404 : Nat := 118140960795 + 8127404 * 2 ^ 59
def prefixEnd_8127404 : Nat := 4983230072969 + 3 ^ 40 * 8127404 * 2
def baseEnd_8127404 : Nat := 4173264725274224728172755

theorem tailTrace_8127404 : CollatzResearch.WordTrace tailWord_8127404 prefixEnd_8127404 4173264725274224728172755 := by
  unfold tailWord_8127404
  simp only [CollatzResearch.WordTrace]
  refine ⟨148215388323905416469998633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197620517765207221959998177 148215388323905416469998633)
  ·
    refine ⟨111161541242929062352498975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148215388323905416469998633 111161541242929062352498975)
    ·
      refine ⟨166742311864393593528748463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111161541242929062352498975 166742311864393593528748463)
      ·
        refine ⟨250113467796590390293122695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166742311864393593528748463 250113467796590390293122695)
        ·
          refine ⟨375170201694885585439684043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250113467796590390293122695 375170201694885585439684043)
          ·
            refine ⟨562755302542328378159526065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 375170201694885585439684043 562755302542328378159526065)
            ·
              refine ⟨422066476906746283619644549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 562755302542328378159526065 422066476906746283619644549)
              ·
                refine ⟨79137464420014928178683353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 422066476906746283619644549 79137464420014928178683353)
                ·
                  refine ⟨59353098315011196134012515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79137464420014928178683353 59353098315011196134012515)
                  ·
                    refine ⟨89029647472516794201018773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59353098315011196134012515 89029647472516794201018773)
                    ·
                      refine ⟨4173264725274224728172755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 89029647472516794201018773 4173264725274224728172755)
                      ·
                        rfl

theorem cell23_8127404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 6].length) (baseStart_8127404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8127404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8127404 prefixEnd_8127404 := by exact prefixLift 8127404
  have htrace : WordTrace (prefixWord ++ tailWord_8127404) baseStart_8127404 baseEnd_8127404 := by
    simpa [prefixWord, tailWord_8127404, baseEnd_8127404] using wordTrace_append hprefix tailTrace_8127404
  have hstable : (prefixWord ++ tailWord_8127404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8127404).length < 2 ^ (prefixWord ++ tailWord_8127404).sum := by decide
  have hdescent : baseEnd_8127404 < baseStart_8127404 := by decide
  rcases family_descends (prefixWord ++ tailWord_8127404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8127435 : List Nat := [1, 1, 1, 1, 3, 6, 2, 3, 1, 4]
def baseStart_8127435 : Nat := 118140960795 + 8127435 * 2 ^ 59
def prefixEnd_8127435 : Nat := 4983230072969 + 3 ^ 40 * 8127435 * 2
def baseEnd_8127435 : Nat := 1391093547724838035628371

theorem tailTrace_8127435 : CollatzResearch.WordTrace tailWord_8127435 prefixEnd_8127435 1391093547724838035628371 := by
  unfold tailWord_8127435
  simp only [CollatzResearch.WordTrace]
  refine ⟨296431907310698525234375759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197621271540465683489583839 296431907310698525234375759)
  ·
    refine ⟨444647860966047787851563639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296431907310698525234375759 444647860966047787851563639)
    ·
      refine ⟨666971791449071681777345459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 444647860966047787851563639 666971791449071681777345459)
      ·
        refine ⟨1000457687173607522666018189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 666971791449071681777345459 1000457687173607522666018189)
        ·
          refine ⟨375171632690102820999756821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1000457687173607522666018189 375171632690102820999756821)
          ·
            refine ⟨17586170282348569734363601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 375171632690102820999756821 17586170282348569734363601)
            ·
              refine ⟨13189627711761427300772701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17586170282348569734363601 13189627711761427300772701)
              ·
                refine ⟨4946110391910535237789763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13189627711761427300772701 4946110391910535237789763)
                ·
                  refine ⟨7419165587865802856684645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4946110391910535237789763 7419165587865802856684645)
                  ·
                    refine ⟨1391093547724838035628371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7419165587865802856684645 1391093547724838035628371)
                    ·
                      rfl

theorem cell23_8127435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 2, 3, 1, 4].length) (baseStart_8127435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8127435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8127435 prefixEnd_8127435 := by exact prefixLift 8127435
  have htrace : WordTrace (prefixWord ++ tailWord_8127435) baseStart_8127435 baseEnd_8127435 := by
    simpa [prefixWord, tailWord_8127435, baseEnd_8127435] using wordTrace_append hprefix tailTrace_8127435
  have hstable : (prefixWord ++ tailWord_8127435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8127435).length < 2 ^ (prefixWord ++ tailWord_8127435).sum := by decide
  have hdescent : baseEnd_8127435 < baseStart_8127435 := by decide
  rcases family_descends (prefixWord ++ tailWord_8127435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8127448 : List Nat := [2, 1, 2, 2, 2, 5, 1, 2, 6]
def baseStart_8127448 : Nat := 118140960795 + 8127448 * 2 ^ 59
def prefixEnd_8127448 : Nat := 4983230072969 + 3 ^ 40 * 8127448 * 2
def baseEnd_8127448 : Nat := 463698590935891395113617

theorem tailTrace_8127448 : CollatzResearch.WordTrace tailWord_8127448 prefixEnd_8127448 463698590935891395113617 := by
  unfold tailWord_8127448
  simp only [CollatzResearch.WordTrace]
  refine ⟨148216190729825714227299499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197621587639767618969732665 148216190729825714227299499)
  ·
    refine ⟨222324286094738571340949249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148216190729825714227299499 222324286094738571340949249)
    ·
      refine ⟨166743214571053928505711937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222324286094738571340949249 166743214571053928505711937)
      ·
        refine ⟨125057410928290446379283953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166743214571053928505711937 125057410928290446379283953)
        ·
          refine ⟨93793058196217834784462965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125057410928290446379283953 93793058196217834784462965)
          ·
            refine ⟨8793099205895422011043403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 93793058196217834784462965 8793099205895422011043403)
            ·
              refine ⟨13189648808843133016565105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8793099205895422011043403 13189648808843133016565105)
              ·
                refine ⟨9892236606632349762423829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13189648808843133016565105 9892236606632349762423829)
                ·
                  refine ⟨463698590935891395113617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9892236606632349762423829 463698590935891395113617)
                  ·
                    rfl

theorem cell23_8127448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 1, 2, 6].length) (baseStart_8127448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8127448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8127448 prefixEnd_8127448 := by exact prefixLift 8127448
  have htrace : WordTrace (prefixWord ++ tailWord_8127448) baseStart_8127448 baseEnd_8127448 := by
    simpa [prefixWord, tailWord_8127448, baseEnd_8127448] using wordTrace_append hprefix tailTrace_8127448
  have hstable : (prefixWord ++ tailWord_8127448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8127448).length < 2 ^ (prefixWord ++ tailWord_8127448).sum := by decide
  have hdescent : baseEnd_8127448 < baseStart_8127448 := by decide
  rcases family_descends (prefixWord ++ tailWord_8127448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8127486 : List Nat := [4, 2, 2, 2, 3, 1, 1, 3, 1, 4]
def baseStart_8127486 : Nat := 118140960795 + 8127486 * 2 ^ 59
def prefixEnd_8127486 : Nat := 4983230072969 + 3 ^ 40 * 8127486 * 2
def baseEnd_8127486 : Nat := 1391102276895964469115793

theorem tailTrace_8127486 : CollatzResearch.WordTrace tailWord_8127486 prefixEnd_8127486 1391102276895964469115793 := by
  unfold tailWord_8127486
  simp only [CollatzResearch.WordTrace]
  refine ⟨37054220929189220118060289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 197622511622342507296321541 37054220929189220118060289)
  ·
    refine ⟨27790665696891915088545217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37054220929189220118060289 27790665696891915088545217)
    ·
      refine ⟨20842999272668936316408913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27790665696891915088545217 20842999272668936316408913)
      ·
        refine ⟨15632249454501702237306685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20842999272668936316408913 15632249454501702237306685)
        ·
          refine ⟨5862093545438138338990007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15632249454501702237306685 5862093545438138338990007)
          ·
            refine ⟨8793140318157207508485011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5862093545438138338990007 8793140318157207508485011)
            ·
              refine ⟨13189710477235811262727517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8793140318157207508485011 13189710477235811262727517)
              ·
                refine ⟨4946141428963429223522819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13189710477235811262727517 4946141428963429223522819)
                ·
                  refine ⟨7419212143445143835284229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4946141428963429223522819 7419212143445143835284229)
                  ·
                    refine ⟨1391102276895964469115793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7419212143445143835284229 1391102276895964469115793)
                    ·
                      rfl

theorem cell23_8127486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 1, 3, 1, 4].length) (baseStart_8127486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8127486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8127486 prefixEnd_8127486 := by exact prefixLift 8127486
  have htrace : WordTrace (prefixWord ++ tailWord_8127486) baseStart_8127486 baseEnd_8127486 := by
    simpa [prefixWord, tailWord_8127486, baseEnd_8127486] using wordTrace_append hprefix tailTrace_8127486
  have hstable : (prefixWord ++ tailWord_8127486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8127486).length < 2 ^ (prefixWord ++ tailWord_8127486).sum := by decide
  have hdescent : baseEnd_8127486 < baseStart_8127486 := by decide
  rcases family_descends (prefixWord ++ tailWord_8127486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8127509 : List Nat := [1, 3, 2, 1, 4, 2, 3, 2, 1, 1, 3]
def baseStart_8127509 : Nat := 118140960795 + 8127509 * 2 ^ 59
def prefixEnd_8127509 : Nat := 4983230072969 + 3 ^ 40 * 8127509 * 2
def baseEnd_8127509 : Nat := 4173318640742946817359773

theorem tailTrace_8127509 : CollatzResearch.WordTrace tailWord_8127509 prefixEnd_8127509 4173318640742946817359773 := by
  unfold tailWord_8127509
  simp only [CollatzResearch.WordTrace]
  refine ⟨296434606312430435872569581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197623070874953623915046387 296434606312430435872569581)
  ·
    refine ⟨111162977367161413452213593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 296434606312430435872569581 111162977367161413452213593)
    ·
      refine ⟨83372233025371060089160195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111162977367161413452213593 83372233025371060089160195)
      ·
        refine ⟨125058349538056590133740293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83372233025371060089160195 125058349538056590133740293)
        ·
          refine ⟨23448440538385610650076305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 125058349538056590133740293 23448440538385610650076305)
          ·
            refine ⟨17586330403789207987557229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23448440538385610650076305 17586330403789207987557229)
            ·
              refine ⟨6594873901420952995333961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17586330403789207987557229 6594873901420952995333961)
              ·
                refine ⟨4946155426065714746500471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6594873901420952995333961 4946155426065714746500471)
                ·
                  refine ⟨7419233139098572119750707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4946155426065714746500471 7419233139098572119750707)
                  ·
                    refine ⟨11128849708647858179626061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7419233139098572119750707 11128849708647858179626061)
                    ·
                      refine ⟨4173318640742946817359773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11128849708647858179626061 4173318640742946817359773)
                      ·
                        rfl

theorem cell23_8127509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 3, 2, 1, 1, 3].length) (baseStart_8127509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8127509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8127509 prefixEnd_8127509 := by exact prefixLift 8127509
  have htrace : WordTrace (prefixWord ++ tailWord_8127509) baseStart_8127509 baseEnd_8127509 := by
    simpa [prefixWord, tailWord_8127509, baseEnd_8127509] using wordTrace_append hprefix tailTrace_8127509
  have hstable : (prefixWord ++ tailWord_8127509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8127509).length < 2 ^ (prefixWord ++ tailWord_8127509).sum := by decide
  have hdescent : baseEnd_8127509 < baseStart_8127509 := by decide
  rcases family_descends (prefixWord ++ tailWord_8127509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8127521 : List Nat := [1, 2, 3, 2, 3, 1, 1, 10]
def baseStart_8127521 : Nat := 118140960795 + 8127521 * 2 ^ 59
def prefixEnd_8127521 : Nat := 4983230072969 + 3 ^ 40 * 8127521 * 2
def baseEnd_8127521 : Nat := 154567585278177806311471

theorem tailTrace_8127521 : CollatzResearch.WordTrace tailWord_8127521 prefixEnd_8127521 154567585278177806311471 := by
  unfold tailWord_8127521
  simp only [CollatzResearch.WordTrace]
  refine ⟨296435043988386961922006417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197623362658924641281337611 296435043988386961922006417)
  ·
    refine ⟨222326282991290221441504813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296435043988386961922006417 222326282991290221441504813)
    ·
      refine ⟨83372356121733833040564305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 222326282991290221441504813 83372356121733833040564305)
      ·
        refine ⟨62529267091300374780423229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83372356121733833040564305 62529267091300374780423229)
        ·
          refine ⟨23448475159237640542658711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62529267091300374780423229 23448475159237640542658711)
          ·
            refine ⟨35172712738856460813988067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23448475159237640542658711 35172712738856460813988067)
            ·
              refine ⟨52759069108284691220982101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35172712738856460813988067 52759069108284691220982101)
              ·
                refine ⟨154567585278177806311471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 52759069108284691220982101 154567585278177806311471)
                ·
                  rfl

theorem cell23_8127521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 10].length) (baseStart_8127521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8127521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8127521 prefixEnd_8127521 := by exact prefixLift 8127521
  have htrace : WordTrace (prefixWord ++ tailWord_8127521) baseStart_8127521 baseEnd_8127521 := by
    simpa [prefixWord, tailWord_8127521, baseEnd_8127521] using wordTrace_append hprefix tailTrace_8127521
  have hstable : (prefixWord ++ tailWord_8127521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8127521).length < 2 ^ (prefixWord ++ tailWord_8127521).sum := by decide
  have hdescent : baseEnd_8127521 < baseStart_8127521 := by decide
  rcases family_descends (prefixWord ++ tailWord_8127521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8127548 : List Nat := [2, 2, 2, 2, 2, 2, 1, 1, 3, 3, 3]
def baseStart_8127548 : Nat := 118140960795 + 8127548 * 2 ^ 59
def prefixEnd_8127548 : Nat := 4983230072969 + 3 ^ 40 * 8127548 * 2
def baseEnd_8127548 : Nat := 4173338666488472164772093

theorem tailTrace_8127548 : CollatzResearch.WordTrace tailWord_8127548 prefixEnd_8127548 4173338666488472164772093 := by
  unfold tailWord_8127548
  simp only [CollatzResearch.WordTrace]
  refine ⟨148218014379644572766619649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197624019172859430355492865 148218014379644572766619649)
  ·
    refine ⟨111163510784733429574964737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148218014379644572766619649 111163510784733429574964737)
    ·
      refine ⟨83372633088550072181223553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111163510784733429574964737 83372633088550072181223553)
      ·
        refine ⟨62529474816412554135917665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83372633088550072181223553 62529474816412554135917665)
        ·
          refine ⟨46897106112309415601938249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62529474816412554135917665 46897106112309415601938249)
          ·
            refine ⟨35172829584232061701453687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46897106112309415601938249 35172829584232061701453687)
            ·
              refine ⟨52759244376348092552180531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35172829584232061701453687 52759244376348092552180531)
              ·
                refine ⟨79138866564522138828270797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52759244376348092552180531 79138866564522138828270797)
                ·
                  refine ⟨29677074961695802060601549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79138866564522138828270797 29677074961695802060601549)
                  ·
                    refine ⟨11128903110635925772725581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29677074961695802060601549 11128903110635925772725581)
                    ·
                      refine ⟨4173338666488472164772093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11128903110635925772725581 4173338666488472164772093)
                      ·
                        rfl

theorem cell23_8127548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 1, 3, 3, 3].length) (baseStart_8127548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8127548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8127548 prefixEnd_8127548 := by exact prefixLift 8127548
  have htrace : WordTrace (prefixWord ++ tailWord_8127548) baseStart_8127548 baseEnd_8127548 := by
    simpa [prefixWord, tailWord_8127548, baseEnd_8127548] using wordTrace_append hprefix tailTrace_8127548
  have hstable : (prefixWord ++ tailWord_8127548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8127548).length < 2 ^ (prefixWord ++ tailWord_8127548).sum := by decide
  have hdescent : baseEnd_8127548 < baseStart_8127548 := by decide
  rcases family_descends (prefixWord ++ tailWord_8127548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8127571 : List Nat := [1, 1, 1, 2, 1, 1, 2, 5, 2, 3, 4]
def baseStart_8127571 : Nat := 118140960795 + 8127571 * 2 ^ 59
def prefixEnd_8127571 : Nat := 4983230072969 + 3 ^ 40 * 8127571 * 2
def baseEnd_8127571 : Nat := 4173350476543525574784487

theorem tailTrace_8127571 : CollatzResearch.WordTrace tailWord_8127571 prefixEnd_8127571 4173350476543525574784487 := by
  unfold tailWord_8127571
  simp only [CollatzResearch.WordTrace]
  refine ⟨296436867638205820461326567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197624578425470546974217711 296436867638205820461326567)
  ·
    refine ⟨444655301457308730691989851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296436867638205820461326567 444655301457308730691989851)
    ·
      refine ⟨666982952185963096037984777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 444655301457308730691989851 666982952185963096037984777)
      ·
        refine ⟨500237214139472322028488583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 666982952185963096037984777 500237214139472322028488583)
        ·
          refine ⟨750355821209208483042732875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 500237214139472322028488583 750355821209208483042732875)
          ·
            refine ⟨1125533731813812724564099313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 750355821209208483042732875 1125533731813812724564099313)
            ·
              refine ⟨844150298860359543423074485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1125533731813812724564099313 844150298860359543423074485)
              ·
                refine ⟨79139090518158707195913233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 844150298860359543423074485 79139090518158707195913233)
                ·
                  refine ⟨59354317888619030396934925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79139090518158707195913233 59354317888619030396934925)
                  ·
                    refine ⟨22257869208232136398850597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59354317888619030396934925 22257869208232136398850597)
                    ·
                      refine ⟨4173350476543525574784487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22257869208232136398850597 4173350476543525574784487)
                      ·
                        rfl

theorem cell23_8127571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 5, 2, 3, 4].length) (baseStart_8127571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8127571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8127571 prefixEnd_8127571 := by exact prefixLift 8127571
  have htrace : WordTrace (prefixWord ++ tailWord_8127571) baseStart_8127571 baseEnd_8127571 := by
    simpa [prefixWord, tailWord_8127571, baseEnd_8127571] using wordTrace_append hprefix tailTrace_8127571
  have hstable : (prefixWord ++ tailWord_8127571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8127571).length < 2 ^ (prefixWord ++ tailWord_8127571).sum := by decide
  have hdescent : baseEnd_8127571 < baseStart_8127571 := by decide
  rcases family_descends (prefixWord ++ tailWord_8127571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8127738 : List Nat := [3, 1, 1, 1, 1, 4, 2, 1, 1, 2, 6]
def baseStart_8127738 : Nat := 118140960795 + 8127738 * 2 ^ 59
def prefixEnd_8127738 : Nat := 4983230072969 + 3 ^ 40 * 8127738 * 2
def baseEnd_8127738 : Nat := 4173436227812826421396219

theorem tailTrace_8127738 : CollatzResearch.WordTrace tailWord_8127738 prefixEnd_8127738 4173436227812826421396219 := by
  unfold tailWord_8127738
  simp only [CollatzResearch.WordTrace]
  refine ⟨74110739657150201995663967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197628639085733871988437245 74110739657150201995663967)
  ·
    refine ⟨111166109485725302993495951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74110739657150201995663967 111166109485725302993495951)
    ·
      refine ⟨166749164228587954490243927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111166109485725302993495951 166749164228587954490243927)
      ·
        refine ⟨250123746342881931735365891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166749164228587954490243927 250123746342881931735365891)
        ·
          refine ⟨375185619514322897603048837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250123746342881931735365891 375185619514322897603048837)
          ·
            refine ⟨70347303658935543300571657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 375185619514322897603048837 70347303658935543300571657)
            ·
              refine ⟨52760477744201657475428743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70347303658935543300571657 52760477744201657475428743)
              ·
                refine ⟨79140716616302486213143115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52760477744201657475428743 79140716616302486213143115)
                ·
                  refine ⟨118711074924453729319714673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79140716616302486213143115 118711074924453729319714673)
                  ·
                    refine ⟨89033306193340296989786005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 118711074924453729319714673 89033306193340296989786005)
                    ·
                      refine ⟨4173436227812826421396219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 89033306193340296989786005 4173436227812826421396219)
                      ·
                        rfl

theorem cell23_8127738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 1, 1, 2, 6].length) (baseStart_8127738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8127738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8127738 prefixEnd_8127738 := by exact prefixLift 8127738
  have htrace : WordTrace (prefixWord ++ tailWord_8127738) baseStart_8127738 baseEnd_8127738 := by
    simpa [prefixWord, tailWord_8127738, baseEnd_8127738] using wordTrace_append hprefix tailTrace_8127738
  have hstable : (prefixWord ++ tailWord_8127738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8127738).length < 2 ^ (prefixWord ++ tailWord_8127738).sum := by decide
  have hdescent : baseEnd_8127738 < baseStart_8127738 := by decide
  rcases family_descends (prefixWord ++ tailWord_8127738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8127765 : List Nat := [1, 3, 2, 1, 2, 1, 1, 6, 1, 5]
def baseStart_8127765 : Nat := 118140960795 + 8127765 * 2 ^ 59
def prefixEnd_8127765 : Nat := 4983230072969 + 3 ^ 40 * 8127765 * 2
def baseEnd_8127765 : Nat := 1391150030596832605252865

theorem tailTrace_8127765 : CollatzResearch.WordTrace tailWord_8127765 prefixEnd_8127765 1391150030596832605252865 := by
  unfold tailWord_8127765
  simp only [CollatzResearch.WordTrace]
  refine ⟨296443943399502991593888749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197629295599668661062592499 296443943399502991593888749)
  ·
    refine ⟨111166478774813621847708281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 296443943399502991593888749 111166478774813621847708281)
    ·
      refine ⟨83374859081110216385781211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111166478774813621847708281 83374859081110216385781211)
      ·
        refine ⟨125062288621665324578671817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83374859081110216385781211 125062288621665324578671817)
        ·
          refine ⟨93796716466248993434003863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125062288621665324578671817 93796716466248993434003863)
          ·
            refine ⟨140695074699373490151005795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93796716466248993434003863 140695074699373490151005795)
            ·
              refine ⟨211042612049060235226508693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140695074699373490151005795 211042612049060235226508693)
              ·
                refine ⟨9892622439799698526242595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 211042612049060235226508693 9892622439799698526242595)
                ·
                  refine ⟨14838933659699547789363893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9892622439799698526242595 14838933659699547789363893)
                  ·
                    refine ⟨1391150030596832605252865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14838933659699547789363893 1391150030596832605252865)
                    ·
                      rfl

theorem cell23_8127765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 6, 1, 5].length) (baseStart_8127765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8127765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8127765 prefixEnd_8127765 := by exact prefixLift 8127765
  have htrace : WordTrace (prefixWord ++ tailWord_8127765) baseStart_8127765 baseEnd_8127765 := by
    simpa [prefixWord, tailWord_8127765, baseEnd_8127765] using wordTrace_append hprefix tailTrace_8127765
  have hstable : (prefixWord ++ tailWord_8127765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8127765).length < 2 ^ (prefixWord ++ tailWord_8127765).sum := by decide
  have hdescent : baseEnd_8127765 < baseStart_8127765 := by decide
  rcases family_descends (prefixWord ++ tailWord_8127765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8127779 : List Nat := [1, 1, 1, 4, 2, 3, 1, 5, 1, 1, 3]
def baseStart_8127779 : Nat := 118140960795 + 8127779 * 2 ^ 59
def prefixEnd_8127779 : Nat := 4983230072969 + 3 ^ 40 * 8127779 * 2
def baseEnd_8127779 : Nat := 4173457280519660760983531

theorem tailTrace_8127779 : CollatzResearch.WordTrace tailWord_8127779 prefixEnd_8127779 4173457280519660760983531 := by
  unfold tailWord_8127779
  simp only [CollatzResearch.WordTrace]
  refine ⟨296444454021452271984898391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197629636014301514656598927 296444454021452271984898391)
  ·
    refine ⟨444666681032178407977347587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296444454021452271984898391 444666681032178407977347587)
    ·
      refine ⟨667000021548267611966021381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 444666681032178407977347587 667000021548267611966021381)
      ·
        refine ⟨125062504040300177243629009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 667000021548267611966021381 125062504040300177243629009)
        ·
          refine ⟨93796878030225132932721757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125062504040300177243629009 93796878030225132932721757)
          ·
            refine ⟨35173829261334424849770659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93796878030225132932721757 35173829261334424849770659)
            ·
              refine ⟨52760743892001637274655989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35173829261334424849770659 52760743892001637274655989)
              ·
                refine ⟨4946319739875153494498999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52760743892001637274655989 4946319739875153494498999)
                ·
                  refine ⟨7419479609812730241748499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4946319739875153494498999 7419479609812730241748499)
                  ·
                    refine ⟨11129219414719095362622749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7419479609812730241748499 11129219414719095362622749)
                    ·
                      refine ⟨4173457280519660760983531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11129219414719095362622749 4173457280519660760983531)
                      ·
                        rfl

theorem cell23_8127779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 5, 1, 1, 3].length) (baseStart_8127779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8127779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8127779 prefixEnd_8127779 := by exact prefixLift 8127779
  have htrace : WordTrace (prefixWord ++ tailWord_8127779) baseStart_8127779 baseEnd_8127779 := by
    simpa [prefixWord, tailWord_8127779, baseEnd_8127779] using wordTrace_append hprefix tailTrace_8127779
  have hstable : (prefixWord ++ tailWord_8127779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8127779).length < 2 ^ (prefixWord ++ tailWord_8127779).sum := by decide
  have hdescent : baseEnd_8127779 < baseStart_8127779 := by decide
  rcases family_descends (prefixWord ++ tailWord_8127779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8127796 : List Nat := [2, 5, 1, 1, 1, 1, 1, 6, 1, 1, 3]
def baseStart_8127796 : Nat := 118140960795 + 8127796 * 2 ^ 59
def prefixEnd_8127796 : Nat := 4983230072969 + 3 ^ 40 * 8127796 * 2
def baseEnd_8127796 : Nat := 4173466009690787194470953

theorem tailTrace_8127796 : CollatzResearch.WordTrace tailWord_8127796 prefixEnd_8127796 4173466009690787194470953 := by
  unfold tailWord_8127796
  simp only [CollatzResearch.WordTrace]
  refine ⟨148222537031195341944133621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197630049374927122592178161 148222537031195341944133621)
  ·
    refine ⟨13895862846674563307262527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 148222537031195341944133621 13895862846674563307262527)
    ·
      refine ⟨20843794270011844960893791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13895862846674563307262527 20843794270011844960893791)
      ·
        refine ⟨31265691405017767441340687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20843794270011844960893791 31265691405017767441340687)
        ·
          refine ⟨46898537107526651162011031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31265691405017767441340687 46898537107526651162011031)
          ·
            refine ⟨70347805661289976743016547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46898537107526651162011031 70347805661289976743016547)
            ·
              refine ⟨105521708491934965114524821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70347805661289976743016547 105521708491934965114524821)
              ·
                refine ⟨4946330085559451489743351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 105521708491934965114524821 4946330085559451489743351)
                ·
                  refine ⟨7419495128339177234615027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4946330085559451489743351 7419495128339177234615027)
                  ·
                    refine ⟨11129242692508765851922541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7419495128339177234615027 11129242692508765851922541)
                    ·
                      refine ⟨4173466009690787194470953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11129242692508765851922541 4173466009690787194470953)
                      ·
                        rfl

theorem cell23_8127796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 6, 1, 1, 3].length) (baseStart_8127796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8127796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8127796 prefixEnd_8127796 := by exact prefixLift 8127796
  have htrace : WordTrace (prefixWord ++ tailWord_8127796) baseStart_8127796 baseEnd_8127796 := by
    simpa [prefixWord, tailWord_8127796, baseEnd_8127796] using wordTrace_append hprefix tailTrace_8127796
  have hstable : (prefixWord ++ tailWord_8127796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8127796).length < 2 ^ (prefixWord ++ tailWord_8127796).sum := by decide
  have hdescent : baseEnd_8127796 < baseStart_8127796 := by decide
  rcases family_descends (prefixWord ++ tailWord_8127796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8127808 : List Nat := [2, 1, 1, 2, 2, 1, 4, 10]
def baseStart_8127808 : Nat := 118140960795 + 8127808 * 2 ^ 59
def prefixEnd_8127808 : Nat := 4983230072969 + 3 ^ 40 * 8127808 * 2
def baseEnd_8127808 : Nat := 154573043387357079537811

theorem tailTrace_8127808 : CollatzResearch.WordTrace tailWord_8127808 prefixEnd_8127808 154573043387357079537811 := by
  unfold tailWord_8127808
  simp only [CollatzResearch.WordTrace]
  refine ⟨148222755869173604968852039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197630341158898139958469385 148222755869173604968852039)
  ·
    refine ⟨222334133803760407453278059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148222755869173604968852039 222334133803760407453278059)
    ·
      refine ⟨333501200705640611179917089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222334133803760407453278059 333501200705640611179917089)
      ·
        refine ⟨250125900529230458384937817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 333501200705640611179917089 250125900529230458384937817)
        ·
          refine ⟨187594425396922843788703363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 250125900529230458384937817 187594425396922843788703363)
          ·
            refine ⟨281391638095384265683055045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187594425396922843788703363 281391638095384265683055045)
            ·
              refine ⟨52760932142884549815572821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 281391638095384265683055045 52760932142884549815572821)
              ·
                refine ⟨154573043387357079537811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 52760932142884549815572821 154573043387357079537811)
                ·
                  rfl

theorem cell23_8127808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 10].length) (baseStart_8127808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8127808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8127808 prefixEnd_8127808 := by exact prefixLift 8127808
  have htrace : WordTrace (prefixWord ++ tailWord_8127808) baseStart_8127808 baseEnd_8127808 := by
    simpa [prefixWord, tailWord_8127808, baseEnd_8127808] using wordTrace_append hprefix tailTrace_8127808
  have hstable : (prefixWord ++ tailWord_8127808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8127808).length < 2 ^ (prefixWord ++ tailWord_8127808).sum := by decide
  have hdescent : baseEnd_8127808 < baseStart_8127808 := by decide
  rcases family_descends (prefixWord ++ tailWord_8127808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8127815 : List Nat := [1, 1, 4, 1, 2, 4, 1, 1, 1, 1, 6]
def baseStart_8127815 : Nat := 118140960795 + 8127815 * 2 ^ 59
def prefixEnd_8127815 : Nat := 4983230072969 + 3 ^ 40 * 8127815 * 2
def baseEnd_8127815 : Nat := 4173475765823222620133365

theorem tailTrace_8127815 : CollatzResearch.WordTrace tailWord_8127815 prefixEnd_8127815 4173475765823222620133365 := by
  unfold tailWord_8127815
  simp only [CollatzResearch.WordTrace]
  refine ⟨296445767049321850133208899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197630511366214566755472599 296445767049321850133208899)
  ·
    refine ⟨444668650573982775199813349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296445767049321850133208899 444668650573982775199813349)
    ·
      refine ⟨83375371982621770349965003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 444668650573982775199813349 83375371982621770349965003)
      ·
        refine ⟨125063057973932655524947505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83375371982621770349965003 125063057973932655524947505)
        ·
          refine ⟨93797293480449491643710629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125063057973932655524947505 93797293480449491643710629)
          ·
            refine ⟨17586992527584279683195743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93797293480449491643710629 17586992527584279683195743)
            ·
              refine ⟨26380488791376419524793615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17586992527584279683195743 26380488791376419524793615)
              ·
                refine ⟨39570733187064629287190423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26380488791376419524793615 39570733187064629287190423)
                ·
                  refine ⟨59356099780596943930785635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39570733187064629287190423 59356099780596943930785635)
                  ·
                    refine ⟨89034149670895415896178453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59356099780596943930785635 89034149670895415896178453)
                    ·
                      refine ⟨4173475765823222620133365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 89034149670895415896178453 4173475765823222620133365)
                      ·
                        rfl

theorem cell23_8127815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 1, 1, 1, 6].length) (baseStart_8127815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8127815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8127815 prefixEnd_8127815 := by exact prefixLift 8127815
  have htrace : WordTrace (prefixWord ++ tailWord_8127815) baseStart_8127815 baseEnd_8127815 := by
    simpa [prefixWord, tailWord_8127815, baseEnd_8127815] using wordTrace_append hprefix tailTrace_8127815
  have hstable : (prefixWord ++ tailWord_8127815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8127815).length < 2 ^ (prefixWord ++ tailWord_8127815).sum := by decide
  have hdescent : baseEnd_8127815 < baseStart_8127815 := by decide
  rcases family_descends (prefixWord ++ tailWord_8127815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8127869 : List Nat := [1, 4, 1, 1, 2, 2, 3, 3, 2, 1, 3]
def baseStart_8127869 : Nat := 118140960795 + 8127869 * 2 ^ 59
def prefixEnd_8127869 : Nat := 4983230072969 + 3 ^ 40 * 8127869 * 2
def baseEnd_8127869 : Nat := 4173503493778565408858117

theorem tailTrace_8127869 : CollatzResearch.WordTrace tailWord_8127869 prefixEnd_8127869 4173503493778565408858117 := by
  unfold tailWord_8127869
  simp only [CollatzResearch.WordTrace]
  refine ⟨296447736591126217355674661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197631824394084144903783107 296447736591126217355674661)
  ·
    refine ⟨55583950610836165754188999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 296447736591126217355674661 55583950610836165754188999)
    ·
      refine ⟨83375925916254248631283499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55583950610836165754188999 83375925916254248631283499)
      ·
        refine ⟨125063888874381372946925249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83375925916254248631283499 125063888874381372946925249)
        ·
          refine ⟨93797916655786029710193937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125063888874381372946925249 93797916655786029710193937)
          ·
            refine ⟨70348437491839522282645453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93797916655786029710193937 70348437491839522282645453)
            ·
              refine ⟨26380664059439820855992045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70348437491839522282645453 26380664059439820855992045)
              ·
                refine ⟨9892749022289932820997017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26380664059439820855992045 9892749022289932820997017)
                ·
                  refine ⟨7419561766717449615747763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9892749022289932820997017 7419561766717449615747763)
                  ·
                    refine ⟨11129342650076174423621645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7419561766717449615747763 11129342650076174423621645)
                    ·
                      refine ⟨4173503493778565408858117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11129342650076174423621645 4173503493778565408858117)
                      ·
                        rfl

theorem cell23_8127869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 3, 2, 1, 3].length) (baseStart_8127869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8127869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8127869 prefixEnd_8127869 := by exact prefixLift 8127869
  have htrace : WordTrace (prefixWord ++ tailWord_8127869) baseStart_8127869 baseEnd_8127869 := by
    simpa [prefixWord, tailWord_8127869, baseEnd_8127869] using wordTrace_append hprefix tailTrace_8127869
  have hstable : (prefixWord ++ tailWord_8127869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8127869).length < 2 ^ (prefixWord ++ tailWord_8127869).sum := by decide
  have hdescent : baseEnd_8127869 < baseStart_8127869 := by decide
  rcases family_descends (prefixWord ++ tailWord_8127869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8127870 : List Nat := [4, 2, 3, 2, 2, 1, 1, 2, 1, 1, 4]
def baseStart_8127870 : Nat := 118140960795 + 8127870 * 2 ^ 59
def prefixEnd_8127870 : Nat := 4983230072969 + 3 ^ 40 * 8127870 * 2
def baseEnd_8127870 : Nat := 4173504007259219904945613

theorem tailTrace_8127870 : CollatzResearch.WordTrace tailWord_8127870 prefixEnd_8127870 4173504007259219904945613 := by
  unfold tailWord_8127870
  simp only [CollatzResearch.WordTrace]
  refine ⟨37055971633015324315807633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 197631848709415063017640709 37055971633015324315807633)
  ·
    refine ⟨27791978724761493236855725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37055971633015324315807633 27791978724761493236855725)
    ·
      refine ⟨10421992021785559963820897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27791978724761493236855725 10421992021785559963820897)
      ·
        refine ⟨7816494016339169972865673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10421992021785559963820897 7816494016339169972865673)
        ·
          refine ⟨5862370512254377479649255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7816494016339169972865673 5862370512254377479649255)
          ·
            refine ⟨8793555768381566219473883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5862370512254377479649255 8793555768381566219473883)
            ·
              refine ⟨13190333652572349329210825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8793555768381566219473883 13190333652572349329210825)
              ·
                refine ⟨9892750239429261996908119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13190333652572349329210825 9892750239429261996908119)
                ·
                  refine ⟨14839125359143892995362179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9892750239429261996908119 14839125359143892995362179)
                  ·
                    refine ⟨22258688038715839493043269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14839125359143892995362179 22258688038715839493043269)
                    ·
                      refine ⟨4173504007259219904945613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22258688038715839493043269 4173504007259219904945613)
                      ·
                        rfl

theorem cell23_8127870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 1, 2, 1, 1, 4].length) (baseStart_8127870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8127870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8127870 prefixEnd_8127870 := by exact prefixLift 8127870
  have htrace : WordTrace (prefixWord ++ tailWord_8127870) baseStart_8127870 baseEnd_8127870 := by
    simpa [prefixWord, tailWord_8127870, baseEnd_8127870] using wordTrace_append hprefix tailTrace_8127870
  have hstable : (prefixWord ++ tailWord_8127870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8127870).length < 2 ^ (prefixWord ++ tailWord_8127870).sum := by decide
  have hdescent : baseEnd_8127870 < baseStart_8127870 := by decide
  rcases family_descends (prefixWord ++ tailWord_8127870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8127873 : List Nat := [1, 2, 4, 3, 3, 1, 1, 2, 1, 2, 3]
def baseStart_8127873 : Nat := 118140960795 + 8127873 * 2 ^ 59
def prefixEnd_8127873 : Nat := 4983230072969 + 3 ^ 40 * 8127873 * 2
def baseEnd_8127873 : Nat := 4173505547701183393208099

theorem tailTrace_8127873 : CollatzResearch.WordTrace tailWord_8127873 prefixEnd_8127873 4173505547701183393208099 := by
  unfold tailWord_8127873
  simp only [CollatzResearch.WordTrace]
  refine ⟨296447882483111726038820273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197631921655407817359213515 296447882483111726038820273)
  ·
    refine ⟨222335911862333794529115205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296447882483111726038820273 222335911862333794529115205)
    ·
      refine ⟨41687983474187586474209101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 222335911862333794529115205 41687983474187586474209101)
      ·
        refine ⟨15632993802820344927828413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41687983474187586474209101 15632993802820344927828413)
        ·
          refine ⟨5862372676057629347935655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15632993802820344927828413 5862372676057629347935655)
          ·
            refine ⟨8793559014086444021903483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5862372676057629347935655 8793559014086444021903483)
            ·
              refine ⟨13190338521129666032855225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8793559014086444021903483 13190338521129666032855225)
              ·
                refine ⟨9892753890847249524641419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13190338521129666032855225 9892753890847249524641419)
                ·
                  refine ⟨14839130836270874286962129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9892753890847249524641419 14839130836270874286962129)
                  ·
                    refine ⟨11129348127203155715221597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14839130836270874286962129 11129348127203155715221597)
                    ·
                      refine ⟨4173505547701183393208099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11129348127203155715221597 4173505547701183393208099)
                      ·
                        rfl

theorem cell23_8127873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 1, 2, 1, 2, 3].length) (baseStart_8127873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8127873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8127873 prefixEnd_8127873 := by exact prefixLift 8127873
  have htrace : WordTrace (prefixWord ++ tailWord_8127873) baseStart_8127873 baseEnd_8127873 := by
    simpa [prefixWord, tailWord_8127873, baseEnd_8127873] using wordTrace_append hprefix tailTrace_8127873
  have hstable : (prefixWord ++ tailWord_8127873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8127873).length < 2 ^ (prefixWord ++ tailWord_8127873).sum := by decide
  have hdescent : baseEnd_8127873 < baseStart_8127873 := by decide
  rcases family_descends (prefixWord ++ tailWord_8127873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8127879 : List Nat := [1, 1, 4, 2, 2, 3, 1, 1, 3, 3, 2]
def baseStart_8127879 : Nat := 118140960795 + 8127879 * 2 ^ 59
def prefixEnd_8127879 : Nat := 4983230072969 + 3 ^ 40 * 8127879 * 2
def baseEnd_8127879 : Nat := 4173508628585110369733071

theorem tailTrace_8127879 : CollatzResearch.WordTrace tailWord_8127879 prefixEnd_8127879 4173508628585110369733071 := by
  unfold tailWord_8127879
  simp only [CollatzResearch.WordTrace]
  refine ⟨296448101321089989063538691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197632067547393326042359127 296448101321089989063538691)
  ·
    refine ⟨444672151981634983595308037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296448101321089989063538691 444672151981634983595308037)
    ·
      refine ⟨83376028496556559424120257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 444672151981634983595308037 83376028496556559424120257)
      ·
        refine ⟨62532021372417419568090193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83376028496556559424120257 62532021372417419568090193)
        ·
          refine ⟨46899016029313064676067645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62532021372417419568090193 46899016029313064676067645)
          ·
            refine ⟨17587131010992399253525367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46899016029313064676067645 17587131010992399253525367)
            ·
              refine ⟨26380696516488598880288051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17587131010992399253525367 26380696516488598880288051)
              ·
                refine ⟨39571044774732898320432077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26380696516488598880288051 39571044774732898320432077)
                ·
                  refine ⟨14839141790524836870162029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39571044774732898320432077 14839141790524836870162029)
                  ·
                    refine ⟨5564678171446813826310761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14839141790524836870162029 5564678171446813826310761)
                    ·
                      refine ⟨4173508628585110369733071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5564678171446813826310761 4173508628585110369733071)
                      ·
                        rfl

theorem cell23_8127879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 1, 3, 3, 2].length) (baseStart_8127879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8127879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8127879 prefixEnd_8127879 := by exact prefixLift 8127879
  have htrace : WordTrace (prefixWord ++ tailWord_8127879) baseStart_8127879 baseEnd_8127879 := by
    simpa [prefixWord, tailWord_8127879, baseEnd_8127879] using wordTrace_append hprefix tailTrace_8127879
  have hstable : (prefixWord ++ tailWord_8127879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8127879).length < 2 ^ (prefixWord ++ tailWord_8127879).sum := by decide
  have hdescent : baseEnd_8127879 < baseStart_8127879 := by decide
  rcases family_descends (prefixWord ++ tailWord_8127879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8127952 : List Nat := [2, 1, 1, 1, 1, 2, 2, 2, 4, 5, 2]
def baseStart_8127952 : Nat := 118140960795 + 8127952 * 2 ^ 59
def prefixEnd_8127952 : Nat := 4983230072969 + 3 ^ 40 * 8127952 * 2
def baseEnd_8127952 : Nat := 4173546112672888584120235

theorem tailTrace_8127952 : CollatzResearch.WordTrace tailWord_8127952 prefixEnd_8127952 4173546112672888584120235 := by
  unfold tailWord_8127952
  simp only [CollatzResearch.WordTrace]
  refine ⟨148225381924912761265473055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197633842566550348353964073 148225381924912761265473055)
  ·
    refine ⟨222338072887369141898209583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148225381924912761265473055 222338072887369141898209583)
    ·
      refine ⟨333507109331053712847314375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222338072887369141898209583 333507109331053712847314375)
      ·
        refine ⟨500260663996580569270971563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 333507109331053712847314375 500260663996580569270971563)
        ·
          refine ⟨750390995994870853906457345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 500260663996580569270971563 750390995994870853906457345)
          ·
            refine ⟨562793246996153140429843009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 750390995994870853906457345 562793246996153140429843009)
            ·
              refine ⟨422094935247114855322382257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 562793246996153140429843009 422094935247114855322382257)
              ·
                refine ⟨316571201435336141491786693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 422094935247114855322382257 316571201435336141491786693)
                ·
                  refine ⟨59357100269125526529710005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 316571201435336141491786693 59357100269125526529710005)
                  ·
                    refine ⟨5564728150230518112160313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59357100269125526529710005 5564728150230518112160313)
                    ·
                      refine ⟨4173546112672888584120235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5564728150230518112160313 4173546112672888584120235)
                      ·
                        rfl

theorem cell23_8127952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 4, 5, 2].length) (baseStart_8127952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8127952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8127952 prefixEnd_8127952 := by exact prefixLift 8127952
  have htrace : WordTrace (prefixWord ++ tailWord_8127952) baseStart_8127952 baseEnd_8127952 := by
    simpa [prefixWord, tailWord_8127952, baseEnd_8127952] using wordTrace_append hprefix tailTrace_8127952
  have hstable : (prefixWord ++ tailWord_8127952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8127952).length < 2 ^ (prefixWord ++ tailWord_8127952).sum := by decide
  have hdescent : baseEnd_8127952 < baseStart_8127952 := by decide
  rcases family_descends (prefixWord ++ tailWord_8127952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8127982 : List Nat := [4, 1, 2, 1, 2, 1, 1, 1, 3, 3, 4]
def baseStart_8127982 : Nat := 118140960795 + 8127982 * 2 ^ 59
def prefixEnd_8127982 : Nat := 4983230072969 + 3 ^ 40 * 8127982 * 2
def baseEnd_8127982 : Nat := 4173561517092523466745097

theorem tailTrace_8127982 : CollatzResearch.WordTrace tailWord_8127982 prefixEnd_8127982 4173561517092523466745097 := by
  unfold tailWord_8127982
  simp only [CollatzResearch.WordTrace]
  refine ⟨37056482254964604706817275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 197634572026477891769692133 37056482254964604706817275)
  ·
    refine ⟨55584723382446907060225913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37056482254964604706817275 55584723382446907060225913)
    ·
      refine ⟨41688542536835180295169435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55584723382446907060225913 41688542536835180295169435)
      ·
        refine ⟨62532813805252770442754153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41688542536835180295169435 62532813805252770442754153)
        ·
          refine ⟨46899610353939577832065615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62532813805252770442754153 46899610353939577832065615)
          ·
            refine ⟨70349415530909366748098423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46899610353939577832065615 70349415530909366748098423)
            ·
              refine ⟨105524123296364050122147635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70349415530909366748098423 105524123296364050122147635)
              ·
                refine ⟨158286184944546075183221453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105524123296364050122147635 158286184944546075183221453)
                ·
                  refine ⟨59357319354204778193708045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 158286184944546075183221453 59357319354204778193708045)
                  ·
                    refine ⟨22258994757826791822640517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59357319354204778193708045 22258994757826791822640517)
                    ·
                      refine ⟨4173561517092523466745097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22258994757826791822640517 4173561517092523466745097)
                      ·
                        rfl

theorem cell23_8127982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 1, 3, 3, 4].length) (baseStart_8127982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8127982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8127982 prefixEnd_8127982 := by exact prefixLift 8127982
  have htrace : WordTrace (prefixWord ++ tailWord_8127982) baseStart_8127982 baseEnd_8127982 := by
    simpa [prefixWord, tailWord_8127982, baseEnd_8127982] using wordTrace_append hprefix tailTrace_8127982
  have hstable : (prefixWord ++ tailWord_8127982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8127982).length < 2 ^ (prefixWord ++ tailWord_8127982).sum := by decide
  have hdescent : baseEnd_8127982 < baseStart_8127982 := by decide
  rcases family_descends (prefixWord ++ tailWord_8127982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8127995 : List Nat := [1, 1, 1, 1, 1, 3, 2, 2, 4, 1, 6]
def baseStart_8127995 : Nat := 118140960795 + 8127995 * 2 ^ 59
def prefixEnd_8127995 : Nat := 4983230072969 + 3 ^ 40 * 8127995 * 2
def baseEnd_8127995 : Nat := 4173568192341031915882537

theorem tailTrace_8127995 : CollatzResearch.WordTrace tailWord_8127995 prefixEnd_8127995 4173568192341031915882537 := by
  unfold tailWord_8127995
  simp only [CollatzResearch.WordTrace]
  refine ⟨296452332188669740874761439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197634888125779827249840959 296452332188669740874761439)
  ·
    refine ⟨444678498283004611312142159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296452332188669740874761439 444678498283004611312142159)
    ·
      refine ⟨667017747424506916968213239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 444678498283004611312142159 667017747424506916968213239)
      ·
        refine ⟨1000526621136760375452319859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 667017747424506916968213239 1000526621136760375452319859)
        ·
          refine ⟨1500789931705140563178479789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1000526621136760375452319859 1500789931705140563178479789)
          ·
            refine ⟨562796224389427711191929921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1500789931705140563178479789 562796224389427711191929921)
            ·
              refine ⟨422097168292070783393947441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 562796224389427711191929921 422097168292070783393947441)
              ·
                refine ⟨316572876219053087545460581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 422097168292070783393947441 316572876219053087545460581)
                ·
                  refine ⟨59357414291072453914773859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 316572876219053087545460581 59357414291072453914773859)
                  ·
                    refine ⟨89036121436608680872160789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59357414291072453914773859 89036121436608680872160789)
                    ·
                      refine ⟨4173568192341031915882537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 89036121436608680872160789 4173568192341031915882537)
                      ·
                        rfl

theorem cell23_8127995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 2, 4, 1, 6].length) (baseStart_8127995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8127995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8127995 prefixEnd_8127995 := by exact prefixLift 8127995
  have htrace : WordTrace (prefixWord ++ tailWord_8127995) baseStart_8127995 baseEnd_8127995 := by
    simpa [prefixWord, tailWord_8127995, baseEnd_8127995] using wordTrace_append hprefix tailTrace_8127995
  have hstable : (prefixWord ++ tailWord_8127995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8127995).length < 2 ^ (prefixWord ++ tailWord_8127995).sum := by decide
  have hdescent : baseEnd_8127995 < baseStart_8127995 := by decide
  rcases family_descends (prefixWord ++ tailWord_8127995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8128013 : List Nat := [1, 7, 1, 1, 2, 1, 1, 2, 2, 5]
def baseStart_8128013 : Nat := 118140960795 + 8128013 * 2 ^ 59
def prefixEnd_8128013 : Nat := 4983230072969 + 3 ^ 40 * 8128013 * 2
def baseEnd_8128013 : Nat := 1391192478330937615152485

theorem tailTrace_8128013 : CollatzResearch.WordTrace tailWord_8128013 prefixEnd_8128013 1391192478330937615152485 := by
  unfold tailWord_8128013
  simp only [CollatzResearch.WordTrace]
  refine ⟨296452988702604529948916693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197635325801736353299277795 296452988702604529948916693)
  ·
    refine ⟨6948116922717293670677735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 296452988702604529948916693 6948116922717293670677735)
    ·
      refine ⟨10422175384075940506016603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6948116922717293670677735 10422175384075940506016603)
      ·
        refine ⟨15633263076113910759024905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10422175384075940506016603 15633263076113910759024905)
        ·
          refine ⟨11724947307085433069268679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15633263076113910759024905 11724947307085433069268679)
          ·
            refine ⟨17587420960628149603903019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11724947307085433069268679 17587420960628149603903019)
            ·
              refine ⟨26381131440942224405854529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17587420960628149603903019 26381131440942224405854529)
              ·
                refine ⟨19785848580706668304390897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26381131440942224405854529 19785848580706668304390897)
                ·
                  refine ⟨14839386435530001228293173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19785848580706668304390897 14839386435530001228293173)
                  ·
                    refine ⟨1391192478330937615152485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14839386435530001228293173 1391192478330937615152485)
                    ·
                      rfl

theorem cell23_8128013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 2, 2, 5].length) (baseStart_8128013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8128013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8128013 prefixEnd_8128013 := by exact prefixLift 8128013
  have htrace : WordTrace (prefixWord ++ tailWord_8128013) baseStart_8128013 baseEnd_8128013 := by
    simpa [prefixWord, tailWord_8128013, baseEnd_8128013] using wordTrace_append hprefix tailTrace_8128013
  have hstable : (prefixWord ++ tailWord_8128013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8128013).length < 2 ^ (prefixWord ++ tailWord_8128013).sum := by decide
  have hdescent : baseEnd_8128013 < baseStart_8128013 := by decide
  rcases family_descends (prefixWord ++ tailWord_8128013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8128019 : List Nat := [1, 1, 1, 2, 1, 7, 1, 2, 2, 2, 3]
def baseStart_8128019 : Nat := 118140960795 + 8128019 * 2 ^ 59
def prefixEnd_8128019 : Nat := 4983230072969 + 3 ^ 40 * 8128019 * 2
def baseEnd_8128019 : Nat := 4173580515876739821982427

theorem tailTrace_8128019 : CollatzResearch.WordTrace tailWord_8128019 prefixEnd_8128019 4173580515876739821982427 := by
  unfold tailWord_8128019
  simp only [CollatzResearch.WordTrace]
  refine ⟨296453207540582792973635111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197635471693721861982423407 296453207540582792973635111)
  ·
    refine ⟨444679811310874189460452667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296453207540582792973635111 444679811310874189460452667)
    ·
      refine ⟨667019716966311284190679001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 444679811310874189460452667 667019716966311284190679001)
      ·
        refine ⟨500264787724733463143009251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 667019716966311284190679001 500264787724733463143009251)
        ·
          refine ⟨750397181587100194714513877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 500264787724733463143009251 750397181587100194714513877)
          ·
            refine ⟨17587433943447660813621419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 750397181587100194714513877 17587433943447660813621419)
            ·
              refine ⟨26381150915171491220432129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17587433943447660813621419 26381150915171491220432129)
              ·
                refine ⟨19785863186378618415324097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26381150915171491220432129 19785863186378618415324097)
                ·
                  refine ⟨14839397389783963811493073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19785863186378618415324097 14839397389783963811493073)
                  ·
                    refine ⟨11129548042337972858619805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14839397389783963811493073 11129548042337972858619805)
                    ·
                      refine ⟨4173580515876739821982427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11129548042337972858619805 4173580515876739821982427)
                      ·
                        rfl

theorem cell23_8128019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 2, 2, 2, 3].length) (baseStart_8128019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8128019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8128019 prefixEnd_8128019 := by exact prefixLift 8128019
  have htrace : WordTrace (prefixWord ++ tailWord_8128019) baseStart_8128019 baseEnd_8128019 := by
    simpa [prefixWord, tailWord_8128019, baseEnd_8128019] using wordTrace_append hprefix tailTrace_8128019
  have hstable : (prefixWord ++ tailWord_8128019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8128019).length < 2 ^ (prefixWord ++ tailWord_8128019).sum := by decide
  have hdescent : baseEnd_8128019 < baseStart_8128019 := by decide
  rcases family_descends (prefixWord ++ tailWord_8128019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8128049 : List Nat := [1, 2, 2, 3, 1, 1, 1, 3, 5, 1, 3]
def baseStart_8128049 : Nat := 118140960795 + 8128049 * 2 ^ 59
def prefixEnd_8128049 : Nat := 4983230072969 + 3 ^ 40 * 8128049 * 2
def baseEnd_8128049 : Nat := 4173595920296374704607289

theorem tailTrace_8128049 : CollatzResearch.WordTrace tailWord_8128049 prefixEnd_8128049 4173595920296374704607289 := by
  unfold tailWord_8128049
  simp only [CollatzResearch.WordTrace]
  refine ⟨296454301730474108097227201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197636201153649405398151467 296454301730474108097227201)
  ·
    refine ⟨222340726297855581072920401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296454301730474108097227201 222340726297855581072920401)
    ·
      refine ⟨166755544723391685804690301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222340726297855581072920401 166755544723391685804690301)
      ·
        refine ⟨62533329271271882176758863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166755544723391685804690301 62533329271271882176758863)
        ·
          refine ⟨93799993906907823265138295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62533329271271882176758863 93799993906907823265138295)
          ·
            refine ⟨140699990860361734897707443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93799993906907823265138295 140699990860361734897707443)
            ·
              refine ⟨211049986290542602346561165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140699990860361734897707443 211049986290542602346561165)
              ·
                refine ⟨79143744858953475879960437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 211049986290542602346561165 79143744858953475879960437)
                ·
                  refine ⟨7419726080526888363746291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 79143744858953475879960437 7419726080526888363746291)
                  ·
                    refine ⟨11129589120790332545619437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7419726080526888363746291 11129589120790332545619437)
                    ·
                      refine ⟨4173595920296374704607289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11129589120790332545619437 4173595920296374704607289)
                      ·
                        rfl

theorem cell23_8128049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 3, 5, 1, 3].length) (baseStart_8128049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8128049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8128049 prefixEnd_8128049 := by exact prefixLift 8128049
  have htrace : WordTrace (prefixWord ++ tailWord_8128049) baseStart_8128049 baseEnd_8128049 := by
    simpa [prefixWord, tailWord_8128049, baseEnd_8128049] using wordTrace_append hprefix tailTrace_8128049
  have hstable : (prefixWord ++ tailWord_8128049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8128049).length < 2 ^ (prefixWord ++ tailWord_8128049).sum := by decide
  have hdescent : baseEnd_8128049 < baseStart_8128049 := by decide
  rcases family_descends (prefixWord ++ tailWord_8128049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8128076 : List Nat := [2, 2, 1, 3, 1, 3, 2, 2, 2, 3, 2]
def baseStart_8128076 : Nat := 118140960795 + 8128076 * 2 ^ 59
def prefixEnd_8128076 : Nat := 4983230072969 + 3 ^ 40 * 8128076 * 2
def baseEnd_8128076 : Nat := 4173609784274046098969665

theorem tailTrace_8128076 : CollatzResearch.WordTrace tailWord_8128076 prefixEnd_8128076 4173609784274046098969665 := by
  unfold tailWord_8128076
  simp only [CollatzResearch.WordTrace]
  refine ⟨148227643250688145854230041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197636857667584194472306721 148227643250688145854230041)
  ·
    refine ⟨111170732438016109390672531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148227643250688145854230041 111170732438016109390672531)
    ·
      refine ⟨166756098657024164086008797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111170732438016109390672531 166756098657024164086008797)
      ·
        refine ⟨62533536996384061532253299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166756098657024164086008797 62533536996384061532253299)
        ·
          refine ⟨93800305494576092298379949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62533536996384061532253299 93800305494576092298379949)
          ·
            refine ⟨35175114560466034611892481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93800305494576092298379949 35175114560466034611892481)
            ·
              refine ⟨26381335920349525958919361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35175114560466034611892481 26381335920349525958919361)
              ·
                refine ⟨19786001940262144469189521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26381335920349525958919361 19786001940262144469189521)
                ·
                  refine ⟨14839501455196608351892141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19786001940262144469189521 14839501455196608351892141)
                  ·
                    refine ⟨5564813045698728131959553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14839501455196608351892141 5564813045698728131959553)
                    ·
                      refine ⟨4173609784274046098969665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5564813045698728131959553 4173609784274046098969665)
                      ·
                        rfl

theorem cell23_8128076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 2, 2, 3, 2].length) (baseStart_8128076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8128076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8128076 prefixEnd_8128076 := by exact prefixLift 8128076
  have htrace : WordTrace (prefixWord ++ tailWord_8128076) baseStart_8128076 baseEnd_8128076 := by
    simpa [prefixWord, tailWord_8128076, baseEnd_8128076] using wordTrace_append hprefix tailTrace_8128076
  have hstable : (prefixWord ++ tailWord_8128076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8128076).length < 2 ^ (prefixWord ++ tailWord_8128076).sum := by decide
  have hdescent : baseEnd_8128076 < baseStart_8128076 := by decide
  rcases family_descends (prefixWord ++ tailWord_8128076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8128077 : List Nat := [1, 6, 1, 1, 3, 2, 2, 2, 1, 4]
def baseStart_8128077 : Nat := 118140960795 + 8128077 * 2 ^ 59
def prefixEnd_8128077 : Nat := 4983230072969 + 3 ^ 40 * 8128077 * 2
def baseEnd_8128077 : Nat := 1391203432584900198352387

theorem tailTrace_8128077 : CollatzResearch.WordTrace tailWord_8128077 prefixEnd_8128077 1391203432584900198352387 := by
  unfold tailWord_8128077
  simp only [CollatzResearch.WordTrace]
  refine ⟨296455322974372668879246485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197636881982915112586164323 296455322974372668879246485)
  ·
    refine ⟨13896343264423718853714679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 296455322974372668879246485 13896343264423718853714679)
    ·
      refine ⟨20844514896635578280572019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13896343264423718853714679 20844514896635578280572019)
      ·
        refine ⟨31266772344953367420858029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20844514896635578280572019 31266772344953367420858029)
        ·
          refine ⟨11725039629357512782821761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31266772344953367420858029 11725039629357512782821761)
          ·
            refine ⟨8793779722018134587116321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11725039629357512782821761 8793779722018134587116321)
            ·
              refine ⟨6595334791513600940337241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8793779722018134587116321 6595334791513600940337241)
              ·
                refine ⟨4946501093635200705252931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6595334791513600940337241 4946501093635200705252931)
                ·
                  refine ⟨7419751640452801057879397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4946501093635200705252931 7419751640452801057879397)
                  ·
                    refine ⟨1391203432584900198352387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7419751640452801057879397 1391203432584900198352387)
                    ·
                      rfl

theorem cell23_8128077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 2, 2, 1, 4].length) (baseStart_8128077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8128077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8128077 prefixEnd_8128077 := by exact prefixLift 8128077
  have htrace : WordTrace (prefixWord ++ tailWord_8128077) baseStart_8128077 baseEnd_8128077 := by
    simpa [prefixWord, tailWord_8128077, baseEnd_8128077] using wordTrace_append hprefix tailTrace_8128077
  have hstable : (prefixWord ++ tailWord_8128077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8128077).length < 2 ^ (prefixWord ++ tailWord_8128077).sum := by decide
  have hdescent : baseEnd_8128077 < baseStart_8128077 := by decide
  rcases family_descends (prefixWord ++ tailWord_8128077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8128099 : List Nat := [1, 1, 1, 5, 1, 4, 2, 1, 1, 6]
def baseStart_8128099 : Nat := 118140960795 + 8128099 * 2 ^ 59
def prefixEnd_8128099 : Nat := 4983230072969 + 3 ^ 40 * 8128099 * 2
def baseEnd_8128099 : Nat := 1391207198109699836327353

theorem tailTrace_8128099 : CollatzResearch.WordTrace tailWord_8128099 prefixEnd_8128099 1391207198109699836327353 := by
  unfold tailWord_8128099
  simp only [CollatzResearch.WordTrace]
  refine ⟨296456125380292966636547351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197637416920195311091031567 296456125380292966636547351)
  ·
    refine ⟨444684188070439449954821027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296456125380292966636547351 444684188070439449954821027)
    ·
      refine ⟨667026282105659174932231541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 444684188070439449954821027 667026282105659174932231541)
      ·
        refine ⟨62533713947405547649896707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 667026282105659174932231541 62533713947405547649896707)
        ·
          refine ⟨93800570921108321474845061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62533713947405547649896707 93800570921108321474845061)
          ·
            refine ⟨17587607047707810276533449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93800570921108321474845061 17587607047707810276533449)
            ·
              refine ⟨13190705285780857707400087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17587607047707810276533449 13190705285780857707400087)
              ·
                refine ⟨19786057928671286561100131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13190705285780857707400087 19786057928671286561100131)
                ·
                  refine ⟨29679086893006929841650197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19786057928671286561100131 29679086893006929841650197)
                  ·
                    refine ⟨1391207198109699836327353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29679086893006929841650197 1391207198109699836327353)
                    ·
                      rfl

theorem cell23_8128099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 2, 1, 1, 6].length) (baseStart_8128099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8128099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8128099 prefixEnd_8128099 := by exact prefixLift 8128099
  have htrace : WordTrace (prefixWord ++ tailWord_8128099) baseStart_8128099 baseEnd_8128099 := by
    simpa [prefixWord, tailWord_8128099, baseEnd_8128099] using wordTrace_append hprefix tailTrace_8128099
  have hstable : (prefixWord ++ tailWord_8128099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8128099).length < 2 ^ (prefixWord ++ tailWord_8128099).sum := by decide
  have hdescent : baseEnd_8128099 < baseStart_8128099 := by decide
  rcases family_descends (prefixWord ++ tailWord_8128099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8128110 : List Nat := [4, 1, 2, 2, 3, 2, 1, 1, 2, 3, 2]
def baseStart_8128110 : Nat := 118140960795 + 8128110 * 2 ^ 59
def prefixEnd_8128110 : Nat := 4983230072969 + 3 ^ 40 * 8128110 * 2
def baseEnd_8128110 : Nat := 4173627242616298965944509

theorem tailTrace_8128110 : CollatzResearch.WordTrace tailWord_8128110 prefixEnd_8128110 4173627242616298965944509 := by
  unfold tailWord_8128110
  simp only [CollatzResearch.WordTrace]
  refine ⟨37057065822906639439399723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 197637684388835410343465189 37057065822906639439399723)
  ·
    refine ⟨55585598734359959159099585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37057065822906639439399723 55585598734359959159099585)
    ·
      refine ⟨41689199050769969369324689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55585598734359959159099585 41689199050769969369324689)
      ·
        refine ⟨31266899288077477026993517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41689199050769969369324689 31266899288077477026993517)
        ·
          refine ⟨11725087233029053885122569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31266899288077477026993517 11725087233029053885122569)
          ·
            refine ⟨8793815424771790413841927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11725087233029053885122569 8793815424771790413841927)
            ·
              refine ⟨13190723137157685620762891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8793815424771790413841927 13190723137157685620762891)
              ·
                refine ⟨19786084705736528431144337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13190723137157685620762891 19786084705736528431144337)
                ·
                  refine ⟨14839563529302396323358253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19786084705736528431144337 14839563529302396323358253)
                  ·
                    refine ⟨5564836323488398621259345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14839563529302396323358253 5564836323488398621259345)
                    ·
                      refine ⟨4173627242616298965944509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5564836323488398621259345 4173627242616298965944509)
                      ·
                        rfl

theorem cell23_8128110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 1, 1, 2, 3, 2].length) (baseStart_8128110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8128110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8128110 prefixEnd_8128110 := by exact prefixLift 8128110
  have htrace : WordTrace (prefixWord ++ tailWord_8128110) baseStart_8128110 baseEnd_8128110 := by
    simpa [prefixWord, tailWord_8128110, baseEnd_8128110] using wordTrace_append hprefix tailTrace_8128110
  have hstable : (prefixWord ++ tailWord_8128110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8128110).length < 2 ^ (prefixWord ++ tailWord_8128110).sum := by decide
  have hdescent : baseEnd_8128110 < baseStart_8128110 := by decide
  rcases family_descends (prefixWord ++ tailWord_8128110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8128183 : List Nat := [1, 1, 3, 1, 5, 1, 2, 3, 1, 3, 2]
def baseStart_8128183 : Nat := 118140960795 + 8128183 * 2 ^ 59
def prefixEnd_8128183 : Nat := 4983230072969 + 3 ^ 40 * 8128183 * 2
def baseEnd_8128183 : Nat := 4173664726704077180331673

theorem tailTrace_8128183 : CollatzResearch.WordTrace tailWord_8128183 prefixEnd_8128183 4173664726704077180331673 := by
  unfold tailWord_8128183
  simp only [CollatzResearch.WordTrace]
  refine ⟨296459189111988648982605203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197639459407992432655070135 296459189111988648982605203)
  ·
    refine ⟨444688783667982973473907805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296459189111988648982605203 444688783667982973473907805)
    ·
      refine ⟨166758293875493615052715427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 444688783667982973473907805 166758293875493615052715427)
      ·
        refine ⟨250137440813240422579073141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166758293875493615052715427 250137440813240422579073141)
        ·
          refine ⟨23450385076241289616788107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 250137440813240422579073141 23450385076241289616788107)
          ·
            refine ⟨35175577614361934425182161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23450385076241289616788107 35175577614361934425182161)
            ·
              refine ⟨26381683210771450818886621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35175577614361934425182161 26381683210771450818886621)
              ·
                refine ⟨9893131204039294057082483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26381683210771450818886621 9893131204039294057082483)
                ·
                  refine ⟨14839696806058941085623725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9893131204039294057082483 14839696806058941085623725)
                  ·
                    refine ⟨5564886302272102907108897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14839696806058941085623725 5564886302272102907108897)
                    ·
                      refine ⟨4173664726704077180331673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5564886302272102907108897 4173664726704077180331673)
                      ·
                        rfl

theorem cell23_8128183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 3, 1, 3, 2].length) (baseStart_8128183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8128183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8128183 prefixEnd_8128183 := by exact prefixLift 8128183
  have htrace : WordTrace (prefixWord ++ tailWord_8128183) baseStart_8128183 baseEnd_8128183 := by
    simpa [prefixWord, tailWord_8128183, baseEnd_8128183] using wordTrace_append hprefix tailTrace_8128183
  have hstable : (prefixWord ++ tailWord_8128183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8128183).length < 2 ^ (prefixWord ++ tailWord_8128183).sum := by decide
  have hdescent : baseEnd_8128183 < baseStart_8128183 := by decide
  rcases family_descends (prefixWord ++ tailWord_8128183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8128199 : List Nat := [1, 1, 4, 1, 1, 1, 4, 1, 2, 4, 3]
def baseStart_8128199 : Nat := 118140960795 + 8128199 * 2 ^ 59
def prefixEnd_8128199 : Nat := 4983230072969 + 3 ^ 40 * 8128199 * 2
def baseEnd_8128199 : Nat := 4173672942394549117731599

theorem tailTrace_8128199 : CollatzResearch.WordTrace tailWord_8128199 prefixEnd_8128199 4173672942394549117731599 := by
  unfold tailWord_8128199
  simp only [CollatzResearch.WordTrace]
  refine ⟨296459772679930683715187651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197639848453287122476791767 296459772679930683715187651)
  ·
    refine ⟨444689659019896025572781477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296459772679930683715187651 444689659019896025572781477)
    ·
      refine ⟨83379311066230504794896527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 444689659019896025572781477 83379311066230504794896527)
      ·
        refine ⟨125068966599345757192344791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83379311066230504794896527 125068966599345757192344791)
        ·
          refine ⟨187603449899018635788517187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125068966599345757192344791 187603449899018635788517187)
          ·
            refine ⟨281405174848527953682775781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187603449899018635788517187 281405174848527953682775781)
            ·
              refine ⟨52763470284098991315520459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 281405174848527953682775781 52763470284098991315520459)
              ·
                refine ⟨79145205426148486973280689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52763470284098991315520459 79145205426148486973280689)
                ·
                  refine ⟨59358904069611365229960517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79145205426148486973280689 59358904069611365229960517)
                  ·
                    refine ⟨11129794513052130980617597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59358904069611365229960517 11129794513052130980617597)
                    ·
                      refine ⟨4173672942394549117731599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11129794513052130980617597 4173672942394549117731599)
                      ·
                        rfl

theorem cell23_8128199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 1, 2, 4, 3].length) (baseStart_8128199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8128199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8128199 prefixEnd_8128199 := by exact prefixLift 8128199
  have htrace : WordTrace (prefixWord ++ tailWord_8128199) baseStart_8128199 baseEnd_8128199 := by
    simpa [prefixWord, tailWord_8128199, baseEnd_8128199] using wordTrace_append hprefix tailTrace_8128199
  have hstable : (prefixWord ++ tailWord_8128199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8128199).length < 2 ^ (prefixWord ++ tailWord_8128199).sum := by decide
  have hdescent : baseEnd_8128199 < baseStart_8128199 := by decide
  rcases family_descends (prefixWord ++ tailWord_8128199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8128259 : List Nat := [1, 1, 1, 3, 2, 2, 4, 1, 1, 2, 5]
def baseStart_8128259 : Nat := 118140960795 + 8128259 * 2 ^ 59
def prefixEnd_8128259 : Nat := 4983230072969 + 3 ^ 40 * 8128259 * 2
def baseEnd_8128259 : Nat := 4173703751233818882981323

theorem tailTrace_8128259 : CollatzResearch.WordTrace tailWord_8128259 prefixEnd_8128259 4173703751233818882981323 := by
  unfold tailWord_8128259
  simp only [CollatzResearch.WordTrace]
  refine ⟨296461961059713313962371831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197641307373142209308247887 296461961059713313962371831)
  ·
    refine ⟨444692941589569970943557747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296461961059713313962371831 444692941589569970943557747)
    ·
      refine ⟨667039412384354956415336621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 444692941589569970943557747 667039412384354956415336621)
      ·
        refine ⟨250139779644133108655751233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 667039412384354956415336621 250139779644133108655751233)
        ·
          refine ⟨187604834733099831491813425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 250139779644133108655751233 187604834733099831491813425)
          ·
            refine ⟨140703626049824873618860069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 187604834733099831491813425 140703626049824873618860069)
            ·
              refine ⟨26381929884342163803536263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 140703626049824873618860069 26381929884342163803536263)
              ·
                refine ⟨39572894826513245705304395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26381929884342163803536263 39572894826513245705304395)
                ·
                  refine ⟨59359342239769868557956593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39572894826513245705304395 59359342239769868557956593)
                  ·
                    refine ⟨44519506679827401418467445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59359342239769868557956593 44519506679827401418467445)
                    ·
                      refine ⟨4173703751233818882981323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44519506679827401418467445 4173703751233818882981323)
                      ·
                        rfl

theorem cell23_8128259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 1, 1, 2, 5].length) (baseStart_8128259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8128259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8128259 prefixEnd_8128259 := by exact prefixLift 8128259
  have htrace : WordTrace (prefixWord ++ tailWord_8128259) baseStart_8128259 baseEnd_8128259 := by
    simpa [prefixWord, tailWord_8128259, baseEnd_8128259] using wordTrace_append hprefix tailTrace_8128259
  have hstable : (prefixWord ++ tailWord_8128259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8128259).length < 2 ^ (prefixWord ++ tailWord_8128259).sum := by decide
  have hdescent : baseEnd_8128259 < baseStart_8128259 := by decide
  rcases family_descends (prefixWord ++ tailWord_8128259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8128263 : List Nat := [1, 1, 4, 4, 2, 1, 1, 1, 2, 3, 3]
def baseStart_8128263 : Nat := 118140960795 + 8128263 * 2 ^ 59
def prefixEnd_8128263 : Nat := 4983230072969 + 3 ^ 40 * 8128263 * 2
def baseEnd_8128263 : Nat := 4173705805156436867331305

theorem tailTrace_8128263 : CollatzResearch.WordTrace tailWord_8128263 prefixEnd_8128263 4173705805156436867331305 := by
  unfold tailWord_8128263
  simp only [CollatzResearch.WordTrace]
  refine ⟨296462106951698822645517443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197641404634465881763678295 296462106951698822645517443)
  ·
    refine ⟨444693160427548233968276165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296462106951698822645517443 444693160427548233968276165)
    ·
      refine ⟨83379967580165293869051781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 444693160427548233968276165 83379967580165293869051781)
      ·
        refine ⟨15633743921280992600447209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83379967580165293869051781 15633743921280992600447209)
        ·
          refine ⟨11725307940960744450335407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15633743921280992600447209 11725307940960744450335407)
          ·
            refine ⟨17587961911441116675503111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11725307940960744450335407 17587961911441116675503111)
            ·
              refine ⟨26381942867161675013254667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17587961911441116675503111 26381942867161675013254667)
              ·
                refine ⟨39572914300742512519882001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26381942867161675013254667 39572914300742512519882001)
                ·
                  refine ⟨29679685725556884389911501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39572914300742512519882001 29679685725556884389911501)
                  ·
                    refine ⟨11129882147083831646216813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29679685725556884389911501 11129882147083831646216813)
                    ·
                      refine ⟨4173705805156436867331305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11129882147083831646216813 4173705805156436867331305)
                      ·
                        rfl

theorem cell23_8128263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 1, 2, 3, 3].length) (baseStart_8128263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8128263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8128263 prefixEnd_8128263 := by exact prefixLift 8128263
  have htrace : WordTrace (prefixWord ++ tailWord_8128263) baseStart_8128263 baseEnd_8128263 := by
    simpa [prefixWord, tailWord_8128263, baseEnd_8128263] using wordTrace_append hprefix tailTrace_8128263
  have hstable : (prefixWord ++ tailWord_8128263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8128263).length < 2 ^ (prefixWord ++ tailWord_8128263).sum := by decide
  have hdescent : baseEnd_8128263 < baseStart_8128263 := by decide
  rcases family_descends (prefixWord ++ tailWord_8128263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8128329 : List Nat := [1, 2, 1, 1, 2, 4, 1, 2, 1, 2, 6]
def baseStart_8128329 : Nat := 118140960795 + 8128329 * 2 ^ 59
def prefixEnd_8128329 : Nat := 4983230072969 + 3 ^ 40 * 8128329 * 2
def baseEnd_8128329 : Nat := 4173739694879633609106001

theorem tailTrace_8128329 : CollatzResearch.WordTrace tailWord_8128329 prefixEnd_8128329 4173739694879633609106001 := by
  unfold tailWord_8128329
  simp only [CollatzResearch.WordTrace]
  refine ⟨296464514169459715917420041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197643009446306477278280027 296464514169459715917420041)
  ·
    refine ⟨222348385627094786938065031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296464514169459715917420041 222348385627094786938065031)
    ·
      refine ⟨333522578440642180407097547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222348385627094786938065031 333522578440642180407097547)
      ·
        refine ⟨500283867660963270610646321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 333522578440642180407097547 500283867660963270610646321)
        ·
          refine ⟨375212900745722452957984741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 500283867660963270610646321 375212900745722452957984741)
          ·
            refine ⟨70352418889822959929622139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 375212900745722452957984741 70352418889822959929622139)
            ·
              refine ⟨105528628334734439894433209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70352418889822959929622139 105528628334734439894433209)
              ·
                refine ⟨79146471251050829920824907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105528628334734439894433209 79146471251050829920824907)
                ·
                  refine ⟨118719706876576244881237361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79146471251050829920824907 118719706876576244881237361)
                  ·
                    refine ⟨89039780157432183660928021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 118719706876576244881237361 89039780157432183660928021)
                    ·
                      refine ⟨4173739694879633609106001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 89039780157432183660928021 4173739694879633609106001)
                      ·
                        rfl

theorem cell23_8128329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 2, 1, 2, 6].length) (baseStart_8128329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8128329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8128329 prefixEnd_8128329 := by exact prefixLift 8128329
  have htrace : WordTrace (prefixWord ++ tailWord_8128329) baseStart_8128329 baseEnd_8128329 := by
    simpa [prefixWord, tailWord_8128329, baseEnd_8128329] using wordTrace_append hprefix tailTrace_8128329
  have hstable : (prefixWord ++ tailWord_8128329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8128329).length < 2 ^ (prefixWord ++ tailWord_8128329).sum := by decide
  have hdescent : baseEnd_8128329 < baseStart_8128329 := by decide
  rcases family_descends (prefixWord ++ tailWord_8128329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8128413 : List Nat := [1, 4, 2, 1, 2, 2, 3, 1, 1, 1, 5]
def baseStart_8128413 : Nat := 118140960795 + 8128413 * 2 ^ 59
def prefixEnd_8128413 : Nat := 4983230072969 + 3 ^ 40 * 8128413 * 2
def baseEnd_8128413 : Nat := 4173782827254611280455615

theorem tailTrace_8128413 : CollatzResearch.WordTrace tailWord_8128413 prefixEnd_8128413 4173782827254611280455615 := by
  unfold tailWord_8128413
  simp only [CollatzResearch.WordTrace]
  refine ⟨296467577901155398263477893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197645051934103598842318595 296467577901155398263477893)
  ·
    refine ⟨55587670856466637174402105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 296467577901155398263477893 55587670856466637174402105)
    ·
      refine ⟨41690753142349977880801579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55587670856466637174402105 41690753142349977880801579)
      ·
        refine ⟨62536129713524966821202369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41690753142349977880801579 62536129713524966821202369)
        ·
          refine ⟨46902097285143725115901777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62536129713524966821202369 46902097285143725115901777)
          ·
            refine ⟨35176572963857793836926333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46902097285143725115901777 35176572963857793836926333)
            ·
              refine ⟨13191214861446672688847375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35176572963857793836926333 13191214861446672688847375)
              ·
                refine ⟨19786822292170009033271063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13191214861446672688847375 19786822292170009033271063)
                ·
                  refine ⟨29680233438255013549906595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19786822292170009033271063 29680233438255013549906595)
                  ·
                    refine ⟨44520350157382520324859893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29680233438255013549906595 44520350157382520324859893)
                    ·
                      refine ⟨4173782827254611280455615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44520350157382520324859893 4173782827254611280455615)
                      ·
                        rfl

theorem cell23_8128413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 3, 1, 1, 1, 5].length) (baseStart_8128413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8128413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8128413 prefixEnd_8128413 := by exact prefixLift 8128413
  have htrace : WordTrace (prefixWord ++ tailWord_8128413) baseStart_8128413 baseEnd_8128413 := by
    simpa [prefixWord, tailWord_8128413, baseEnd_8128413] using wordTrace_append hprefix tailTrace_8128413
  have hstable : (prefixWord ++ tailWord_8128413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8128413).length < 2 ^ (prefixWord ++ tailWord_8128413).sum := by decide
  have hdescent : baseEnd_8128413 < baseStart_8128413 := by decide
  rcases family_descends (prefixWord ++ tailWord_8128413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8128420 : List Nat := [2, 3, 1, 2, 1, 4, 2, 2, 2, 4]
def baseStart_8128420 : Nat := 118140960795 + 8128420 * 2 ^ 59
def prefixEnd_8128420 : Nat := 4983230072969 + 3 ^ 40 * 8128420 * 2
def baseEnd_8128420 : Nat := 1391262140539730917689361

theorem tailTrace_8128420 : CollatzResearch.WordTrace tailWord_8128420 prefixEnd_8128420 1391262140539730917689361 := by
  unfold tailWord_8128420
  simp only [CollatzResearch.WordTrace]
  refine ⟨148233916606065019229491357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197645222141420025639321809 148233916606065019229491357)
  ·
    refine ⟨55587718727274382211059259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148233916606065019229491357 55587718727274382211059259)
    ·
      refine ⟨83381578090911573316588889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55587718727274382211059259 83381578090911573316588889)
      ·
        refine ⟨62536183568183679987441667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83381578090911573316588889 62536183568183679987441667)
        ·
          refine ⟨93804275352275519981162501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62536183568183679987441667 93804275352275519981162501)
          ·
            refine ⟨17588301628551659996467969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93804275352275519981162501 17588301628551659996467969)
            ·
              refine ⟨13191226221413744997350977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17588301628551659996467969 13191226221413744997350977)
              ·
                refine ⟨9893419666060308748013233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13191226221413744997350977 9893419666060308748013233)
                ·
                  refine ⟨7420064749545231561009925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9893419666060308748013233 7420064749545231561009925)
                  ·
                    refine ⟨1391262140539730917689361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7420064749545231561009925 1391262140539730917689361)
                    ·
                      rfl

theorem cell23_8128420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 2, 2, 2, 4].length) (baseStart_8128420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8128420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8128420 prefixEnd_8128420 := by exact prefixLift 8128420
  have htrace : WordTrace (prefixWord ++ tailWord_8128420) baseStart_8128420 baseEnd_8128420 := by
    simpa [prefixWord, tailWord_8128420, baseEnd_8128420] using wordTrace_append hprefix tailTrace_8128420
  have hstable : (prefixWord ++ tailWord_8128420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8128420).length < 2 ^ (prefixWord ++ tailWord_8128420).sum := by decide
  have hdescent : baseEnd_8128420 < baseStart_8128420 := by decide
  rcases family_descends (prefixWord ++ tailWord_8128420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8128433 : List Nat := [1, 2, 2, 4, 2, 3, 1, 8]
def baseStart_8128433 : Nat := 118140960795 + 8128433 * 2 ^ 59
def prefixEnd_8128433 : Nat := 4983230072969 + 3 ^ 40 * 8128433 * 2
def baseEnd_8128433 : Nat := 154584929513618563044649

theorem tailTrace_8128433 : CollatzResearch.WordTrace tailWord_8128433 prefixEnd_8128433 154584929513618563044649 := by
  unfold tailWord_8128433
  simp only [CollatzResearch.WordTrace]
  refine ⟨296468307361082941679205953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197645538240721961119470635 296468307361082941679205953)
  ·
    refine ⟨222351230520812206259404465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296468307361082941679205953 222351230520812206259404465)
    ·
      refine ⟨166763422890609154694553349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222351230520812206259404465 166763422890609154694553349)
      ·
        refine ⟨31268141791989216505228753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 166763422890609154694553349 31268141791989216505228753)
        ·
          refine ⟨23451106343991912378921565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31268141791989216505228753 23451106343991912378921565)
          ·
            refine ⟨8794164878996967142095587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23451106343991912378921565 8794164878996967142095587)
            ·
              refine ⟨13191247318495450713143381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8794164878996967142095587 13191247318495450713143381)
              ·
                refine ⟨154584929513618563044649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13191247318495450713143381 154584929513618563044649)
                ·
                  rfl

theorem cell23_8128433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 1, 8].length) (baseStart_8128433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8128433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8128433 prefixEnd_8128433 := by exact prefixLift 8128433
  have htrace : WordTrace (prefixWord ++ tailWord_8128433) baseStart_8128433 baseEnd_8128433 := by
    simpa [prefixWord, tailWord_8128433, baseEnd_8128433] using wordTrace_append hprefix tailTrace_8128433
  have hstable : (prefixWord ++ tailWord_8128433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8128433).length < 2 ^ (prefixWord ++ tailWord_8128433).sum := by decide
  have hdescent : baseEnd_8128433 < baseStart_8128433 := by decide
  rcases family_descends (prefixWord ++ tailWord_8128433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8128444 : List Nat := [2, 2, 2, 5, 1, 1, 1, 2, 3, 2, 2]
def baseStart_8128444 : Nat := 118140960795 + 8128444 * 2 ^ 59
def prefixEnd_8128444 : Nat := 4983230072969 + 3 ^ 40 * 8128444 * 2
def baseEnd_8128444 : Nat := 4173798745154900659167973

theorem tailTrace_8128444 : CollatzResearch.WordTrace tailWord_8128444 prefixEnd_8128444 4173798745154900659167973 := by
  unfold tailWord_8128444
  simp only [CollatzResearch.WordTrace]
  refine ⟨148234354282021545278928193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197645805709362060371904257 148234354282021545278928193)
  ·
    refine ⟨111175765711516158959196145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148234354282021545278928193 111175765711516158959196145)
    ·
      refine ⟨83381824283637119219397109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111175765711516158959196145 83381824283637119219397109)
      ·
        refine ⟨7817046026590979926818479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 83381824283637119219397109 7817046026590979926818479)
        ·
          refine ⟨11725569039886469890227719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7817046026590979926818479 11725569039886469890227719)
          ·
            refine ⟨17588353559829704835341579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11725569039886469890227719 17588353559829704835341579)
            ·
              refine ⟨26382530339744557253012369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17588353559829704835341579 26382530339744557253012369)
              ·
                refine ⟨19786897754808417939759277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26382530339744557253012369 19786897754808417939759277)
                ·
                  refine ⟨7420086658053156727409729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19786897754808417939759277 7420086658053156727409729)
                  ·
                    refine ⟨5565064993539867545557297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7420086658053156727409729 5565064993539867545557297)
                    ·
                      refine ⟨4173798745154900659167973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5565064993539867545557297 4173798745154900659167973)
                      ·
                        rfl

theorem cell23_8128444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 2, 3, 2, 2].length) (baseStart_8128444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8128444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8128444 prefixEnd_8128444 := by exact prefixLift 8128444
  have htrace : WordTrace (prefixWord ++ tailWord_8128444) baseStart_8128444 baseEnd_8128444 := by
    simpa [prefixWord, tailWord_8128444, baseEnd_8128444] using wordTrace_append hprefix tailTrace_8128444
  have hstable : (prefixWord ++ tailWord_8128444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8128444).length < 2 ^ (prefixWord ++ tailWord_8128444).sum := by decide
  have hdescent : baseEnd_8128444 < baseStart_8128444 := by decide
  rcases family_descends (prefixWord ++ tailWord_8128444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8128477 : List Nat := [1, 4, 3, 1, 3, 1, 1, 1, 4, 1, 3]
def baseStart_8128477 : Nat := 118140960795 + 8128477 * 2 ^ 59
def prefixEnd_8128477 : Nat := 4983230072969 + 3 ^ 40 * 8128477 * 2
def baseEnd_8128477 : Nat := 4173815690016499030055321

theorem tailTrace_8128477 : CollatzResearch.WordTrace tailWord_8128477 prefixEnd_8128477 4173815690016499030055321 := by
  unfold tailWord_8128477
  simp only [CollatzResearch.WordTrace]
  refine ⟨296469912172923537193807685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197646608115282358129205123 296469912172923537193807685)
  ·
    refine ⟨55588108532423163223838941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 296469912172923537193807685 55588108532423163223838941)
    ·
      refine ⟨20845540699658686208939603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55588108532423163223838941 20845540699658686208939603)
      ·
        refine ⟨31268311049488029313409405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20845540699658686208939603 31268311049488029313409405)
        ·
          refine ⟨11725616643558010992528527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31268311049488029313409405 11725616643558010992528527)
          ·
            refine ⟨17588424965337016488792791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11725616643558010992528527 17588424965337016488792791)
            ·
              refine ⟨26382637448005524733189187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17588424965337016488792791 26382637448005524733189187)
              ·
                refine ⟨39573956172008287099783781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26382637448005524733189187 39573956172008287099783781)
                ·
                  refine ⟨7420116782251553831209459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39573956172008287099783781 7420116782251553831209459)
                  ·
                    refine ⟨11130175173377330746814189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7420116782251553831209459 11130175173377330746814189)
                    ·
                      refine ⟨4173815690016499030055321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11130175173377330746814189 4173815690016499030055321)
                      ·
                        rfl

theorem cell23_8128477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 1, 4, 1, 3].length) (baseStart_8128477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8128477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8128477 prefixEnd_8128477 := by exact prefixLift 8128477
  have htrace : WordTrace (prefixWord ++ tailWord_8128477) baseStart_8128477 baseEnd_8128477 := by
    simpa [prefixWord, tailWord_8128477, baseEnd_8128477] using wordTrace_append hprefix tailTrace_8128477
  have hstable : (prefixWord ++ tailWord_8128477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8128477).length < 2 ^ (prefixWord ++ tailWord_8128477).sum := by decide
  have hdescent : baseEnd_8128477 < baseStart_8128477 := by decide
  rcases family_descends (prefixWord ++ tailWord_8128477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8128494 : List Nat := [4, 1, 2, 1, 3, 2, 3, 1, 2, 1, 3]
def baseStart_8128494 : Nat := 118140960795 + 8128494 * 2 ^ 59
def prefixEnd_8128494 : Nat := 4983230072969 + 3 ^ 40 * 8128494 * 2
def baseEnd_8128494 : Nat := 4173824419187625463542743

theorem tailTrace_8128494 : CollatzResearch.WordTrace tailWord_8128494 prefixEnd_8128494 4173824419187625463542743 := by
  unfold tailWord_8128494
  simp only [CollatzResearch.WordTrace]
  refine ⟨37058816526732743637147067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 197647021475907966064784357 37058816526732743637147067)
  ·
    refine ⟨55588224790099115455720601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37058816526732743637147067 55588224790099115455720601)
    ·
      refine ⟨41691168592574336591790451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55588224790099115455720601 41691168592574336591790451)
      ·
        refine ⟨62536752888861504887685677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41691168592574336591790451 62536752888861504887685677)
        ·
          refine ⟨23451282333323064332882129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62536752888861504887685677 23451282333323064332882129)
          ·
            refine ⟨17588461749992298249661597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23451282333323064332882129 17588461749992298249661597)
            ·
              refine ⟨6595673156247111843623099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17588461749992298249661597 6595673156247111843623099)
              ·
                refine ⟨9893509734370667765434649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6595673156247111843623099 9893509734370667765434649)
                ·
                  refine ⟨7420132300778000824075987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9893509734370667765434649 7420132300778000824075987)
                  ·
                    refine ⟨11130198451167001236113981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7420132300778000824075987 11130198451167001236113981)
                    ·
                      refine ⟨4173824419187625463542743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11130198451167001236113981 4173824419187625463542743)
                      ·
                        rfl

theorem cell23_8128494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 3, 1, 2, 1, 3].length) (baseStart_8128494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8128494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8128494 prefixEnd_8128494 := by exact prefixLift 8128494
  have htrace : WordTrace (prefixWord ++ tailWord_8128494) baseStart_8128494 baseEnd_8128494 := by
    simpa [prefixWord, tailWord_8128494, baseEnd_8128494] using wordTrace_append hprefix tailTrace_8128494
  have hstable : (prefixWord ++ tailWord_8128494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8128494).length < 2 ^ (prefixWord ++ tailWord_8128494).sum := by decide
  have hdescent : baseEnd_8128494 < baseStart_8128494 := by decide
  rcases family_descends (prefixWord ++ tailWord_8128494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8128540 : List Nat := [2, 2, 3, 1, 3, 3, 1, 1, 7]
def baseStart_8128540 : Nat := 118140960795 + 8128540 * 2 ^ 59
def prefixEnd_8128540 : Nat := 4983230072969 + 3 ^ 40 * 8128540 * 2
def baseEnd_8128540 : Nat := 463760893255303587063059

theorem tailTrace_8128540 : CollatzResearch.WordTrace tailWord_8128540 prefixEnd_8128540 463760893255303587063059 := by
  unfold tailWord_8128540
  simp only [CollatzResearch.WordTrace]
  refine ⟨148236104985847649476675537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197648139981130199302234049 148236104985847649476675537)
  ·
    refine ⟨111177078739385737107506653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148236104985847649476675537 111177078739385737107506653)
    ·
      refine ⟨41691404527269651415314995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111177078739385737107506653 41691404527269651415314995)
      ·
        refine ⟨62537106790904477122972493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41691404527269651415314995 62537106790904477122972493)
        ·
          refine ⟨23451415046589178921114685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62537106790904477122972493 23451415046589178921114685)
          ·
            refine ⟨8794280642470942095418007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23451415046589178921114685 8794280642470942095418007)
            ·
              refine ⟨13191420963706413143127011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8794280642470942095418007 13191420963706413143127011)
              ·
                refine ⟨19787131445559619714690517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13191420963706413143127011 19787131445559619714690517)
                ·
                  refine ⟨463760893255303587063059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19787131445559619714690517 463760893255303587063059)
                  ·
                    rfl

theorem cell23_8128540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 1, 1, 7].length) (baseStart_8128540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8128540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8128540 prefixEnd_8128540 := by exact prefixLift 8128540
  have htrace : WordTrace (prefixWord ++ tailWord_8128540) baseStart_8128540 baseEnd_8128540 := by
    simpa [prefixWord, tailWord_8128540, baseEnd_8128540] using wordTrace_append hprefix tailTrace_8128540
  have hstable : (prefixWord ++ tailWord_8128540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8128540).length < 2 ^ (prefixWord ++ tailWord_8128540).sum := by decide
  have hdescent : baseEnd_8128540 < baseStart_8128540 := by decide
  rcases family_descends (prefixWord ++ tailWord_8128540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8128551 : List Nat := [1, 1, 7, 1, 2, 1, 1, 3, 2, 2, 2]
def baseStart_8128551 : Nat := 118140960795 + 8128551 * 2 ^ 59
def prefixEnd_8128551 : Nat := 4983230072969 + 3 ^ 40 * 8128551 * 2
def baseEnd_8128551 : Nat := 4173853687584931740529981

theorem tailTrace_8128551 : CollatzResearch.WordTrace tailWord_8128551 prefixEnd_8128551 4173853687584931740529981 := by
  unfold tailWord_8128551
  simp only [CollatzResearch.WordTrace]
  refine ⟨296472611174655447832001507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197648407449770298554667671 296472611174655447832001507)
  ·
    refine ⟨444708916761983171748002261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296472611174655447832001507 444708916761983171748002261)
    ·
      refine ⟨10422865236608980587843803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 444708916761983171748002261 10422865236608980587843803)
      ·
        refine ⟨15634297854913470881765705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10422865236608980587843803 15634297854913470881765705)
        ·
          refine ⟨11725723391185103161324279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15634297854913470881765705 11725723391185103161324279)
          ·
            refine ⟨17588585086777654741986419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11725723391185103161324279 17588585086777654741986419)
            ·
              refine ⟨26382877630166482112979629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17588585086777654741986419 26382877630166482112979629)
              ·
                refine ⟨9893579111312430792367361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26382877630166482112979629 9893579111312430792367361)
                ·
                  refine ⟨7420184333484323094275521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9893579111312430792367361 7420184333484323094275521)
                  ·
                    refine ⟨5565138250113242320706641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7420184333484323094275521 5565138250113242320706641)
                    ·
                      refine ⟨4173853687584931740529981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5565138250113242320706641 4173853687584931740529981)
                      ·
                        rfl

theorem cell23_8128551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 3, 2, 2, 2].length) (baseStart_8128551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8128551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8128551 prefixEnd_8128551 := by exact prefixLift 8128551
  have htrace : WordTrace (prefixWord ++ tailWord_8128551) baseStart_8128551 baseEnd_8128551 := by
    simpa [prefixWord, tailWord_8128551, baseEnd_8128551] using wordTrace_append hprefix tailTrace_8128551
  have hstable : (prefixWord ++ tailWord_8128551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8128551).length < 2 ^ (prefixWord ++ tailWord_8128551).sum := by decide
  have hdescent : baseEnd_8128551 < baseStart_8128551 := by decide
  rcases family_descends (prefixWord ++ tailWord_8128551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8128590 : List Nat := [4, 1, 1, 1, 1, 4, 2, 2, 2, 1, 4]
def baseStart_8128590 : Nat := 118140960795 + 8128590 * 2 ^ 59
def prefixEnd_8128590 : Nat := 4983230072969 + 3 ^ 40 * 8128590 * 2
def baseEnd_8128590 : Nat := 4173873713330457087942301

theorem tailTrace_8128590 : CollatzResearch.WordTrace tailWord_8128590 prefixEnd_8128590 4173873713330457087942301 := by
  unfold tailWord_8128590
  simp only [CollatzResearch.WordTrace]
  refine ⟨37059254202689269686583903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 197649355747676104995114149 37059254202689269686583903)
  ·
    refine ⟨55588881304033904529875855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37059254202689269686583903 55588881304033904529875855)
    ·
      refine ⟨83383321956050856794813783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55588881304033904529875855 83383321956050856794813783)
      ·
        refine ⟨125074982934076285192220675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83383321956050856794813783 125074982934076285192220675)
        ·
          refine ⟨187612474401114427788331013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125074982934076285192220675 187612474401114427788331013)
          ·
            refine ⟨35177338950208955210312065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 187612474401114427788331013 35177338950208955210312065)
            ·
              refine ⟨26383004212656716407734049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35177338950208955210312065 26383004212656716407734049)
              ·
                refine ⟨19787253159492537305800537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26383004212656716407734049 19787253159492537305800537)
                ·
                  refine ⟨14840439869619402979350403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19787253159492537305800537 14840439869619402979350403)
                  ·
                    refine ⟨22260659804429104469025605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14840439869619402979350403 22260659804429104469025605)
                    ·
                      refine ⟨4173873713330457087942301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22260659804429104469025605 4173873713330457087942301)
                      ·
                        rfl

theorem cell23_8128590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 2, 2, 1, 4].length) (baseStart_8128590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8128590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8128590 prefixEnd_8128590 := by exact prefixLift 8128590
  have htrace : WordTrace (prefixWord ++ tailWord_8128590) baseStart_8128590 baseEnd_8128590 := by
    simpa [prefixWord, tailWord_8128590, baseEnd_8128590] using wordTrace_append hprefix tailTrace_8128590
  have hstable : (prefixWord ++ tailWord_8128590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8128590).length < 2 ^ (prefixWord ++ tailWord_8128590).sum := by decide
  have hdescent : baseEnd_8128590 < baseStart_8128590 := by decide
  rcases family_descends (prefixWord ++ tailWord_8128590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8128593 : List Nat := [1, 2, 2, 1, 3, 1, 1, 2, 3, 4, 3]
def baseStart_8128593 : Nat := 118140960795 + 8128593 * 2 ^ 59
def prefixEnd_8128593 : Nat := 4983230072969 + 3 ^ 40 * 8128593 * 2
def baseEnd_8128593 : Nat := 4173875253772420576204787

theorem tailTrace_8128593 : CollatzResearch.WordTrace tailWord_8128593 prefixEnd_8128593 4173875253772420576204787 := by
  unfold tailWord_8128593
  simp only [CollatzResearch.WordTrace]
  refine ⟨296474143040503289005030433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197649428693668859336686955 296474143040503289005030433)
  ·
    refine ⟨222355607280377466753772825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296474143040503289005030433 222355607280377466753772825)
    ·
      refine ⟨166766705460283100065329619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222355607280377466753772825 166766705460283100065329619)
      ·
        refine ⟨250150058190424650097994429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166766705460283100065329619 250150058190424650097994429)
        ·
          refine ⟨93806271821409243786747911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 250150058190424650097994429 93806271821409243786747911)
          ·
            refine ⟨140709407732113865680121867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93806271821409243786747911 140709407732113865680121867)
            ·
              refine ⟨211064111598170798520182801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140709407732113865680121867 211064111598170798520182801)
              ·
                refine ⟨158298083698628098890137101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 211064111598170798520182801 158298083698628098890137101)
                ·
                  refine ⟨59361781386985537083801413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 158298083698628098890137101 59361781386985537083801413)
                  ·
                    refine ⟨11130334010059788203212765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59361781386985537083801413 11130334010059788203212765)
                    ·
                      refine ⟨4173875253772420576204787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11130334010059788203212765 4173875253772420576204787)
                      ·
                        rfl

theorem cell23_8128593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 2, 3, 4, 3].length) (baseStart_8128593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8128593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8128593 prefixEnd_8128593 := by exact prefixLift 8128593
  have htrace : WordTrace (prefixWord ++ tailWord_8128593) baseStart_8128593 baseEnd_8128593 := by
    simpa [prefixWord, tailWord_8128593, baseEnd_8128593] using wordTrace_append hprefix tailTrace_8128593
  have hstable : (prefixWord ++ tailWord_8128593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8128593).length < 2 ^ (prefixWord ++ tailWord_8128593).sum := by decide
  have hdescent : baseEnd_8128593 < baseStart_8128593 := by decide
  rcases family_descends (prefixWord ++ tailWord_8128593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8128640 : List Nat := [2, 1, 1, 2, 1, 3, 1, 1, 7, 1, 3]
def baseStart_8128640 : Nat := 118140960795 + 8128640 * 2 ^ 59
def prefixEnd_8128640 : Nat := 4983230072969 + 3 ^ 40 * 8128640 * 2
def baseEnd_8128640 : Nat := 4173899387363181892317071

theorem tailTrace_8128640 : CollatzResearch.WordTrace tailWord_8128640 prefixEnd_8128640 4173899387363181892317071 := by
  unfold tailWord_8128640
  simp only [CollatzResearch.WordTrace]
  refine ⟨148237928635666508015995687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197650571514222010687994249 148237928635666508015995687)
  ·
    refine ⟨222356892953499762023993531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148237928635666508015995687 222356892953499762023993531)
    ·
      refine ⟨333535339430249643035990297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222356892953499762023993531 333535339430249643035990297)
      ·
        refine ⟨250151504572687232276992723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 333535339430249643035990297 250151504572687232276992723)
        ·
          refine ⟨375227256859030848415489085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250151504572687232276992723 375227256859030848415489085)
          ·
            refine ⟨140710221322136568155808407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 375227256859030848415489085 140710221322136568155808407)
            ·
              refine ⟨211065331983204852233712611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140710221322136568155808407 211065331983204852233712611)
              ·
                refine ⟨316597997974807278350568917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 211065331983204852233712611 316597997974807278350568917)
                ·
                  refine ⟨7420265577534545586341459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 316597997974807278350568917 7420265577534545586341459)
                  ·
                    refine ⟨11130398366301818379512189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7420265577534545586341459 11130398366301818379512189)
                    ·
                      refine ⟨4173899387363181892317071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11130398366301818379512189 4173899387363181892317071)
                      ·
                        rfl

theorem cell23_8128640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 7, 1, 3].length) (baseStart_8128640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8128640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8128640 prefixEnd_8128640 := by exact prefixLift 8128640
  have htrace : WordTrace (prefixWord ++ tailWord_8128640) baseStart_8128640 baseEnd_8128640 := by
    simpa [prefixWord, tailWord_8128640, baseEnd_8128640] using wordTrace_append hprefix tailTrace_8128640
  have hstable : (prefixWord ++ tailWord_8128640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8128640).length < 2 ^ (prefixWord ++ tailWord_8128640).sum := by decide
  have hdescent : baseEnd_8128640 < baseStart_8128640 := by decide
  rcases family_descends (prefixWord ++ tailWord_8128640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8128674 : List Nat := [3, 3, 1, 3, 1, 1, 2, 2, 3, 1, 3]
def baseStart_8128674 : Nat := 118140960795 + 8128674 * 2 ^ 59
def prefixEnd_8128674 : Nat := 4983230072969 + 3 ^ 40 * 8128674 * 2
def baseEnd_8128674 : Nat := 4173916845705434759291915

theorem tailTrace_8128674 : CollatzResearch.WordTrace tailWord_8128674 prefixEnd_8128674 4173916845705434759291915 := by
  unfold tailWord_8128674
  simp only [CollatzResearch.WordTrace]
  refine ⟨74119274338302459959682269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197651398235473226559152717 74119274338302459959682269)
  ·
    refine ⟨27794727876863422484880851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74119274338302459959682269 27794727876863422484880851)
    ·
      refine ⟨41692091815295133727321277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27794727876863422484880851 41692091815295133727321277)
      ·
        refine ⟨15634534430735675147745479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41692091815295133727321277 15634534430735675147745479)
        ·
          refine ⟨23451801646103512721618219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15634534430735675147745479 23451801646103512721618219)
          ·
            refine ⟨35177702469155269082427329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23451801646103512721618219 35177702469155269082427329)
            ·
              refine ⟨26383276851866451811820497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35177702469155269082427329 26383276851866451811820497)
              ·
                refine ⟨19787457638899838858865373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26383276851866451811820497 19787457638899838858865373)
                ·
                  refine ⟨7420296614587439572074515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19787457638899838858865373 7420296614587439572074515)
                  ·
                    refine ⟨11130444921881159358111773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7420296614587439572074515 11130444921881159358111773)
                    ·
                      refine ⟨4173916845705434759291915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11130444921881159358111773 4173916845705434759291915)
                      ·
                        rfl

theorem cell23_8128674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 2, 3, 1, 3].length) (baseStart_8128674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8128674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8128674 prefixEnd_8128674 := by exact prefixLift 8128674
  have htrace : WordTrace (prefixWord ++ tailWord_8128674) baseStart_8128674 baseEnd_8128674 := by
    simpa [prefixWord, tailWord_8128674, baseEnd_8128674] using wordTrace_append hprefix tailTrace_8128674
  have hstable : (prefixWord ++ tailWord_8128674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8128674).length < 2 ^ (prefixWord ++ tailWord_8128674).sum := by decide
  have hdescent : baseEnd_8128674 < baseStart_8128674 := by decide
  rcases family_descends (prefixWord ++ tailWord_8128674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8128690 : List Nat := [3, 2, 1, 1, 1, 3, 1, 1, 6, 4]
def baseStart_8128690 : Nat := 118140960795 + 8128690 * 2 ^ 59
def prefixEnd_8128690 : Nat := 4983230072969 + 3 ^ 40 * 8128690 * 2
def baseEnd_8128690 : Nat := 1391308353798635565563947

theorem tailTrace_8128690 : CollatzResearch.WordTrace tailWord_8128690 prefixEnd_8128690 1391308353798635565563947 := by
  unfold tailWord_8128690
  simp only [CollatzResearch.WordTrace]
  refine ⟨74119420230287968642827881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197651787280767916380874349 74119420230287968642827881)
  ·
    refine ⟨55589565172715976482120911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74119420230287968642827881 55589565172715976482120911)
    ·
      refine ⟨83384347759073964723181367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55589565172715976482120911 83384347759073964723181367)
      ·
        refine ⟨125076521638610947084772051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83384347759073964723181367 125076521638610947084772051)
        ·
          refine ⟨187614782457916420627158077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125076521638610947084772051 187614782457916420627158077)
          ·
            refine ⟨70355543421718657735184279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 187614782457916420627158077 70355543421718657735184279)
            ·
              refine ⟨105533315132577986602776419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70355543421718657735184279 105533315132577986602776419)
              ·
                refine ⟨158299972698866979904164629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105533315132577986602776419 158299972698866979904164629)
                ·
                  refine ⟨7420311220259389683007717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 158299972698866979904164629 7420311220259389683007717)
                  ·
                    refine ⟨1391308353798635565563947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7420311220259389683007717 1391308353798635565563947)
                    ·
                      rfl

theorem cell23_8128690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 1, 6, 4].length) (baseStart_8128690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8128690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8128690 prefixEnd_8128690 := by exact prefixLift 8128690
  have htrace : WordTrace (prefixWord ++ tailWord_8128690) baseStart_8128690 baseEnd_8128690 := by
    simpa [prefixWord, tailWord_8128690, baseEnd_8128690] using wordTrace_append hprefix tailTrace_8128690
  have hstable : (prefixWord ++ tailWord_8128690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8128690).length < 2 ^ (prefixWord ++ tailWord_8128690).sum := by decide
  have hdescent : baseEnd_8128690 < baseStart_8128690 := by decide
  rcases family_descends (prefixWord ++ tailWord_8128690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8128708 : List Nat := [2, 3, 3, 1, 2, 2, 3, 2, 1, 1, 3]
def baseStart_8128708 : Nat := 118140960795 + 8128708 * 2 ^ 59
def prefixEnd_8128708 : Nat := 4983230072969 + 3 ^ 40 * 8128708 * 2
def baseEnd_8128708 : Nat := 4173934304047687626266759

theorem tailTrace_8128708 : CollatzResearch.WordTrace tailWord_8128708 prefixEnd_8128708 4173934304047687626266759 := by
  unfold tailWord_8128708
  simp only [CollatzResearch.WordTrace]
  refine ⟨148239168717543331822733389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197652224956724442430311185 148239168717543331822733389)
  ·
    refine ⟨55589688269078749433525021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148239168717543331822733389 55589688269078749433525021)
    ·
      refine ⟨20846133100904531037571883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55589688269078749433525021 20846133100904531037571883)
      ·
        refine ⟨31269199651356796556357825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20846133100904531037571883 31269199651356796556357825)
        ·
          refine ⟨23451899738517597417268369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31269199651356796556357825 23451899738517597417268369)
          ·
            refine ⟨17588924803888198062951277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23451899738517597417268369 17588924803888198062951277)
            ·
              refine ⟨6595846801458074273606729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17588924803888198062951277 6595846801458074273606729)
              ·
                refine ⟨4946885101093555705205047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6595846801458074273606729 4946885101093555705205047)
                ·
                  refine ⟨7420327651640333557807571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4946885101093555705205047 7420327651640333557807571)
                  ·
                    refine ⟨11130491477460500336711357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7420327651640333557807571 11130491477460500336711357)
                    ·
                      refine ⟨4173934304047687626266759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11130491477460500336711357 4173934304047687626266759)
                      ·
                        rfl

theorem cell23_8128708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 3, 2, 1, 1, 3].length) (baseStart_8128708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8128708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8128708 prefixEnd_8128708 := by exact prefixLift 8128708
  have htrace : WordTrace (prefixWord ++ tailWord_8128708) baseStart_8128708 baseEnd_8128708 := by
    simpa [prefixWord, tailWord_8128708, baseEnd_8128708] using wordTrace_append hprefix tailTrace_8128708
  have hstable : (prefixWord ++ tailWord_8128708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8128708).length < 2 ^ (prefixWord ++ tailWord_8128708).sum := by decide
  have hdescent : baseEnd_8128708 < baseStart_8128708 := by decide
  rcases family_descends (prefixWord ++ tailWord_8128708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8128763 : List Nat := [1, 1, 1, 1, 1, 3, 1, 1, 5, 8]
def baseStart_8128763 : Nat := 118140960795 + 8128763 * 2 ^ 59
def prefixEnd_8128763 : Nat := 4983230072969 + 3 ^ 40 * 8128763 * 2
def baseEnd_8128763 : Nat := 1391320848494561637026335

theorem tailTrace_8128763 : CollatzResearch.WordTrace tailWord_8128763 prefixEnd_8128763 1391320848494561637026335 := by
  unfold tailWord_8128763
  simp only [CollatzResearch.WordTrace]
  refine ⟨296480343449887408038718943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197653562299924938692479295 296480343449887408038718943)
  ·
    refine ⟨444720515174831112058078415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296480343449887408038718943 444720515174831112058078415)
    ·
      refine ⟨667080772762246668087117623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 444720515174831112058078415 667080772762246668087117623)
      ·
        refine ⟨1000621159143370002130676435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 667080772762246668087117623 1000621159143370002130676435)
        ·
          refine ⟨1500931738715055003196014653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1000621159143370002130676435 1500931738715055003196014653)
          ·
            refine ⟨562849402018145626198505495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1500931738715055003196014653 562849402018145626198505495)
            ·
              refine ⟨844274103027218439297758243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 562849402018145626198505495 844274103027218439297758243)
              ·
                refine ⟨1266411154540827658946637365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 844274103027218439297758243 1266411154540827658946637365)
                ·
                  refine ⟨118726045738202593026247253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1266411154540827658946637365 118726045738202593026247253)
                  ·
                    refine ⟨1391320848494561637026335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 118726045738202593026247253 1391320848494561637026335)
                    ·
                      rfl

theorem cell23_8128763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 5, 8].length) (baseStart_8128763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8128763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8128763 prefixEnd_8128763 := by exact prefixLift 8128763
  have htrace : WordTrace (prefixWord ++ tailWord_8128763) baseStart_8128763 baseEnd_8128763 := by
    simpa [prefixWord, tailWord_8128763, baseEnd_8128763] using wordTrace_append hprefix tailTrace_8128763
  have hstable : (prefixWord ++ tailWord_8128763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8128763).length < 2 ^ (prefixWord ++ tailWord_8128763).sum := by decide
  have hdescent : baseEnd_8128763 < baseStart_8128763 := by decide
  rcases family_descends (prefixWord ++ tailWord_8128763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8128764 : List Nat := [2, 2, 2, 1, 4, 1, 1, 4, 2, 1, 3]
def baseStart_8128764 : Nat := 118140960795 + 8128764 * 2 ^ 59
def prefixEnd_8128764 : Nat := 4983230072969 + 3 ^ 40 * 8128764 * 2
def baseEnd_8128764 : Nat := 4173963058964339407166501

theorem tailTrace_8128764 : CollatzResearch.WordTrace tailWord_8128764 prefixEnd_8128764 4173963058964339407166501 := by
  unfold tailWord_8128764
  simp only [CollatzResearch.WordTrace]
  refine ⟨148240189961441892604752673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197653586615255856806336897 148240189961441892604752673)
  ·
    refine ⟨111180142471081419453564505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148240189961441892604752673 111180142471081419453564505)
    ·
      refine ⟨83385106853311064590173379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111180142471081419453564505 83385106853311064590173379)
      ·
        refine ⟨125077660279966596885260069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83385106853311064590173379 125077660279966596885260069)
        ·
          refine ⟨23452061302493736915986263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 125077660279966596885260069 23452061302493736915986263)
          ·
            refine ⟨35178091953740605373979395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23452061302493736915986263 35178091953740605373979395)
            ·
              refine ⟨52767137930610908060969093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35178091953740605373979395 52767137930610908060969093)
              ·
                refine ⟨9893838361989545261431705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52767137930610908060969093 9893838361989545261431705)
                ·
                  refine ⟨7420378771492158946073779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9893838361989545261431705 7420378771492158946073779)
                  ·
                    refine ⟨11130568157238238419110669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7420378771492158946073779 11130568157238238419110669)
                    ·
                      refine ⟨4173963058964339407166501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11130568157238238419110669 4173963058964339407166501)
                      ·
                        rfl

theorem cell23_8128764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 4, 2, 1, 3].length) (baseStart_8128764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8128764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8128764 prefixEnd_8128764 := by exact prefixLift 8128764
  have htrace : WordTrace (prefixWord ++ tailWord_8128764) baseStart_8128764 baseEnd_8128764 := by
    simpa [prefixWord, tailWord_8128764, baseEnd_8128764] using wordTrace_append hprefix tailTrace_8128764
  have hstable : (prefixWord ++ tailWord_8128764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8128764).length < 2 ^ (prefixWord ++ tailWord_8128764).sum := by decide
  have hdescent : baseEnd_8128764 < baseStart_8128764 := by decide
  rcases family_descends (prefixWord ++ tailWord_8128764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8128780 : List Nat := [2, 2, 1, 2, 2, 2, 3, 1, 2, 6]
def baseStart_8128780 : Nat := 118140960795 + 8128780 * 2 ^ 59
def prefixEnd_8128780 : Nat := 4983230072969 + 3 ^ 40 * 8128780 * 2
def baseEnd_8128780 : Nat := 1391323758218270448188809

theorem tailTrace_8128780 : CollatzResearch.WordTrace tailWord_8128780 prefixEnd_8128780 1391323758218270448188809 := by
  unfold tailWord_8128780
  simp only [CollatzResearch.WordTrace]
  refine ⟨148240481745412909971043897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197653975660550546628058529 148240481745412909971043897)
  ·
    refine ⟨111180361309059682478282923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148240481745412909971043897 111180361309059682478282923)
    ·
      refine ⟨166770541963589523717424385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111180361309059682478282923 166770541963589523717424385)
      ·
        refine ⟨125077906472692142788068289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166770541963589523717424385 125077906472692142788068289)
        ·
          refine ⟨93808429854519107091051217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125077906472692142788068289 93808429854519107091051217)
          ·
            refine ⟨70356322390889330318288413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93808429854519107091051217 70356322390889330318288413)
            ·
              refine ⟨26383620896583498869358155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70356322390889330318288413 26383620896583498869358155)
              ·
                refine ⟨39575431344875248304037233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26383620896583498869358155 39575431344875248304037233)
                ·
                  refine ⟨29681573508656436228027925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39575431344875248304037233 29681573508656436228027925)
                  ·
                    refine ⟨1391323758218270448188809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29681573508656436228027925 1391323758218270448188809)
                    ·
                      rfl

theorem cell23_8128780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 1, 2, 6].length) (baseStart_8128780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8128780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8128780 prefixEnd_8128780 := by exact prefixLift 8128780
  have htrace : WordTrace (prefixWord ++ tailWord_8128780) baseStart_8128780 baseEnd_8128780 := by
    simpa [prefixWord, tailWord_8128780, baseEnd_8128780] using wordTrace_append hprefix tailTrace_8128780
  have hstable : (prefixWord ++ tailWord_8128780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8128780).length < 2 ^ (prefixWord ++ tailWord_8128780).sum := by decide
  have hdescent : baseEnd_8128780 < baseStart_8128780 := by decide
  rcases family_descends (prefixWord ++ tailWord_8128780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8128804 : List Nat := [2, 3, 1, 3, 1, 2, 2, 2, 1, 4, 2]
def baseStart_8128804 : Nat := 118140960795 + 8128804 * 2 ^ 59
def prefixEnd_8128804 : Nat := 4983230072969 + 3 ^ 40 * 8128804 * 2
def baseEnd_8128804 : Nat := 4173983598190519250666317

theorem tailTrace_8128804 : CollatzResearch.WordTrace tailWord_8128804 prefixEnd_8128804 4173983598190519250666317 := by
  unfold tailWord_8128804
  simp only [CollatzResearch.WordTrace]
  refine ⟨148240919421369436020480733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197654559228492581360640977 148240919421369436020480733)
  ·
    refine ⟨55590344783013538507680275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148240919421369436020480733 55590344783013538507680275)
    ·
      refine ⟨83385517174520307761520413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55590344783013538507680275 83385517174520307761520413)
      ·
        refine ⟨31269568940445115410570155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83385517174520307761520413 31269568940445115410570155)
        ·
          refine ⟨46904353410667673115855233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31269568940445115410570155 46904353410667673115855233)
          ·
            refine ⟨35178265058000754836891425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46904353410667673115855233 35178265058000754836891425)
            ·
              refine ⟨26383698793500566127668569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35178265058000754836891425 26383698793500566127668569)
              ·
                refine ⟨19787774095125424595751427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26383698793500566127668569 19787774095125424595751427)
                ·
                  refine ⟨29681661142688136893627141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19787774095125424595751427 29681661142688136893627141)
                  ·
                    refine ⟨5565311464254025667555089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29681661142688136893627141 5565311464254025667555089)
                    ·
                      refine ⟨4173983598190519250666317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5565311464254025667555089 4173983598190519250666317)
                      ·
                        rfl

theorem cell23_8128804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 2, 1, 4, 2].length) (baseStart_8128804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8128804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8128804 prefixEnd_8128804 := by exact prefixLift 8128804
  have htrace : WordTrace (prefixWord ++ tailWord_8128804) baseStart_8128804 baseEnd_8128804 := by
    simpa [prefixWord, tailWord_8128804, baseEnd_8128804] using wordTrace_append hprefix tailTrace_8128804
  have hstable : (prefixWord ++ tailWord_8128804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8128804).length < 2 ^ (prefixWord ++ tailWord_8128804).sum := by decide
  have hdescent : baseEnd_8128804 < baseStart_8128804 := by decide
  rcases family_descends (prefixWord ++ tailWord_8128804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8128840 : List Nat := [2, 1, 3, 1, 1, 2, 3, 2, 1, 7]
def baseStart_8128840 : Nat := 118140960795 + 8128840 * 2 ^ 59
def prefixEnd_8128840 : Nat := 4983230072969 + 3 ^ 40 * 8128840 * 2
def baseEnd_8128840 : Nat := 1391334027831360369938717

theorem tailTrace_8128840 : CollatzResearch.WordTrace tailWord_8128840 prefixEnd_8128840 1391334027831360369938717 := by
  unfold tailWord_8128840
  simp only [CollatzResearch.WordTrace]
  refine ⟨148241575935304225094635987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197655434580405633459514649 148241575935304225094635987)
  ·
    refine ⟨222362363902956337641953981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148241575935304225094635987 222362363902956337641953981)
    ·
      refine ⟨83385886463608626615732743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 222362363902956337641953981 83385886463608626615732743)
      ·
        refine ⟨125078829695412939923599115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83385886463608626615732743 125078829695412939923599115)
        ·
          refine ⟨187618244543119409885398673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125078829695412939923599115 187618244543119409885398673)
          ·
            refine ⟨140713683407339557414049005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 187618244543119409885398673 140713683407339557414049005)
            ·
              refine ⟨52767631277752334030268377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 140713683407339557414049005 52767631277752334030268377)
              ·
                refine ⟨39575723458314250522701283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52767631277752334030268377 39575723458314250522701283)
                ·
                  refine ⟨59363585187471375784051925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39575723458314250522701283 59363585187471375784051925)
                  ·
                    refine ⟨1391334027831360369938717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59363585187471375784051925 1391334027831360369938717)
                    ·
                      rfl

theorem cell23_8128840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 2, 1, 7].length) (baseStart_8128840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8128840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8128840 prefixEnd_8128840 := by exact prefixLift 8128840
  have htrace : WordTrace (prefixWord ++ tailWord_8128840) baseStart_8128840 baseEnd_8128840 := by
    simpa [prefixWord, tailWord_8128840, baseEnd_8128840] using wordTrace_append hprefix tailTrace_8128840
  have hstable : (prefixWord ++ tailWord_8128840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8128840).length < 2 ^ (prefixWord ++ tailWord_8128840).sum := by decide
  have hdescent : baseEnd_8128840 < baseStart_8128840 := by decide
  rcases family_descends (prefixWord ++ tailWord_8128840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8128874 : List Nat := [3, 1, 3, 3, 1, 2, 1, 2, 2, 5]
def baseStart_8128874 : Nat := 118140960795 + 8128874 * 2 ^ 59
def prefixEnd_8128874 : Nat := 4983230072969 + 3 ^ 40 * 8128874 * 2
def baseEnd_8128874 : Nat := 1391339847278777992263665

theorem tailTrace_8128874 : CollatzResearch.WordTrace tailWord_8128874 prefixEnd_8128874 1391339847278777992263665 := by
  unfold tailWord_8128874
  simp only [CollatzResearch.WordTrace]
  refine ⟨74121097988121318499002419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197656261301656849330673117 74121097988121318499002419)
  ·
    refine ⟨111181646982181977748503629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74121097988121318499002419 111181646982181977748503629)
    ·
      refine ⟨41693117618318241655688861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111181646982181977748503629 41693117618318241655688861)
      ·
        refine ⟨15634919106869340620883323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41693117618318241655688861 15634919106869340620883323)
        ·
          refine ⟨23452378660304010931324985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15634919106869340620883323 23452378660304010931324985)
          ·
            refine ⟨17589283995228008198493739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23452378660304010931324985 17589283995228008198493739)
            ·
              refine ⟨26383925992842012297740609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17589283995228008198493739 26383925992842012297740609)
              ·
                refine ⟨19787944494631509223305457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26383925992842012297740609 19787944494631509223305457)
                ·
                  refine ⟨14840958370973631917479093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19787944494631509223305457 14840958370973631917479093)
                  ·
                    refine ⟨1391339847278777992263665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14840958370973631917479093 1391339847278777992263665)
                    ·
                      rfl

theorem cell23_8128874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 2, 2, 5].length) (baseStart_8128874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8128874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8128874 prefixEnd_8128874 := by exact prefixLift 8128874
  have htrace : WordTrace (prefixWord ++ tailWord_8128874) baseStart_8128874 baseEnd_8128874 := by
    simpa [prefixWord, tailWord_8128874, baseEnd_8128874] using wordTrace_append hprefix tailTrace_8128874
  have hstable : (prefixWord ++ tailWord_8128874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8128874).length < 2 ^ (prefixWord ++ tailWord_8128874).sum := by decide
  have hdescent : baseEnd_8128874 < baseStart_8128874 := by decide
  rcases family_descends (prefixWord ++ tailWord_8128874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8128887 : List Nat := [1, 1, 3, 1, 1, 2, 2, 5, 3, 4]
def baseStart_8128887 : Nat := 118140960795 + 8128887 * 2 ^ 59
def prefixEnd_8128887 : Nat := 4983230072969 + 3 ^ 40 * 8128887 * 2
def baseEnd_8128887 : Nat := 1391342072361614141976145

theorem tailTrace_8128887 : CollatzResearch.WordTrace tailWord_8128887 prefixEnd_8128887 1391342072361614141976145 := by
  unfold tailWord_8128887
  simp only [CollatzResearch.WordTrace]
  refine ⟨296484866101438177216232915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197656577400958784810821943 296484866101438177216232915)
  ·
    refine ⟨444727299152157265824349373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296484866101438177216232915 444727299152157265824349373)
    ·
      refine ⟨166772737182058974684131015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 444727299152157265824349373 166772737182058974684131015)
      ·
        refine ⟨250159105773088462026196523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166772737182058974684131015 250159105773088462026196523)
        ·
          refine ⟨375238658659632693039294785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250159105773088462026196523 375238658659632693039294785)
          ·
            refine ⟨281428993994724519779471089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 375238658659632693039294785 281428993994724519779471089)
            ·
              refine ⟨211071745496043389834603317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 281428993994724519779471089 211071745496043389834603317)
              ·
                refine ⟨19787976140254067796994061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 211071745496043389834603317 19787976140254067796994061)
                ·
                  refine ⟨7420491052595275423872773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19787976140254067796994061 7420491052595275423872773)
                  ·
                    refine ⟨1391342072361614141976145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7420491052595275423872773 1391342072361614141976145)
                    ·
                      rfl

theorem cell23_8128887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 5, 3, 4].length) (baseStart_8128887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8128887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8128887 prefixEnd_8128887 := by exact prefixLift 8128887
  have htrace : WordTrace (prefixWord ++ tailWord_8128887) baseStart_8128887 baseEnd_8128887 := by
    simpa [prefixWord, tailWord_8128887, baseEnd_8128887] using wordTrace_append hprefix tailTrace_8128887
  have hstable : (prefixWord ++ tailWord_8128887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8128887).length < 2 ^ (prefixWord ++ tailWord_8128887).sum := by decide
  have hdescent : baseEnd_8128887 < baseStart_8128887 := by decide
  rcases family_descends (prefixWord ++ tailWord_8128887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8128954 : List Nat := [3, 1, 1, 1, 2, 1, 1, 4, 4, 3, 2]
def baseStart_8128954 : Nat := 118140960795 + 8128954 * 2 ^ 59
def prefixEnd_8128954 : Nat := 4983230072969 + 3 ^ 40 * 8128954 * 2
def baseEnd_8128954 : Nat := 4174060620288693663790627

theorem tailTrace_8128954 : CollatzResearch.WordTrace tailWord_8128954 prefixEnd_8128954 4174060620288693663790627 := by
  unfold tailWord_8128954
  simp only [CollatzResearch.WordTrace]
  refine ⟨74121827448048861914730479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197658206528130298439281277 74121827448048861914730479)
  ·
    refine ⟨111182741172073292872095719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74121827448048861914730479 111182741172073292872095719)
    ·
      refine ⟨166774111758109939308143579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111182741172073292872095719 166774111758109939308143579)
      ·
        refine ⟨250161167637164908962215369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166774111758109939308143579 250161167637164908962215369)
        ·
          refine ⟨187620875727873681721661527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 250161167637164908962215369 187620875727873681721661527)
          ·
            refine ⟨281431313591810522582492291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187620875727873681721661527 281431313591810522582492291)
            ·
              refine ⟨422146970387715783873738437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 281431313591810522582492291 422146970387715783873738437)
              ·
                refine ⟨79152556947696709476325957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 422146970387715783873738437 79152556947696709476325957)
                ·
                  refine ⟨14841104427693133026811117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79152556947696709476325957 14841104427693133026811117)
                  ·
                    refine ⟨5565414160384924885054169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14841104427693133026811117 5565414160384924885054169)
                    ·
                      refine ⟨4174060620288693663790627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5565414160384924885054169 4174060620288693663790627)
                      ·
                        rfl

theorem cell23_8128954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 4, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 4, 4, 3, 2].length) (baseStart_8128954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8128954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8128954 prefixEnd_8128954 := by exact prefixLift 8128954
  have htrace : WordTrace (prefixWord ++ tailWord_8128954) baseStart_8128954 baseEnd_8128954 := by
    simpa [prefixWord, tailWord_8128954, baseEnd_8128954] using wordTrace_append hprefix tailTrace_8128954
  have hstable : (prefixWord ++ tailWord_8128954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8128954).length < 2 ^ (prefixWord ++ tailWord_8128954).sum := by decide
  have hdescent : baseEnd_8128954 < baseStart_8128954 := by decide
  rcases family_descends (prefixWord ++ tailWord_8128954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8128981 : List Nat := [1, 3, 2, 3, 1, 2, 4, 1, 1, 5]
def baseStart_8128981 : Nat := 118140960795 + 8128981 * 2 ^ 59
def prefixEnd_8128981 : Nat := 4983230072969 + 3 ^ 40 * 8128981 * 2
def baseEnd_8128981 : Nat := 1391358161422121686051001

theorem tailTrace_8128981 : CollatzResearch.WordTrace tailWord_8128981 prefixEnd_8128981 1391358161422121686051001 := by
  unfold tailWord_8128981
  simp only [CollatzResearch.WordTrace]
  refine ⟨296488294563097631270154797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197658863042065087513436531 296488294563097631270154797)
  ·
    refine ⟨111183110461161611726308049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 296488294563097631270154797 111183110461161611726308049)
    ·
      refine ⟨83387332845871208794731037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111183110461161611726308049 83387332845871208794731037)
      ·
        refine ⟨31270249817201703298024139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83387332845871208794731037 31270249817201703298024139)
        ·
          refine ⟨46905374725802554947036209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31270249817201703298024139 46905374725802554947036209)
          ·
            refine ⟨35179031044351916210277157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46905374725802554947036209 35179031044351916210277157)
            ·
              refine ⟨6596068320815984289426967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35179031044351916210277157 6596068320815984289426967)
              ·
                refine ⟨9894102481223976434140451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6596068320815984289426967 9894102481223976434140451)
                ·
                  refine ⟨14841153721835964651210677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9894102481223976434140451 14841153721835964651210677)
                  ·
                    refine ⟨1391358161422121686051001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14841153721835964651210677 1391358161422121686051001)
                    ·
                      rfl

theorem cell23_8128981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 4, 1, 1, 5].length) (baseStart_8128981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8128981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8128981 prefixEnd_8128981 := by exact prefixLift 8128981
  have htrace : WordTrace (prefixWord ++ tailWord_8128981) baseStart_8128981 baseEnd_8128981 := by
    simpa [prefixWord, tailWord_8128981, baseEnd_8128981] using wordTrace_append hprefix tailTrace_8128981
  have hstable : (prefixWord ++ tailWord_8128981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8128981).length < 2 ^ (prefixWord ++ tailWord_8128981).sum := by decide
  have hdescent : baseEnd_8128981 < baseStart_8128981 := by decide
  rcases family_descends (prefixWord ++ tailWord_8128981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8129011 : List Nat := [1, 1, 1, 2, 2, 2, 7, 1, 2, 4]
def baseStart_8129011 : Nat := 118140960795 + 8129011 * 2 ^ 59
def prefixEnd_8129011 : Nat := 4983230072969 + 3 ^ 40 * 8129011 * 2
def baseEnd_8129011 : Nat := 1391363296228666646925955

theorem tailTrace_8129011 : CollatzResearch.WordTrace tailWord_8129011 prefixEnd_8129011 1391363296228666646925955 := by
  unfold tailWord_8129011
  simp only [CollatzResearch.WordTrace]
  refine ⟨296489388752988946393746887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197659592501992630929164591 296489388752988946393746887)
  ·
    refine ⟨444734083129483419590620331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296489388752988946393746887 444734083129483419590620331)
    ·
      refine ⟨667101124694225129385930497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 444734083129483419590620331 667101124694225129385930497)
      ·
        refine ⟨500325843520668847039447873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 667101124694225129385930497 500325843520668847039447873)
        ·
          refine ⟨375244382640501635279585905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 500325843520668847039447873 375244382640501635279585905)
          ·
            refine ⟨281433286980376226459689429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 375244382640501635279585905 281433286980376226459689429)
            ·
              refine ⟨6596092663602567807648971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 281433286980376226459689429 6596092663602567807648971)
              ·
                refine ⟨9894138995403851711473457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6596092663602567807648971 9894138995403851711473457)
                ·
                  refine ⟨7420604246552888783605093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9894138995403851711473457 7420604246552888783605093)
                  ·
                    refine ⟨1391363296228666646925955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7420604246552888783605093 1391363296228666646925955)
                    ·
                      rfl

theorem cell23_8129011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 7, 1, 2, 4].length) (baseStart_8129011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8129011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8129011 prefixEnd_8129011 := by exact prefixLift 8129011
  have htrace : WordTrace (prefixWord ++ tailWord_8129011) baseStart_8129011 baseEnd_8129011 := by
    simpa [prefixWord, tailWord_8129011, baseEnd_8129011] using wordTrace_append hprefix tailTrace_8129011
  have hstable : (prefixWord ++ tailWord_8129011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8129011).length < 2 ^ (prefixWord ++ tailWord_8129011).sum := by decide
  have hdescent : baseEnd_8129011 < baseStart_8129011 := by decide
  rcases family_descends (prefixWord ++ tailWord_8129011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8129014 : List Nat := [5, 1, 1, 1, 2, 1, 3, 1, 1, 1, 6]
def baseStart_8129014 : Nat := 118140960795 + 8129014 * 2 ^ 59
def prefixEnd_8129014 : Nat := 4983230072969 + 3 ^ 40 * 8129014 * 2
def baseEnd_8129014 : Nat := 4174091429127963429040351

theorem tailTrace_8129014 : CollatzResearch.WordTrace tailWord_8129014 prefixEnd_8129014 4174091429127963429040351 := by
  unfold tailWord_8129014
  simp only [CollatzResearch.WordTrace]
  refine ⟨18530593635748629869131631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 197659665447985385270737397 18530593635748629869131631)
  ·
    refine ⟨27795890453622944803697447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18530593635748629869131631 27795890453622944803697447)
    ·
      refine ⟨41693835680434417205546171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27795890453622944803697447 41693835680434417205546171)
      ·
        refine ⟨62540753520651625808319257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41693835680434417205546171 62540753520651625808319257)
        ·
          refine ⟨46905565140488719356239443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62540753520651625808319257 46905565140488719356239443)
          ·
            refine ⟨70358347710733079034359165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46905565140488719356239443 70358347710733079034359165)
            ·
              refine ⟨26384380391524904637884687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70358347710733079034359165 26384380391524904637884687)
              ·
                refine ⟨39576570587287356956827031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26384380391524904637884687 39576570587287356956827031)
                ·
                  refine ⟨59364855880931035435240547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39576570587287356956827031 59364855880931035435240547)
                  ·
                    refine ⟨89047283821396553152860821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59364855880931035435240547 89047283821396553152860821)
                    ·
                      refine ⟨4174091429127963429040351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 89047283821396553152860821 4174091429127963429040351)
                      ·
                        rfl

theorem cell23_8129014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 1, 1, 1, 6].length) (baseStart_8129014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8129014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8129014 prefixEnd_8129014 := by exact prefixLift 8129014
  have htrace : WordTrace (prefixWord ++ tailWord_8129014) baseStart_8129014 baseEnd_8129014 := by
    simpa [prefixWord, tailWord_8129014, baseEnd_8129014] using wordTrace_append hprefix tailTrace_8129014
  have hstable : (prefixWord ++ tailWord_8129014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8129014).length < 2 ^ (prefixWord ++ tailWord_8129014).sum := by decide
  have hdescent : baseEnd_8129014 < baseStart_8129014 := by decide
  rcases family_descends (prefixWord ++ tailWord_8129014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8129021 : List Nat := [1, 4, 1, 1, 1, 3, 4, 2, 1, 2, 3]
def baseStart_8129021 : Nat := 118140960795 + 8129021 * 2 ^ 59
def prefixEnd_8129021 : Nat := 4983230072969 + 3 ^ 40 * 8129021 * 2
def baseEnd_8129021 : Nat := 4174095023492544901652819

theorem tailTrace_8129021 : CollatzResearch.WordTrace tailWord_8129021 prefixEnd_8129021 4174095023492544901652819 := by
  unfold tailWord_8129021
  simp only [CollatzResearch.WordTrace]
  refine ⟨296489753482952718101610917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197659835655301812067740611 296489753482952718101610917)
  ·
    refine ⟨55591828778053634644052047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 296489753482952718101610917 55591828778053634644052047)
    ·
      refine ⟨83387743167080451966078071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55591828778053634644052047 83387743167080451966078071)
      ·
        refine ⟨125081614750620677949117107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83387743167080451966078071 125081614750620677949117107)
        ·
          refine ⟨187622422125931016923675661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125081614750620677949117107 187622422125931016923675661)
          ·
            refine ⟨70358408297224131346378373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 187622422125931016923675661 70358408297224131346378373)
            ·
              refine ⟨13192201555729524627445945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70358408297224131346378373 13192201555729524627445945)
              ·
                refine ⟨9894151166797143470584459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13192201555729524627445945 9894151166797143470584459)
                ·
                  refine ⟨14841226750195715205876689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9894151166797143470584459 14841226750195715205876689)
                  ·
                    refine ⟨11130920062646786404407517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14841226750195715205876689 11130920062646786404407517)
                    ·
                      refine ⟨4174095023492544901652819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11130920062646786404407517 4174095023492544901652819)
                      ·
                        rfl

theorem cell23_8129021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 4, 2, 1, 2, 3].length) (baseStart_8129021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8129021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8129021 prefixEnd_8129021 := by exact prefixLift 8129021
  have htrace : WordTrace (prefixWord ++ tailWord_8129021) baseStart_8129021 baseEnd_8129021 := by
    simpa [prefixWord, tailWord_8129021, baseEnd_8129021] using wordTrace_append hprefix tailTrace_8129021
  have hstable : (prefixWord ++ tailWord_8129021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8129021).length < 2 ^ (prefixWord ++ tailWord_8129021).sum := by decide
  have hdescent : baseEnd_8129021 < baseStart_8129021 := by decide
  rcases family_descends (prefixWord ++ tailWord_8129021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8129034 : List Nat := [3, 1, 2, 2, 2, 1, 2, 1, 3, 3, 3]
def baseStart_8129034 : Nat := 118140960795 + 8129034 * 2 ^ 59
def prefixEnd_8129034 : Nat := 4983230072969 + 3 ^ 40 * 8129034 * 2
def baseEnd_8129034 : Nat := 4174101698741053350790259

theorem tailTrace_8129034 : CollatzResearch.WordTrace tailWord_8129034 prefixEnd_8129034 4174101698741053350790259 := by
  unfold tailWord_8129034
  simp only [CollatzResearch.WordTrace]
  refine ⟨74122556907976405330458539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197660151754603747547889437 74122556907976405330458539)
  ·
    refine ⟨111183835361964607995687809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74122556907976405330458539 111183835361964607995687809)
    ·
      refine ⟨83387876521473455996765857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111183835361964607995687809 83387876521473455996765857)
      ·
        refine ⟨62540907391105091997574393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83387876521473455996765857 62540907391105091997574393)
        ·
          refine ⟨46905680543328818998180795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62540907391105091997574393 46905680543328818998180795)
          ·
            refine ⟨70358520814993228497271193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46905680543328818998180795 70358520814993228497271193)
            ·
              refine ⟨52768890611244921372953395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70358520814993228497271193 52768890611244921372953395)
              ·
                refine ⟨79153335916867382059430093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52768890611244921372953395 79153335916867382059430093)
                ·
                  refine ⟨29682500968825268272286285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79153335916867382059430093 29682500968825268272286285)
                  ·
                    refine ⟨11130937863309475602107357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29682500968825268272286285 11130937863309475602107357)
                    ·
                      refine ⟨4174101698741053350790259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11130937863309475602107357 4174101698741053350790259)
                      ·
                        rfl

theorem cell23_8129034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 1, 3, 3, 3].length) (baseStart_8129034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8129034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8129034 prefixEnd_8129034 := by exact prefixLift 8129034
  have htrace : WordTrace (prefixWord ++ tailWord_8129034) baseStart_8129034 baseEnd_8129034 := by
    simpa [prefixWord, tailWord_8129034, baseEnd_8129034] using wordTrace_append hprefix tailTrace_8129034
  have hstable : (prefixWord ++ tailWord_8129034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8129034).length < 2 ^ (prefixWord ++ tailWord_8129034).sum := by decide
  have hdescent : baseEnd_8129034 < baseStart_8129034 := by decide
  rcases family_descends (prefixWord ++ tailWord_8129034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8129035 : List Nat := [1, 1, 1, 1, 7, 1, 3, 3, 1, 2, 2]
def baseStart_8129035 : Nat := 118140960795 + 8129035 * 2 ^ 59
def prefixEnd_8129035 : Nat := 4983230072969 + 3 ^ 40 * 8129035 * 2
def baseEnd_8129035 : Nat := 4174102212221707846877755

theorem tailTrace_8129035 : CollatzResearch.WordTrace tailWord_8129035 prefixEnd_8129035 4174102212221707846877755 := by
  unfold tailWord_8129035
  simp only [CollatzResearch.WordTrace]
  refine ⟨296490264104901998492620559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197660176069934665661747039 296490264104901998492620559)
  ·
    refine ⟨444735396157352997738930839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296490264104901998492620559 444735396157352997738930839)
    ·
      refine ⟨667103094236029496608396259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 444735396157352997738930839 667103094236029496608396259)
      ·
        refine ⟨1000654641354044244912594389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 667103094236029496608396259 1000654641354044244912594389)
        ·
          refine ⟨23452843156735411990138931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 1000654641354044244912594389 23452843156735411990138931)
          ·
            refine ⟨35179264735103117985208397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23452843156735411990138931 35179264735103117985208397)
            ·
              refine ⟨13192224275663669244453149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35179264735103117985208397 13192224275663669244453149)
              ·
                refine ⟨4947084103373875966669931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13192224275663669244453149 4947084103373875966669931)
                ·
                  refine ⟨7420626155060813950004897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4947084103373875966669931 7420626155060813950004897)
                  ·
                    refine ⟨5565469616295610462503673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7420626155060813950004897 5565469616295610462503673)
                    ·
                      refine ⟨4174102212221707846877755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5565469616295610462503673 4174102212221707846877755)
                      ·
                        rfl

theorem cell23_8129035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 3, 3, 1, 2, 2].length) (baseStart_8129035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8129035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8129035 prefixEnd_8129035 := by exact prefixLift 8129035
  have htrace : WordTrace (prefixWord ++ tailWord_8129035) baseStart_8129035 baseEnd_8129035 := by
    simpa [prefixWord, tailWord_8129035, baseEnd_8129035] using wordTrace_append hprefix tailTrace_8129035
  have hstable : (prefixWord ++ tailWord_8129035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8129035).length < 2 ^ (prefixWord ++ tailWord_8129035).sum := by decide
  have hdescent : baseEnd_8129035 < baseStart_8129035 := by decide
  rcases family_descends (prefixWord ++ tailWord_8129035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8129052 : List Nat := [2, 2, 3, 1, 2, 3, 3, 2, 1, 2, 2]
def baseStart_8129052 : Nat := 118140960795 + 8129052 * 2 ^ 59
def prefixEnd_8129052 : Nat := 4983230072969 + 3 ^ 40 * 8129052 * 2
def baseEnd_8129052 : Nat := 4174110941392834280365177

theorem tailTrace_8129052 : CollatzResearch.WordTrace tailWord_8129052 prefixEnd_8129052 4174110941392834280365177 := by
  unfold tailWord_8129052
  simp only [CollatzResearch.WordTrace]
  refine ⟨148245442072920205197994705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197660589430560273597326273 148245442072920205197994705)
  ·
    refine ⟨111184081554690153898496029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148245442072920205197994705 111184081554690153898496029)
    ·
      refine ⟨41694030583008807711936011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111184081554690153898496029 41694030583008807711936011)
      ·
        refine ⟨62541045874513211567904017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41694030583008807711936011 62541045874513211567904017)
        ·
          refine ⟨46905784405884908675928013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62541045874513211567904017 46905784405884908675928013)
          ·
            refine ⟨17589669152206840753473005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46905784405884908675928013 17589669152206840753473005)
            ·
              refine ⟨6596125932077565282552377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17589669152206840753473005 6596125932077565282552377)
              ·
                refine ⟨4947094449058173961914283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6596125932077565282552377 4947094449058173961914283)
                ·
                  refine ⟨7420641673587260942871425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4947094449058173961914283 7420641673587260942871425)
                  ·
                    refine ⟨5565481255190445707153569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7420641673587260942871425 5565481255190445707153569)
                    ·
                      refine ⟨4174110941392834280365177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5565481255190445707153569 4174110941392834280365177)
                      ·
                        rfl

theorem cell23_8129052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 3, 2, 1, 2, 2].length) (baseStart_8129052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8129052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8129052 prefixEnd_8129052 := by exact prefixLift 8129052
  have htrace : WordTrace (prefixWord ++ tailWord_8129052) baseStart_8129052 baseEnd_8129052 := by
    simpa [prefixWord, tailWord_8129052, baseEnd_8129052] using wordTrace_append hprefix tailTrace_8129052
  have hstable : (prefixWord ++ tailWord_8129052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8129052).length < 2 ^ (prefixWord ++ tailWord_8129052).sum := by decide
  have hdescent : baseEnd_8129052 < baseStart_8129052 := by decide
  rcases family_descends (prefixWord ++ tailWord_8129052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8129067 : List Nat := [1, 1, 1, 1, 2, 1, 3, 5, 2, 6]
def baseStart_8129067 : Nat := 118140960795 + 8129067 * 2 ^ 59
def prefixEnd_8129067 : Nat := 4983230072969 + 3 ^ 40 * 8129067 * 2
def baseEnd_8129067 : Nat := 1391372881200883907225869

theorem tailTrace_8129067 : CollatzResearch.WordTrace tailWord_8129067 prefixEnd_8129067 1391372881200883907225869 := by
  unfold tailWord_8129067
  simp only [CollatzResearch.WordTrace]
  refine ⟨296491431240786067957785455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197660954160524045305190303 296491431240786067957785455)
  ·
    refine ⟨444737146861179101936678183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296491431240786067957785455 444737146861179101936678183)
    ·
      refine ⟨667105720291768652905017275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 444737146861179101936678183 667105720291768652905017275)
      ·
        refine ⟨1000658580437652979357525913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 667105720291768652905017275 1000658580437652979357525913)
        ·
          refine ⟨750493935328239734518144435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1000658580437652979357525913 750493935328239734518144435)
          ·
            refine ⟨1125740902992359601777216653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 750493935328239734518144435 1125740902992359601777216653)
            ·
              refine ⟨422152838622134850666456245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1125740902992359601777216653 422152838622134850666456245)
              ·
                refine ⟨39576828620825142249980273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 422152838622134850666456245 39576828620825142249980273)
                ·
                  refine ⟨29682621465618856687485205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39576828620825142249980273 29682621465618856687485205)
                  ·
                    refine ⟨1391372881200883907225869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29682621465618856687485205 1391372881200883907225869)
                    ·
                      rfl

theorem cell23_8129067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 5, 2, 6].length) (baseStart_8129067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8129067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8129067 prefixEnd_8129067 := by exact prefixLift 8129067
  have htrace : WordTrace (prefixWord ++ tailWord_8129067) baseStart_8129067 baseEnd_8129067 := by
    simpa [prefixWord, tailWord_8129067, baseEnd_8129067] using wordTrace_append hprefix tailTrace_8129067
  have hstable : (prefixWord ++ tailWord_8129067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8129067).length < 2 ^ (prefixWord ++ tailWord_8129067).sum := by decide
  have hdescent : baseEnd_8129067 < baseStart_8129067 := by decide
  rcases family_descends (prefixWord ++ tailWord_8129067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8129069 : List Nat := [1, 5, 4, 1, 2, 1, 1, 2, 1, 1, 4]
def baseStart_8129069 : Nat := 118140960795 + 8129069 * 2 ^ 59
def prefixEnd_8129069 : Nat := 4983230072969 + 3 ^ 40 * 8129069 * 2
def baseEnd_8129069 : Nat := 4174119670563960713852599

theorem tailTrace_8129069 : CollatzResearch.WordTrace tailWord_8129069 prefixEnd_8129069 4174119670563960713852599 := by
  unfold tailWord_8129069
  simp only [CollatzResearch.WordTrace]
  refine ⟨296491504186778822299358261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197661002791185881532905507 296491504186778822299358261)
  ·
    refine ⟨27796078517510514590564837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 296491504186778822299358261 27796078517510514590564837)
    ·
      refine ⟨5211764722033221485730907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27796078517510514590564837 5211764722033221485730907)
      ·
        refine ⟨7817647083049832228596361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5211764722033221485730907 7817647083049832228596361)
        ·
          refine ⟨5863235312287374171447271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7817647083049832228596361 5863235312287374171447271)
          ·
            refine ⟨8794852968431061257170907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5863235312287374171447271 8794852968431061257170907)
            ·
              refine ⟨13192279452646591885756361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8794852968431061257170907 13192279452646591885756361)
              ·
                refine ⟨9894209589484943914317271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13192279452646591885756361 9894209589484943914317271)
                ·
                  refine ⟨14841314384227415871475907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9894209589484943914317271 14841314384227415871475907)
                  ·
                    refine ⟨22261971576341123807213861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14841314384227415871475907 22261971576341123807213861)
                    ·
                      refine ⟨4174119670563960713852599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22261971576341123807213861 4174119670563960713852599)
                      ·
                        rfl

theorem cell23_8129069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 1, 2, 1, 1, 4].length) (baseStart_8129069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8129069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8129069 prefixEnd_8129069 := by exact prefixLift 8129069
  have htrace : WordTrace (prefixWord ++ tailWord_8129069) baseStart_8129069 baseEnd_8129069 := by
    simpa [prefixWord, tailWord_8129069, baseEnd_8129069] using wordTrace_append hprefix tailTrace_8129069
  have hstable : (prefixWord ++ tailWord_8129069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8129069).length < 2 ^ (prefixWord ++ tailWord_8129069).sum := by decide
  have hdescent : baseEnd_8129069 < baseStart_8129069 := by decide
  rcases family_descends (prefixWord ++ tailWord_8129069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8129091 : List Nat := [1, 1, 1, 3, 1, 2, 1, 3, 6, 2, 2]
def baseStart_8129091 : Nat := 118140960795 + 8129091 * 2 ^ 59
def prefixEnd_8129091 : Nat := 4983230072969 + 3 ^ 40 * 8129091 * 2
def baseEnd_8129091 : Nat := 4174130967138359627777497

theorem tailTrace_8129091 : CollatzResearch.WordTrace tailWord_8129091 prefixEnd_8129091 4174130967138359627777497 := by
  unfold tailWord_8129091
  simp only [CollatzResearch.WordTrace]
  refine ⟨296492306592699120056659127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197661537728466080037772751 296492306592699120056659127)
  ·
    refine ⟨444738459889048680084988691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296492306592699120056659127 444738459889048680084988691)
    ·
      refine ⟨667107689833573020127483037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 444738459889048680084988691 667107689833573020127483037)
      ·
        refine ⟨250165383687589882547806139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 667107689833573020127483037 250165383687589882547806139)
        ·
          refine ⟨375248075531384823821709209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250165383687589882547806139 375248075531384823821709209)
          ·
            refine ⟨281436056648538617866281907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 375248075531384823821709209 281436056648538617866281907)
            ·
              refine ⟨422154084972807926799422861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 281436056648538617866281907 422154084972807926799422861)
              ·
                refine ⟨158307781864802972549783573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 422154084972807926799422861 158307781864802972549783573)
                ·
                  refine ⟨7420677274912639338271105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 158307781864802972549783573 7420677274912639338271105)
                  ·
                    refine ⟨5565507956184479503703329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7420677274912639338271105 5565507956184479503703329)
                    ·
                      refine ⟨4174130967138359627777497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5565507956184479503703329 4174130967138359627777497)
                      ·
                        rfl

theorem cell23_8129091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 3, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 3, 6, 2, 2].length) (baseStart_8129091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8129091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8129091 prefixEnd_8129091 := by exact prefixLift 8129091
  have htrace : WordTrace (prefixWord ++ tailWord_8129091) baseStart_8129091 baseEnd_8129091 := by
    simpa [prefixWord, tailWord_8129091, baseEnd_8129091] using wordTrace_append hprefix tailTrace_8129091
  have hstable : (prefixWord ++ tailWord_8129091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8129091).length < 2 ^ (prefixWord ++ tailWord_8129091).sum := by decide
  have hdescent : baseEnd_8129091 < baseStart_8129091 := by decide
  rcases family_descends (prefixWord ++ tailWord_8129091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8129095 : List Nat := [1, 1, 4, 1, 4, 2, 3, 1, 1, 3, 2]
def baseStart_8129095 : Nat := 118140960795 + 8129095 * 2 ^ 59
def prefixEnd_8129095 : Nat := 4983230072969 + 3 ^ 40 * 8129095 * 2
def baseEnd_8129095 : Nat := 4174133021060977612127479

theorem tailTrace_8129095 : CollatzResearch.WordTrace tailWord_8129095 prefixEnd_8129095 4174133021060977612127479 := by
  unfold tailWord_8129095
  simp only [CollatzResearch.WordTrace]
  refine ⟨296492452484684628739804739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197661634989789752493203159 296492452484684628739804739)
  ·
    refine ⟨444738678727026943109707109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296492452484684628739804739 444738678727026943109707109)
    ·
      refine ⟨83388502261317551833070083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 444738678727026943109707109 83388502261317551833070083)
      ·
        refine ⟨125082753391976327749605125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83388502261317551833070083 125082753391976327749605125)
        ·
          refine ⟨23453016260995561453050961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 125082753391976327749605125 23453016260995561453050961)
          ·
            refine ⟨17589762195746671089788221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23453016260995561453050961 17589762195746671089788221)
            ·
              refine ⟨6596160823405001658670583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17589762195746671089788221 6596160823405001658670583)
              ·
                refine ⟨9894241235107502488005875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6596160823405001658670583 9894241235107502488005875)
                ·
                  refine ⟨14841361852661253732008813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9894241235107502488005875 14841361852661253732008813)
                  ·
                    refine ⟨5565510694747970149503305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14841361852661253732008813 5565510694747970149503305)
                    ·
                      refine ⟨4174133021060977612127479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5565510694747970149503305 4174133021060977612127479)
                      ·
                        rfl

theorem cell23_8129095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 3, 1, 1, 3, 2].length) (baseStart_8129095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8129095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8129095 prefixEnd_8129095 := by exact prefixLift 8129095
  have htrace : WordTrace (prefixWord ++ tailWord_8129095) baseStart_8129095 baseEnd_8129095 := by
    simpa [prefixWord, tailWord_8129095, baseEnd_8129095] using wordTrace_append hprefix tailTrace_8129095
  have hstable : (prefixWord ++ tailWord_8129095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8129095).length < 2 ^ (prefixWord ++ tailWord_8129095).sum := by decide
  have hdescent : baseEnd_8129095 < baseStart_8129095 := by decide
  rcases family_descends (prefixWord ++ tailWord_8129095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8129198 : List Nat := [4, 1, 4, 1, 1, 1, 2, 1, 1, 3, 4]
def baseStart_8129198 : Nat := 118140960795 + 8129198 * 2 ^ 59
def prefixEnd_8129198 : Nat := 4983230072969 + 3 ^ 40 * 8129198 * 2
def baseEnd_8129198 : Nat := 4174185909568390709139505

theorem tailTrace_8129198 : CollatzResearch.WordTrace tailWord_8129198 prefixEnd_8129198 4174185909568390709139505 := by
  unfold tailWord_8129198
  simp only [CollatzResearch.WordTrace]
  refine ⟨37062026150413934666350531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 197664139468874318220536165 37062026150413934666350531)
  ·
    refine ⟨55593039225620901999525797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37062026150413934666350531 55593039225620901999525797)
    ·
      refine ⟨10423694854803919124911087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55593039225620901999525797 10423694854803919124911087)
      ·
        refine ⟨15635542282205878687366631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10423694854803919124911087 15635542282205878687366631)
        ·
          refine ⟨23453313423308818031049947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15635542282205878687366631 23453313423308818031049947)
          ·
            refine ⟨35179970134963227046574921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23453313423308818031049947 35179970134963227046574921)
            ·
              refine ⟨26384977601222420284931191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35179970134963227046574921 26384977601222420284931191)
              ·
                refine ⟨39577466401833630427396787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26384977601222420284931191 39577466401833630427396787)
                ·
                  refine ⟨59366199602750445641095181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39577466401833630427396787 59366199602750445641095181)
                  ·
                    refine ⟨22262324851031417115410693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59366199602750445641095181 22262324851031417115410693)
                    ·
                      refine ⟨4174185909568390709139505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22262324851031417115410693 4174185909568390709139505)
                      ·
                        rfl

theorem cell23_8129198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_8129198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8129198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8129198 prefixEnd_8129198 := by exact prefixLift 8129198
  have htrace : WordTrace (prefixWord ++ tailWord_8129198) baseStart_8129198 baseEnd_8129198 := by
    simpa [prefixWord, tailWord_8129198, baseEnd_8129198] using wordTrace_append hprefix tailTrace_8129198
  have hstable : (prefixWord ++ tailWord_8129198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8129198).length < 2 ^ (prefixWord ++ tailWord_8129198).sum := by decide
  have hdescent : baseEnd_8129198 < baseStart_8129198 := by decide
  rcases family_descends (prefixWord ++ tailWord_8129198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8129265 : List Nat := [1, 2, 2, 2, 2, 2, 2, 5, 1, 1, 3]
def baseStart_8129265 : Nat := 118140960795 + 8129265 * 2 ^ 59
def prefixEnd_8129265 : Nat := 4983230072969 + 3 ^ 40 * 8129265 * 2
def baseEnd_8129265 : Nat := 4174220312772241947001697

theorem tailTrace_8129265 : CollatzResearch.WordTrace tailWord_8129265 prefixEnd_8129265 4174220312772241947001697 := by
  unfold tailWord_8129265
  simp only [CollatzResearch.WordTrace]
  refine ⟨296498652894068747773493249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197665768596045831848995499 296498652894068747773493249)
  ·
    refine ⟨222373989670551560830119937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296498652894068747773493249 222373989670551560830119937)
    ·
      refine ⟨166780492252913670622589953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222373989670551560830119937 166780492252913670622589953)
      ·
        refine ⟨125085369189685252966942465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166780492252913670622589953 125085369189685252966942465)
        ·
          refine ⟨93814026892263939725206849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125085369189685252966942465 93814026892263939725206849)
          ·
            refine ⟨70360520169197954793905137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93814026892263939725206849 70360520169197954793905137)
            ·
              refine ⟨52770390126898466095428853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70360520169197954793905137 52770390126898466095428853)
              ·
                refine ⟨4947224074396731196446455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52770390126898466095428853 4947224074396731196446455)
                ·
                  refine ⟨7420836111595096794669683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4947224074396731196446455 7420836111595096794669683)
                  ·
                    refine ⟨11131254167392645192004525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7420836111595096794669683 11131254167392645192004525)
                    ·
                      refine ⟨4174220312772241947001697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11131254167392645192004525 4174220312772241947001697)
                      ·
                        rfl

theorem cell23_8129265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 5, 1, 1, 3].length) (baseStart_8129265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8129265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8129265 prefixEnd_8129265 := by exact prefixLift 8129265
  have htrace : WordTrace (prefixWord ++ tailWord_8129265) baseStart_8129265 baseEnd_8129265 := by
    simpa [prefixWord, tailWord_8129265, baseEnd_8129265] using wordTrace_append hprefix tailTrace_8129265
  have hstable : (prefixWord ++ tailWord_8129265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8129265).length < 2 ^ (prefixWord ++ tailWord_8129265).sum := by decide
  have hdescent : baseEnd_8129265 < baseStart_8129265 := by decide
  rcases family_descends (prefixWord ++ tailWord_8129265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8129308 : List Nat := [2, 2, 3, 1, 1, 3, 2, 1, 3, 2, 3]
def baseStart_8129308 : Nat := 118140960795 + 8129308 * 2 ^ 59
def prefixEnd_8129308 : Nat := 4983230072969 + 3 ^ 40 * 8129308 * 2
def baseEnd_8129308 : Nat := 4174242392440385278763999

theorem tailTrace_8129308 : CollatzResearch.WordTrace tailWord_8129308 prefixEnd_8129308 4174242392440385278763999 := by
  unfold tailWord_8129308
  simp only [CollatzResearch.WordTrace]
  refine ⟨148250110616456483058654289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197666814155275310744872385 148250110616456483058654289)
  ·
    refine ⟨111187582962342362293990717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148250110616456483058654289 111187582962342362293990717)
    ·
      refine ⟨41695343610878385860246519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111187582962342362293990717 41695343610878385860246519)
      ·
        refine ⟨62543015416317578790369779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41695343610878385860246519 62543015416317578790369779)
        ·
          refine ⟨93814523124476368185554669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62543015416317578790369779 93814523124476368185554669)
          ·
            refine ⟨35180446171678638069583001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93814523124476368185554669 35180446171678638069583001)
            ·
              refine ⟨26385334628758978552187251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35180446171678638069583001 26385334628758978552187251)
              ·
                refine ⟨39578001943138467828280877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26385334628758978552187251 39578001943138467828280877)
                ·
                  refine ⟨14841750728676925435605329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39578001943138467828280877 14841750728676925435605329)
                  ·
                    refine ⟨11131313046507694076703997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14841750728676925435605329 11131313046507694076703997)
                    ·
                      refine ⟨4174242392440385278763999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11131313046507694076703997 4174242392440385278763999)
                      ·
                        rfl

theorem cell23_8129308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 1, 3, 2, 3].length) (baseStart_8129308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8129308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8129308 prefixEnd_8129308 := by exact prefixLift 8129308
  have htrace : WordTrace (prefixWord ++ tailWord_8129308) baseStart_8129308 baseEnd_8129308 := by
    simpa [prefixWord, tailWord_8129308, baseEnd_8129308] using wordTrace_append hprefix tailTrace_8129308
  have hstable : (prefixWord ++ tailWord_8129308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8129308).length < 2 ^ (prefixWord ++ tailWord_8129308).sum := by decide
  have hdescent : baseEnd_8129308 < baseStart_8129308 := by decide
  rcases family_descends (prefixWord ++ tailWord_8129308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8129309 : List Nat := [1, 4, 2, 4, 1, 2, 1, 1, 2, 3, 2]
def baseStart_8129309 : Nat := 118140960795 + 8129309 * 2 ^ 59
def prefixEnd_8129309 : Nat := 4983230072969 + 3 ^ 40 * 8129309 * 2
def baseEnd_8129309 : Nat := 4174242905921039774851495

theorem tailTrace_8129309 : CollatzResearch.WordTrace tailWord_8129309 prefixEnd_8129309 4174242905921039774851495 := by
  unfold tailWord_8129309
  simp only [CollatzResearch.WordTrace]
  refine ⟨296500257705909343288094981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197666838470606228858729987 296500257705909343288094981)
  ·
    refine ⟨55593798319858001866517809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 296500257705909343288094981 55593798319858001866517809)
    ·
      refine ⟨41695348739893501399888357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55593798319858001866517809 41695348739893501399888357)
      ·
        refine ⟨7817877888730031512479067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41695348739893501399888357 7817877888730031512479067)
        ·
          refine ⟨11726816833095047268718601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7817877888730031512479067 11726816833095047268718601)
          ·
            refine ⟨8795112624821285451538951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11726816833095047268718601 8795112624821285451538951)
            ·
              refine ⟨13192668937231928177308427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8795112624821285451538951 13192668937231928177308427)
              ·
                refine ⟨19789003405847892265962641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13192668937231928177308427 19789003405847892265962641)
                ·
                  refine ⟨14841752554385919199471981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19789003405847892265962641 14841752554385919199471981)
                  ·
                    refine ⟨5565657207894719699801993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14841752554385919199471981 5565657207894719699801993)
                    ·
                      refine ⟨4174242905921039774851495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5565657207894719699801993 4174242905921039774851495)
                      ·
                        rfl

theorem cell23_8129309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 1, 1, 2, 3, 2].length) (baseStart_8129309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8129309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8129309 prefixEnd_8129309 := by exact prefixLift 8129309
  have htrace : WordTrace (prefixWord ++ tailWord_8129309) baseStart_8129309 baseEnd_8129309 := by
    simpa [prefixWord, tailWord_8129309, baseEnd_8129309] using wordTrace_append hprefix tailTrace_8129309
  have hstable : (prefixWord ++ tailWord_8129309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8129309).length < 2 ^ (prefixWord ++ tailWord_8129309).sum := by decide
  have hdescent : baseEnd_8129309 < baseStart_8129309 := by decide
  rcases family_descends (prefixWord ++ tailWord_8129309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8129322 : List Nat := [3, 1, 4, 3, 1, 1, 1, 3, 1, 1, 4]
def baseStart_8129322 : Nat := 118140960795 + 8129322 * 2 ^ 59
def prefixEnd_8129322 : Nat := 4983230072969 + 3 ^ 40 * 8129322 * 2
def baseEnd_8129322 : Nat := 4174249581169548223988935

theorem tailTrace_8129322 : CollatzResearch.WordTrace tailWord_8129322 prefixEnd_8129322 4174249581169548223988935 := by
  unfold tailWord_8129322
  simp only [CollatzResearch.WordTrace]
  refine ⟨74125182963715561627079555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197667154569908164338878813 74125182963715561627079555)
  ·
    refine ⟨111187774445573342440619333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74125182963715561627079555 111187774445573342440619333)
    ·
      refine ⟨20847707708545001707616125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 111187774445573342440619333 20847707708545001707616125)
      ·
        refine ⟨7817890390704375640356047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20847707708545001707616125 7817890390704375640356047)
        ·
          refine ⟨11726835586056563460534071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7817890390704375640356047 11726835586056563460534071)
          ·
            refine ⟨17590253379084845190801107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11726835586056563460534071 17590253379084845190801107)
            ·
              refine ⟨26385380068627267786201661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17590253379084845190801107 26385380068627267786201661)
              ·
                refine ⟨9894517525735225419825623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26385380068627267786201661 9894517525735225419825623)
                ·
                  refine ⟨14841776288602838129738435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9894517525735225419825623 14841776288602838129738435)
                  ·
                    refine ⟨22262664432904257194607653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14841776288602838129738435 22262664432904257194607653)
                    ·
                      refine ⟨4174249581169548223988935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22262664432904257194607653 4174249581169548223988935)
                      ·
                        rfl

theorem cell23_8129322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_8129322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8129322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8129322 prefixEnd_8129322 := by exact prefixLift 8129322
  have htrace : WordTrace (prefixWord ++ tailWord_8129322) baseStart_8129322 baseEnd_8129322 := by
    simpa [prefixWord, tailWord_8129322, baseEnd_8129322] using wordTrace_append hprefix tailTrace_8129322
  have hstable : (prefixWord ++ tailWord_8129322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8129322).length < 2 ^ (prefixWord ++ tailWord_8129322).sum := by decide
  have hdescent : baseEnd_8129322 < baseStart_8129322 := by decide
  rcases family_descends (prefixWord ++ tailWord_8129322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8129381 : List Nat := [1, 3, 1, 3, 1, 1, 3, 1, 1, 3, 5]
def baseStart_8129381 : Nat := 118140960795 + 8129381 * 2 ^ 59
def prefixEnd_8129381 : Nat := 4983230072969 + 3 ^ 40 * 8129381 * 2
def baseEnd_8129381 : Nat := 4174279876528163493151163

theorem tailTrace_8129381 : CollatzResearch.WordTrace tailWord_8129381 prefixEnd_8129381 4174279876528163493151163 := by
  unfold tailWord_8129381
  simp only [CollatzResearch.WordTrace]
  refine ⟨296502883761648499584715997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197668589174432333056477331 296502883761648499584715997)
  ·
    refine ⟨111188581410618187344268499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 296502883761648499584715997 111188581410618187344268499)
    ·
      refine ⟨166782872115927281016402749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111188581410618187344268499 166782872115927281016402749)
      ·
        refine ⟨62543577043472730381151031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166782872115927281016402749 62543577043472730381151031)
        ·
          refine ⟨93815365565209095571726547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62543577043472730381151031 93815365565209095571726547)
          ·
            refine ⟨140723048347813643357589821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93815365565209095571726547 140723048347813643357589821)
            ·
              refine ⟨52771143130430116259096183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 140723048347813643357589821 52771143130430116259096183)
              ·
                refine ⟨79156714695645174388644275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52771143130430116259096183 79156714695645174388644275)
                ·
                  refine ⟨118735072043467761582966413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79156714695645174388644275 118735072043467761582966413)
                  ·
                    refine ⟨44525652016300410593612405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 118735072043467761582966413 44525652016300410593612405)
                    ·
                      refine ⟨4174279876528163493151163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44525652016300410593612405 4174279876528163493151163)
                      ·
                        rfl

theorem cell23_8129381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 1, 1, 3, 5].length) (baseStart_8129381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8129381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8129381 prefixEnd_8129381 := by exact prefixLift 8129381
  have htrace : WordTrace (prefixWord ++ tailWord_8129381) baseStart_8129381 baseEnd_8129381 := by
    simpa [prefixWord, tailWord_8129381, baseEnd_8129381] using wordTrace_append hprefix tailTrace_8129381
  have hstable : (prefixWord ++ tailWord_8129381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8129381).length < 2 ^ (prefixWord ++ tailWord_8129381).sum := by decide
  have hdescent : baseEnd_8129381 < baseStart_8129381 := by decide
  rcases family_descends (prefixWord ++ tailWord_8129381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8129391 : List Nat := [1, 1, 2, 1, 3, 1, 1, 3, 4, 2, 4]
def baseStart_8129391 : Nat := 118140960795 + 8129391 * 2 ^ 59
def prefixEnd_8129391 : Nat := 4983230072969 + 3 ^ 40 * 8129391 * 2
def baseEnd_8129391 : Nat := 4174285011334708454026117

theorem tailTrace_8129391 : CollatzResearch.WordTrace tailWord_8129391 prefixEnd_8129391 4174285011334708454026117 := by
  unfold tailWord_8129391
  simp only [CollatzResearch.WordTrace]
  refine ⟨296503248491612271292580027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197668832327741514195053351 296503248491612271292580027)
  ·
    refine ⟨444754872737418406938870041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296503248491612271292580027 444754872737418406938870041)
    ·
      refine ⟨333566154553063805204152531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 444754872737418406938870041 333566154553063805204152531)
      ·
        refine ⟨500349231829595707806228797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 333566154553063805204152531 500349231829595707806228797)
        ·
          refine ⟨187630961936098390427335799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 500349231829595707806228797 187630961936098390427335799)
          ·
            refine ⟨281446442904147585641003699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187630961936098390427335799 281446442904147585641003699)
            ·
              refine ⟨422169664356221378461505549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 281446442904147585641003699 422169664356221378461505549)
              ·
                refine ⟨158313624133583016923064581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 422169664356221378461505549 158313624133583016923064581)
                ·
                  refine ⟨29683804525046815673074609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 158313624133583016923064581 29683804525046815673074609)
                  ·
                    refine ⟨22262853393785111754805957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29683804525046815673074609 22262853393785111754805957)
                    ·
                      refine ⟨4174285011334708454026117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22262853393785111754805957 4174285011334708454026117)
                      ·
                        rfl

theorem cell23_8129391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 3, 4, 2, 4].length) (baseStart_8129391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8129391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8129391 prefixEnd_8129391 := by exact prefixLift 8129391
  have htrace : WordTrace (prefixWord ++ tailWord_8129391) baseStart_8129391 baseEnd_8129391 := by
    simpa [prefixWord, tailWord_8129391, baseEnd_8129391] using wordTrace_append hprefix tailTrace_8129391
  have hstable : (prefixWord ++ tailWord_8129391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8129391).length < 2 ^ (prefixWord ++ tailWord_8129391).sum := by decide
  have hdescent : baseEnd_8129391 < baseStart_8129391 := by decide
  rcases family_descends (prefixWord ++ tailWord_8129391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8129395 : List Nat := [1, 1, 1, 2, 2, 1, 6, 1, 4, 2, 2]
def baseStart_8129395 : Nat := 118140960795 + 8129395 * 2 ^ 59
def prefixEnd_8129395 : Nat := 4983230072969 + 3 ^ 40 * 8129395 * 2
def baseEnd_8129395 : Nat := 4174287065257326438376099

theorem tailTrace_8129395 : CollatzResearch.WordTrace tailWord_8129395 prefixEnd_8129395 4174287065257326438376099 := by
  unfold tailWord_8129395
  simp only [CollatzResearch.WordTrace]
  refine ⟨296503394383597779975725639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197668929589065186650483759 296503394383597779975725639)
  ·
    refine ⟨444755091575396669963588459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296503394383597779975725639 444755091575396669963588459)
    ·
      refine ⟨667132637363095004945382689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 444755091575396669963588459 667132637363095004945382689)
      ·
        refine ⟨500349478022321253709037017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 667132637363095004945382689 500349478022321253709037017)
        ·
          refine ⟨375262108516740940281777763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 500349478022321253709037017 375262108516740940281777763)
          ·
            refine ⟨562893162775111410422666645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 375262108516740940281777763 562893162775111410422666645)
            ·
              refine ⟨26385617005083347363562499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 562893162775111410422666645 26385617005083347363562499)
              ·
                refine ⟨39578425507625021045343749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26385617005083347363562499 39578425507625021045343749)
                ·
                  refine ⟨7420954782679691446001953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39578425507625021045343749 7420954782679691446001953)
                  ·
                    refine ⟨5565716087009768584501465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7420954782679691446001953 5565716087009768584501465)
                    ·
                      refine ⟨4174287065257326438376099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5565716087009768584501465 4174287065257326438376099)
                      ·
                        rfl

theorem cell23_8129395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 1, 4, 2, 2].length) (baseStart_8129395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8129395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8129395 prefixEnd_8129395 := by exact prefixLift 8129395
  have htrace : WordTrace (prefixWord ++ tailWord_8129395) baseStart_8129395 baseEnd_8129395 := by
    simpa [prefixWord, tailWord_8129395, baseEnd_8129395] using wordTrace_append hprefix tailTrace_8129395
  have hstable : (prefixWord ++ tailWord_8129395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8129395).length < 2 ^ (prefixWord ++ tailWord_8129395).sum := by decide
  have hdescent : baseEnd_8129395 < baseStart_8129395 := by decide
  rcases family_descends (prefixWord ++ tailWord_8129395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8129481 : List Nat := [1, 2, 1, 1, 2, 1, 2, 1, 3, 3, 6]
def baseStart_8129481 : Nat := 118140960795 + 8129481 * 2 ^ 59
def prefixEnd_8129481 : Nat := 4983230072969 + 3 ^ 40 * 8129481 * 2
def baseEnd_8129481 : Nat := 4174331224593613101900703

theorem tailTrace_8129481 : CollatzResearch.WordTrace tailWord_8129481 prefixEnd_8129481 4174331224593613101900703 := by
  unfold tailWord_8129481
  simp only [CollatzResearch.WordTrace]
  refine ⟨296506531061286216663356297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197671020707524144442237531 296506531061286216663356297)
  ·
    refine ⟨222379898295964662497517223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296506531061286216663356297 222379898295964662497517223)
    ·
      refine ⟨333569847443946993746275835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222379898295964662497517223 333569847443946993746275835)
      ·
        refine ⟨500354771165920490619413753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 333569847443946993746275835 500354771165920490619413753)
        ·
          refine ⟨375266078374440367964560315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 500354771165920490619413753 375266078374440367964560315)
          ·
            refine ⟨562899117561660551946840473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 375266078374440367964560315 562899117561660551946840473)
            ·
              refine ⟨422174338171245413960130355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 562899117561660551946840473 422174338171245413960130355)
              ·
                refine ⟨633261507256868120940195533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 422174338171245413960130355 633261507256868120940195533)
                ·
                  refine ⟨237473065221325545352573325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 633261507256868120940195533 237473065221325545352573325)
                  ·
                    refine ⟨89052399457997079507214997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 237473065221325545352573325 89052399457997079507214997)
                    ·
                      refine ⟨4174331224593613101900703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 89052399457997079507214997 4174331224593613101900703)
                      ·
                        rfl

theorem cell23_8129481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 3, 3, 6].length) (baseStart_8129481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8129481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8129481 prefixEnd_8129481 := by exact prefixLift 8129481
  have htrace : WordTrace (prefixWord ++ tailWord_8129481) baseStart_8129481 baseEnd_8129481 := by
    simpa [prefixWord, tailWord_8129481, baseEnd_8129481] using wordTrace_append hprefix tailTrace_8129481
  have hstable : (prefixWord ++ tailWord_8129481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8129481).length < 2 ^ (prefixWord ++ tailWord_8129481).sum := by decide
  have hdescent : baseEnd_8129481 < baseStart_8129481 := by decide
  rcases family_descends (prefixWord ++ tailWord_8129481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8129498 : List Nat := [3, 1, 1, 2, 4, 1, 1, 1, 2, 1, 6]
def baseStart_8129498 : Nat := 118140960795 + 8129498 * 2 ^ 59
def prefixEnd_8129498 : Nat := 4983230072969 + 3 ^ 40 * 8129498 * 2
def baseEnd_8129498 : Nat := 4174339953764739535388125

theorem tailTrace_8129498 : CollatzResearch.WordTrace tailWord_8129498 prefixEnd_8129498 4174339953764739535388125 := by
  unfold tailWord_8129498
  simp only [CollatzResearch.WordTrace]
  refine ⟨74126787775556157141681287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197671434068149752377816765 74126787775556157141681287)
  ·
    refine ⟨111190181663334235712521931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74126787775556157141681287 111190181663334235712521931)
    ·
      refine ⟨166785272495001353568782897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111190181663334235712521931 166785272495001353568782897)
      ·
        refine ⟨125088954371251015176587173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166785272495001353568782897 125088954371251015176587173)
        ·
          refine ⟨23454178944609565345610095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 125088954371251015176587173 23454178944609565345610095)
          ·
            refine ⟨35181268416914348018415143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23454178944609565345610095 35181268416914348018415143)
            ·
              refine ⟨52771902625371522027622715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35181268416914348018415143 52771902625371522027622715)
              ·
                refine ⟨79157853938057283041434073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52771902625371522027622715 79157853938057283041434073)
                ·
                  refine ⟨59368390453542962281075555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79157853938057283041434073 59368390453542962281075555)
                  ·
                    refine ⟨89052585680314443421613333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59368390453542962281075555 89052585680314443421613333)
                    ·
                      refine ⟨4174339953764739535388125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 89052585680314443421613333 4174339953764739535388125)
                      ·
                        rfl

theorem cell23_8129498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 1, 2, 1, 6].length) (baseStart_8129498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8129498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8129498 prefixEnd_8129498 := by exact prefixLift 8129498
  have htrace : WordTrace (prefixWord ++ tailWord_8129498) baseStart_8129498 baseEnd_8129498 := by
    simpa [prefixWord, tailWord_8129498, baseEnd_8129498] using wordTrace_append hprefix tailTrace_8129498
  have hstable : (prefixWord ++ tailWord_8129498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8129498).length < 2 ^ (prefixWord ++ tailWord_8129498).sum := by decide
  have hdescent : baseEnd_8129498 < baseStart_8129498 := by decide
  rcases family_descends (prefixWord ++ tailWord_8129498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8129508 : List Nat := [2, 3, 1, 1, 1, 1, 2, 6, 6]
def baseStart_8129508 : Nat := 118140960795 + 8129508 * 2 ^ 59
def prefixEnd_8129508 : Nat := 4983230072969 + 3 ^ 40 * 8129508 * 2
def baseEnd_8129508 : Nat := 463816120952364944029231

theorem tailTrace_8129508 : CollatzResearch.WordTrace tailWord_8129508 prefixEnd_8129508 463816120952364944029231 := by
  unfold tailWord_8129508
  simp only [CollatzResearch.WordTrace]
  refine ⟨148253757916094200137294589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197671677221458933516392785 148253757916094200137294589)
  ·
    refine ⟨55595159218535325051485471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148253757916094200137294589 55595159218535325051485471)
    ·
      refine ⟨83392738827802987577228207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55595159218535325051485471 83392738827802987577228207)
      ·
        refine ⟨125089108241704481365842311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83392738827802987577228207 125089108241704481365842311)
        ·
          refine ⟨187633662362556722048763467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125089108241704481365842311 187633662362556722048763467)
          ·
            refine ⟨281450493543835083073145201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187633662362556722048763467 281450493543835083073145201)
            ·
              refine ⟨211087870157876312304858901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 281450493543835083073145201 211087870157876312304858901)
              ·
                refine ⟨9894743913650452139290261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 211087870157876312304858901 9894743913650452139290261)
                ·
                  refine ⟨463816120952364944029231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9894743913650452139290261 463816120952364944029231)
                  ·
                    rfl

theorem cell23_8129508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 6, 6].length) (baseStart_8129508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8129508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8129508 prefixEnd_8129508 := by exact prefixLift 8129508
  have htrace : WordTrace (prefixWord ++ tailWord_8129508) baseStart_8129508 baseEnd_8129508 := by
    simpa [prefixWord, tailWord_8129508, baseEnd_8129508] using wordTrace_append hprefix tailTrace_8129508
  have hstable : (prefixWord ++ tailWord_8129508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8129508).length < 2 ^ (prefixWord ++ tailWord_8129508).sum := by decide
  have hdescent : baseEnd_8129508 < baseStart_8129508 := by decide
  rcases family_descends (prefixWord ++ tailWord_8129508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8129512 : List Nat := [2, 1, 4, 1, 1, 1, 4, 4, 1, 4]
def baseStart_8129512 : Nat := 118140960795 + 8129512 * 2 ^ 59
def prefixEnd_8129512 : Nat := 4983230072969 + 3 ^ 40 * 8129512 * 2
def baseEnd_8129512 : Nat := 1391449047497967493537687

theorem tailTrace_8129512 : CollatzResearch.WordTrace tailWord_8129512 prefixEnd_8129512 1391449047497967493537687 := by
  unfold tailWord_8129512
  simp only [CollatzResearch.WordTrace]
  refine ⟨148253830862086954478867395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197671774482782605971823193 148253830862086954478867395)
  ·
    refine ⟨222380746293130431718301093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148253830862086954478867395 222380746293130431718301093)
    ·
      refine ⟨41696389929961955947181455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 222380746293130431718301093 41696389929961955947181455)
      ·
        refine ⟨62544584894942933920772183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41696389929961955947181455 62544584894942933920772183)
        ·
          refine ⟨93816877342414400881158275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62544584894942933920772183 93816877342414400881158275)
          ·
            refine ⟨140725316013621601321737413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93816877342414400881158275 140725316013621601321737413)
            ·
              refine ⟨26385996752554050247825765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 140725316013621601321737413 26385996752554050247825765)
              ·
                refine ⟨4947374391103884421467331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26385996752554050247825765 4947374391103884421467331)
                ·
                  refine ⟨7421061586655826632200997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4947374391103884421467331 7421061586655826632200997)
                  ·
                    refine ⟨1391449047497967493537687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7421061586655826632200997 1391449047497967493537687)
                    ·
                      rfl

theorem cell23_8129512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 4, 1, 4].length) (baseStart_8129512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8129512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8129512 prefixEnd_8129512 := by exact prefixLift 8129512
  have htrace : WordTrace (prefixWord ++ tailWord_8129512) baseStart_8129512 baseEnd_8129512 := by
    simpa [prefixWord, tailWord_8129512, baseEnd_8129512] using wordTrace_append hprefix tailTrace_8129512
  have hstable : (prefixWord ++ tailWord_8129512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8129512).length < 2 ^ (prefixWord ++ tailWord_8129512).sum := by decide
  have hdescent : baseEnd_8129512 < baseStart_8129512 := by decide
  rcases family_descends (prefixWord ++ tailWord_8129512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8129545 : List Nat := [1, 2, 1, 1, 3, 1, 1, 2, 6, 3, 2]
def baseStart_8129545 : Nat := 118140960795 + 8129545 * 2 ^ 59
def prefixEnd_8129545 : Nat := 4983230072969 + 3 ^ 40 * 8129545 * 2
def baseEnd_8129545 : Nat := 4174364087355500851500409

theorem tailTrace_8129545 : CollatzResearch.WordTrace tailWord_8129545 prefixEnd_8129545 4174364087355500851500409 := by
  unfold tailWord_8129545
  simp only [CollatzResearch.WordTrace]
  refine ⟨296508865333054355593686089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197672576888702903729124059 296508865333054355593686089)
  ·
    refine ⟨222381648999790766695264567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296508865333054355593686089 222381648999790766695264567)
    ·
      refine ⟨333572473499686150042896851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222381648999790766695264567 333572473499686150042896851)
      ·
        refine ⟨500358710249529225064345277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 333572473499686150042896851 500358710249529225064345277)
        ·
          refine ⟨187634516343573459399129479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 500358710249529225064345277 187634516343573459399129479)
          ·
            refine ⟨281451774515360189098694219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187634516343573459399129479 281451774515360189098694219)
            ·
              refine ⟨422177661773040283648041329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 281451774515360189098694219 422177661773040283648041329)
              ·
                refine ⟨316633246329780212736030997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 422177661773040283648041329 316633246329780212736030997)
                ·
                  refine ⟨14842183421708447472001453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 316633246329780212736030997 14842183421708447472001453)
                  ·
                    refine ⟨5565818783140667802000545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14842183421708447472001453 5565818783140667802000545)
                    ·
                      refine ⟨4174364087355500851500409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5565818783140667802000545 4174364087355500851500409)
                      ·
                        rfl

theorem cell23_8129545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 2, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 2, 6, 3, 2].length) (baseStart_8129545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8129545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8129545 prefixEnd_8129545 := by exact prefixLift 8129545
  have htrace : WordTrace (prefixWord ++ tailWord_8129545) baseStart_8129545 baseEnd_8129545 := by
    simpa [prefixWord, tailWord_8129545, baseEnd_8129545] using wordTrace_append hprefix tailTrace_8129545
  have hstable : (prefixWord ++ tailWord_8129545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8129545).length < 2 ^ (prefixWord ++ tailWord_8129545).sum := by decide
  have hdescent : baseEnd_8129545 < baseStart_8129545 := by decide
  rcases family_descends (prefixWord ++ tailWord_8129545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8129562 : List Nat := [3, 1, 1, 3, 1, 2, 3, 2, 2, 3, 2]
def baseStart_8129562 : Nat := 118140960795 + 8129562 * 2 ^ 59
def prefixEnd_8129562 : Nat := 4983230072969 + 3 ^ 40 * 8129562 * 2
def baseEnd_8129562 : Nat := 4174372816526627284987831

theorem tailTrace_8129562 : CollatzResearch.WordTrace tailWord_8129562 prefixEnd_8129562 4174372816526627284987831 := by
  unfold tailWord_8129562
  simp only [CollatzResearch.WordTrace]
  refine ⟨74127371343498191874263735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197672990249328511664703293 74127371343498191874263735)
  ·
    refine ⟨111191057015247287811395603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74127371343498191874263735 111191057015247287811395603)
    ·
      refine ⟨166786585522870931717093405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111191057015247287811395603 166786585522870931717093405)
      ·
        refine ⟨62544969571076599393910027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166786585522870931717093405 62544969571076599393910027)
        ·
          refine ⟨93817454356614899090865041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62544969571076599393910027 93817454356614899090865041)
          ·
            refine ⟨70363090767461174318148781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93817454356614899090865041 70363090767461174318148781)
            ·
              refine ⟨26386159037797940369305793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70363090767461174318148781 26386159037797940369305793)
              ·
                refine ⟨19789619278348455276979345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26386159037797940369305793 19789619278348455276979345)
                ·
                  refine ⟨14842214458761341457734509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19789619278348455276979345 14842214458761341457734509)
                  ·
                    refine ⟨5565830422035503046650441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14842214458761341457734509 5565830422035503046650441)
                    ·
                      refine ⟨4174372816526627284987831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5565830422035503046650441 4174372816526627284987831)
                      ·
                        rfl

theorem cell23_8129562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 2, 2, 3, 2].length) (baseStart_8129562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8129562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8129562 prefixEnd_8129562 := by exact prefixLift 8129562
  have htrace : WordTrace (prefixWord ++ tailWord_8129562) baseStart_8129562 baseEnd_8129562 := by
    simpa [prefixWord, tailWord_8129562, baseEnd_8129562] using wordTrace_append hprefix tailTrace_8129562
  have hstable : (prefixWord ++ tailWord_8129562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8129562).length < 2 ^ (prefixWord ++ tailWord_8129562).sum := by decide
  have hdescent : baseEnd_8129562 < baseStart_8129562 := by decide
  rcases family_descends (prefixWord ++ tailWord_8129562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8129569 : List Nat := [1, 2, 3, 2, 3, 3, 1, 1, 3, 1, 3]
def baseStart_8129569 : Nat := 118140960795 + 8129569 * 2 ^ 59
def prefixEnd_8129569 : Nat := 4983230072969 + 3 ^ 40 * 8129569 * 2
def baseEnd_8129569 : Nat := 4174376410891208757600299

theorem tailTrace_8129569 : CollatzResearch.WordTrace tailWord_8129569 prefixEnd_8129569 4174376410891208757600299 := by
  unfold tailWord_8129569
  simp only [CollatzResearch.WordTrace]
  refine ⟨296509740684967407692559761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197673160456644938461706507 296509740684967407692559761)
  ·
    refine ⟨222382305513725555769419821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296509740684967407692559761 222382305513725555769419821)
    ·
      refine ⟨83393364567647083413532433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 222382305513725555769419821 83393364567647083413532433)
      ·
        refine ⟨62545023425735312560149325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83393364567647083413532433 62545023425735312560149325)
        ·
          refine ⟨23454383784650742210055997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62545023425735312560149325 23454383784650742210055997)
          ·
            refine ⟨8795393919244028328770999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23454383784650742210055997 8795393919244028328770999)
            ·
              refine ⟨13193090878866042493156499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8795393919244028328770999 13193090878866042493156499)
              ·
                refine ⟨19789636318299063739734749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13193090878866042493156499 19789636318299063739734749)
                ·
                  refine ⟨7421113619362148902400531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19789636318299063739734749 7421113619362148902400531)
                  ·
                    refine ⟨11131670429043223353600797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7421113619362148902400531 11131670429043223353600797)
                    ·
                      refine ⟨4174376410891208757600299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11131670429043223353600797 4174376410891208757600299)
                      ·
                        rfl

theorem cell23_8129569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 1, 1, 3, 1, 3].length) (baseStart_8129569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8129569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8129569 prefixEnd_8129569 := by exact prefixLift 8129569
  have htrace : WordTrace (prefixWord ++ tailWord_8129569) baseStart_8129569 baseEnd_8129569 := by
    simpa [prefixWord, tailWord_8129569, baseEnd_8129569] using wordTrace_append hprefix tailTrace_8129569
  have hstable : (prefixWord ++ tailWord_8129569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8129569).length < 2 ^ (prefixWord ++ tailWord_8129569).sum := by decide
  have hdescent : baseEnd_8129569 < baseStart_8129569 := by decide
  rcases family_descends (prefixWord ++ tailWord_8129569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8129592 : List Nat := [2, 1, 2, 1, 5, 1, 3, 2, 1, 1, 4]
def baseStart_8129592 : Nat := 118140960795 + 8129592 * 2 ^ 59
def prefixEnd_8129592 : Nat := 4983230072969 + 3 ^ 40 * 8129592 * 2
def baseEnd_8129592 : Nat := 4174388220946262167612693

theorem tailTrace_8129592 : CollatzResearch.WordTrace tailWord_8129592 prefixEnd_8129592 4174388220946262167612693 := by
  unfold tailWord_8129592
  simp only [CollatzResearch.WordTrace]
  refine ⟨148255289781942041310323515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197673719709256055080431353 148255289781942041310323515)
  ·
    refine ⟨222382934672913061965485273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148255289781942041310323515 222382934672913061965485273)
    ·
      refine ⟨166787201004684796474113955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222382934672913061965485273 166787201004684796474113955)
      ·
        refine ⟨250180801507027194711170933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166787201004684796474113955 250180801507027194711170933)
        ·
          refine ⟨23454450141283799504172275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 250180801507027194711170933 23454450141283799504172275)
          ·
            refine ⟨35181675211925699256258413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23454450141283799504172275 35181675211925699256258413)
            ·
              refine ⟨13193128204472137221096905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35181675211925699256258413 13193128204472137221096905)
              ·
                refine ⟨9894846153354102915822679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13193128204472137221096905 9894846153354102915822679)
                ·
                  refine ⟨14842269230031154373734019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9894846153354102915822679 14842269230031154373734019)
                  ·
                    refine ⟨22263403845046731560601029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14842269230031154373734019 22263403845046731560601029)
                    ·
                      refine ⟨4174388220946262167612693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22263403845046731560601029 4174388220946262167612693)
                      ·
                        rfl

theorem cell23_8129592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 3, 2, 1, 1, 4].length) (baseStart_8129592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8129592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8129592 prefixEnd_8129592 := by exact prefixLift 8129592
  have htrace : WordTrace (prefixWord ++ tailWord_8129592) baseStart_8129592 baseEnd_8129592 := by
    simpa [prefixWord, tailWord_8129592, baseEnd_8129592] using wordTrace_append hprefix tailTrace_8129592
  have hstable : (prefixWord ++ tailWord_8129592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8129592).length < 2 ^ (prefixWord ++ tailWord_8129592).sum := by decide
  have hdescent : baseEnd_8129592 < baseStart_8129592 := by decide
  rcases family_descends (prefixWord ++ tailWord_8129592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8129606 : List Nat := [6, 1, 1, 1, 1, 3, 3, 1, 1, 5]
def baseStart_8129606 : Nat := 118140960795 + 8129606 * 2 ^ 59
def prefixEnd_8129606 : Nat := 4983230072969 + 3 ^ 40 * 8129606 * 2
def baseEnd_8129606 : Nat := 1391465136558475037612543

theorem tailTrace_8129606 : CollatzResearch.WordTrace tailWord_8129606 prefixEnd_8129606 1391465136558475037612543 := by
  unfold tailWord_8129606
  simp only [CollatzResearch.WordTrace]
  refine ⟨9265971568307292594114271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 197674060123888908674437781 9265971568307292594114271)
  ·
    refine ⟨13898957352460938891171407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9265971568307292594114271 13898957352460938891171407)
    ·
      refine ⟨20848436028691408336757111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13898957352460938891171407 20848436028691408336757111)
      ·
        refine ⟨31272654043037112505135667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20848436028691408336757111 31272654043037112505135667)
        ·
          refine ⟨46908981064555668757703501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31272654043037112505135667 46908981064555668757703501)
          ·
            refine ⟨17590867899208375784138813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46908981064555668757703501 17590867899208375784138813)
            ·
              refine ⟨6596575462203140919052055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17590867899208375784138813 6596575462203140919052055)
              ·
                refine ⟨9894863193304711378578083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6596575462203140919052055 9894863193304711378578083)
                ·
                  refine ⟨14842294789957067067867125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9894863193304711378578083 14842294789957067067867125)
                  ·
                    refine ⟨1391465136558475037612543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14842294789957067067867125 1391465136558475037612543)
                    ·
                      rfl

theorem cell23_8129606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 3, 1, 1, 5].length) (baseStart_8129606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8129606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8129606 prefixEnd_8129606 := by exact prefixLift 8129606
  have htrace : WordTrace (prefixWord ++ tailWord_8129606) baseStart_8129606 baseEnd_8129606 := by
    simpa [prefixWord, tailWord_8129606, baseEnd_8129606] using wordTrace_append hprefix tailTrace_8129606
  have hstable : (prefixWord ++ tailWord_8129606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8129606).length < 2 ^ (prefixWord ++ tailWord_8129606).sum := by decide
  have hdescent : baseEnd_8129606 < baseStart_8129606 := by decide
  rcases family_descends (prefixWord ++ tailWord_8129606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8129642 : List Nat := [3, 1, 3, 2, 2, 1, 1, 3, 1, 3, 3]
def baseStart_8129642 : Nat := 118140960795 + 8129642 * 2 ^ 59
def prefixEnd_8129642 : Nat := 4983230072969 + 3 ^ 40 * 8129642 * 2
def baseEnd_8129642 : Nat := 4174413894978986971987463

theorem tailTrace_8129642 : CollatzResearch.WordTrace tailWord_8129642 prefixEnd_8129642 4174413894978986971987463 := by
  unfold tailWord_8129642
  simp only [CollatzResearch.WordTrace]
  refine ⟨74128100803425735289991795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197674935475801960773311453 74128100803425735289991795)
  ·
    refine ⟨111192151205138602934987693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74128100803425735289991795 111192151205138602934987693)
    ·
      refine ⟨41697056701926976100620385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111192151205138602934987693 41697056701926976100620385)
      ·
        refine ⟨31272792526445232075465289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41697056701926976100620385 31272792526445232075465289)
        ·
          refine ⟨23454594394833924056598967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31272792526445232075465289 23454594394833924056598967)
          ·
            refine ⟨35181891592250886084898451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23454594394833924056598967 35181891592250886084898451)
            ·
              refine ⟨52772837388376329127347677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35181891592250886084898451 52772837388376329127347677)
              ·
                refine ⟨19789814020641123422755379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52772837388376329127347677 19789814020641123422755379)
                ·
                  refine ⟨29684721030961685134133069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19789814020641123422755379 29684721030961685134133069)
                  ·
                    refine ⟨11131770386610631925299901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29684721030961685134133069 11131770386610631925299901)
                    ·
                      refine ⟨4174413894978986971987463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11131770386610631925299901 4174413894978986971987463)
                      ·
                        rfl

theorem cell23_8129642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 3, 1, 3, 3].length) (baseStart_8129642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8129642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8129642 prefixEnd_8129642 := by exact prefixLift 8129642
  have htrace : WordTrace (prefixWord ++ tailWord_8129642) baseStart_8129642 baseEnd_8129642 := by
    simpa [prefixWord, tailWord_8129642, baseEnd_8129642] using wordTrace_append hprefix tailTrace_8129642
  have hstable : (prefixWord ++ tailWord_8129642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8129642).length < 2 ^ (prefixWord ++ tailWord_8129642).sum := by decide
  have hdescent : baseEnd_8129642 < baseStart_8129642 := by decide
  rcases family_descends (prefixWord ++ tailWord_8129642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8129685 : List Nat := [1, 3, 2, 1, 1, 1, 2, 3, 2, 4, 3]
def baseStart_8129685 : Nat := 118140960795 + 8129685 * 2 ^ 59
def prefixEnd_8129685 : Nat := 4983230072969 + 3 ^ 40 * 8129685 * 2
def baseEnd_8129685 : Nat := 4174435974647130303749765

theorem tailTrace_8129685 : CollatzResearch.WordTrace tailWord_8129685 prefixEnd_8129685 4174435974647130303749765 := by
  unfold tailWord_8129685
  simp only [CollatzResearch.WordTrace]
  refine ⟨296513971552547159503782509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197675981035031439669188339 296513971552547159503782509)
  ·
    refine ⟨111192739332205184813918441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 296513971552547159503782509 111192739332205184813918441)
    ·
      refine ⟨83394554499153888610438831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111192739332205184813918441 83394554499153888610438831)
      ·
        refine ⟨125091831748730832915658247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83394554499153888610438831 125091831748730832915658247)
        ·
          refine ⟨187637747623096249373487371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125091831748730832915658247 187637747623096249373487371)
          ·
            refine ⟨281456621434644374060231057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187637747623096249373487371 281456621434644374060231057)
            ·
              refine ⟨211092466075983280545173293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 281456621434644374060231057 211092466075983280545173293)
              ·
                refine ⟨79159674778493730204439985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 211092466075983280545173293 79159674778493730204439985)
                ·
                  refine ⟨59369756083870297653329989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79159674778493730204439985 59369756083870297653329989)
                  ·
                    refine ⟨11131829265725680809999373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59369756083870297653329989 11131829265725680809999373)
                    ·
                      refine ⟨4174435974647130303749765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11131829265725680809999373 4174435974647130303749765)
                      ·
                        rfl

theorem cell23_8129685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 3, 2, 4, 3].length) (baseStart_8129685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8129685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8129685 prefixEnd_8129685 := by exact prefixLift 8129685
  have htrace : WordTrace (prefixWord ++ tailWord_8129685) baseStart_8129685 baseEnd_8129685 := by
    simpa [prefixWord, tailWord_8129685, baseEnd_8129685] using wordTrace_append hprefix tailTrace_8129685
  have hstable : (prefixWord ++ tailWord_8129685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8129685).length < 2 ^ (prefixWord ++ tailWord_8129685).sum := by decide
  have hdescent : baseEnd_8129685 < baseStart_8129685 := by decide
  rcases family_descends (prefixWord ++ tailWord_8129685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8129699 : List Nat := [1, 1, 1, 4, 1, 1, 1, 7, 2, 2, 2]
def baseStart_8129699 : Nat := 118140960795 + 8129699 * 2 ^ 59
def prefixEnd_8129699 : Nat := 4983230072969 + 3 ^ 40 * 8129699 * 2
def baseEnd_8129699 : Nat := 4174443163376293248974701

theorem tailTrace_8129699 : CollatzResearch.WordTrace tailWord_8129699 prefixEnd_8129699 4174443163376293248974701 := by
  unfold tailWord_8129699
  simp only [CollatzResearch.WordTrace]
  refine ⟨296514482174496439894792151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197676321449664293263194767 296514482174496439894792151)
  ·
    refine ⟨444771723261744659842188227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296514482174496439894792151 444771723261744659842188227)
    ·
      refine ⟨667157584892616989763282341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 444771723261744659842188227 667157584892616989763282341)
      ·
        refine ⟨125092047167365685580615439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 667157584892616989763282341 125092047167365685580615439)
        ·
          refine ⟨187638070751048528370923159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125092047167365685580615439 187638070751048528370923159)
          ·
            refine ⟨281457106126572792556384739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187638070751048528370923159 281457106126572792556384739)
            ·
              refine ⟨422185659189859188834577109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 281457106126572792556384739 422185659189859188834577109)
              ·
                refine ⟨9894976387262324738310401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 422185659189859188834577109 9894976387262324738310401)
                ·
                  refine ⟨7421232290446743553732801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9894976387262324738310401 7421232290446743553732801)
                  ·
                    refine ⟨5565924217835057665299601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7421232290446743553732801 5565924217835057665299601)
                    ·
                      refine ⟨4174443163376293248974701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5565924217835057665299601 4174443163376293248974701)
                      ·
                        rfl

theorem cell23_8129699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 7, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 7, 2, 2, 2].length) (baseStart_8129699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8129699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8129699 prefixEnd_8129699 := by exact prefixLift 8129699
  have htrace : WordTrace (prefixWord ++ tailWord_8129699) baseStart_8129699 baseEnd_8129699 := by
    simpa [prefixWord, tailWord_8129699, baseEnd_8129699] using wordTrace_append hprefix tailTrace_8129699
  have hstable : (prefixWord ++ tailWord_8129699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8129699).length < 2 ^ (prefixWord ++ tailWord_8129699).sum := by decide
  have hdescent : baseEnd_8129699 < baseStart_8129699 := by decide
  rcases family_descends (prefixWord ++ tailWord_8129699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8129715 : List Nat := [1, 1, 1, 2, 3, 2, 2, 2, 1, 5, 3]
def baseStart_8129715 : Nat := 118140960795 + 8129715 * 2 ^ 59
def prefixEnd_8129715 : Nat := 4983230072969 + 3 ^ 40 * 8129715 * 2
def baseEnd_8129715 : Nat := 4174451379066765186374627

theorem tailTrace_8129715 : CollatzResearch.WordTrace tailWord_8129715 prefixEnd_8129715 4174451379066765186374627 := by
  unfold tailWord_8129715
  simp only [CollatzResearch.WordTrace]
  refine ⟨296515065742438474627374599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197676710494958983084916399 296515065742438474627374599)
  ·
    refine ⟨444772598613657711941061899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296515065742438474627374599 444772598613657711941061899)
    ·
      refine ⟨667158897920486567911592849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 444772598613657711941061899 667158897920486567911592849)
      ·
        refine ⟨500369173440364925933694637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 667158897920486567911592849 500369173440364925933694637)
        ·
          refine ⟨187638440040136847225135489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 500369173440364925933694637 187638440040136847225135489)
          ·
            refine ⟨140728830030102635418851617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 187638440040136847225135489 140728830030102635418851617)
            ·
              refine ⟨105546622522576976564138713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140728830030102635418851617 105546622522576976564138713)
              ·
                refine ⟨79159966891932732423104035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105546622522576976564138713 79159966891932732423104035)
                ·
                  refine ⟨118739950337899098634656053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79159966891932732423104035 118739950337899098634656053)
                  ·
                    refine ⟨11131870344178040496999005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 118739950337899098634656053 11131870344178040496999005)
                    ·
                      refine ⟨4174451379066765186374627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11131870344178040496999005 4174451379066765186374627)
                      ·
                        rfl

theorem cell23_8129715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 2, 1, 5, 3].length) (baseStart_8129715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8129715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8129715 prefixEnd_8129715 := by exact prefixLift 8129715
  have htrace : WordTrace (prefixWord ++ tailWord_8129715) baseStart_8129715 baseEnd_8129715 := by
    simpa [prefixWord, tailWord_8129715, baseEnd_8129715] using wordTrace_append hprefix tailTrace_8129715
  have hstable : (prefixWord ++ tailWord_8129715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8129715).length < 2 ^ (prefixWord ++ tailWord_8129715).sum := by decide
  have hdescent : baseEnd_8129715 < baseStart_8129715 := by decide
  rcases family_descends (prefixWord ++ tailWord_8129715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8129750 : List Nat := [5, 2, 1, 2, 2, 1, 1, 3, 2, 2, 2]
def baseStart_8129750 : Nat := 118140960795 + 8129750 * 2 ^ 59
def prefixEnd_8129750 : Nat := 4983230072969 + 3 ^ 40 * 8129750 * 2
def baseEnd_8129750 : Nat := 4174469350889672549436967

theorem tailTrace_8129750 : CollatzResearch.WordTrace tailWord_8129750 prefixEnd_8129750 4174469350889672549436967 := by
  unfold tailWord_8129750
  simp only [CollatzResearch.WordTrace]
  refine ⟨18532271393581979725306169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 197677561531541117069932469 18532271393581979725306169)
  ·
    refine ⟨13899203545186484793979627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18532271393581979725306169 13899203545186484793979627)
    ·
      refine ⟨20848805317779727190969441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13899203545186484793979627 20848805317779727190969441)
      ·
        refine ⟨15636603988334795393227081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20848805317779727190969441 15636603988334795393227081)
        ·
          refine ⟨11727452991251096544920311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15636603988334795393227081 11727452991251096544920311)
          ·
            refine ⟨17591179486876644817380467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11727452991251096544920311 17591179486876644817380467)
            ·
              refine ⟨26386769230314967226070701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17591179486876644817380467 26386769230314967226070701)
              ·
                refine ⟨9895038461368112709776513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26386769230314967226070701 9895038461368112709776513)
                ·
                  refine ⟨7421278846026084532332385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9895038461368112709776513 7421278846026084532332385)
                  ·
                    refine ⟨5565959134519563399249289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7421278846026084532332385 5565959134519563399249289)
                    ·
                      refine ⟨4174469350889672549436967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5565959134519563399249289 4174469350889672549436967)
                      ·
                        rfl

theorem cell23_8129750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 3, 2, 2, 2].length) (baseStart_8129750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8129750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8129750 prefixEnd_8129750 := by exact prefixLift 8129750
  have htrace : WordTrace (prefixWord ++ tailWord_8129750) baseStart_8129750 baseEnd_8129750 := by
    simpa [prefixWord, tailWord_8129750, baseEnd_8129750] using wordTrace_append hprefix tailTrace_8129750
  have hstable : (prefixWord ++ tailWord_8129750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8129750).length < 2 ^ (prefixWord ++ tailWord_8129750).sum := by decide
  have hdescent : baseEnd_8129750 < baseStart_8129750 := by decide
  rcases family_descends (prefixWord ++ tailWord_8129750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8129772 : List Nat := [2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 4]
def baseStart_8129772 : Nat := 118140960795 + 8129772 * 2 ^ 59
def prefixEnd_8129772 : Nat := 4983230072969 + 3 ^ 40 * 8129772 * 2
def baseEnd_8129772 : Nat := 4174480647464071463361865

theorem tailTrace_8129772 : CollatzResearch.WordTrace tailWord_8129772 prefixEnd_8129772 4174480647464071463361865 := by
  unfold tailWord_8129772
  simp only [CollatzResearch.WordTrace]
  refine ⟨148258572351615986681099785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197678096468821315574799713 148258572351615986681099785)
  ·
    refine ⟨111193929263711990010824839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148258572351615986681099785 111193929263711990010824839)
    ·
      refine ⟨166790893895567985016237259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111193929263711990010824839 166790893895567985016237259)
      ·
        refine ⟨250186340843351977524355889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166790893895567985016237259 250186340843351977524355889)
        ·
          refine ⟨187639755632513983143266917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 250186340843351977524355889 187639755632513983143266917)
          ·
            refine ⟨35182454181096371839362547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 187639755632513983143266917 35182454181096371839362547)
            ·
              refine ⟨52773681271644557759043821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35182454181096371839362547 52773681271644557759043821)
              ·
                refine ⟨19790130476866709159641433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52773681271644557759043821 19790130476866709159641433)
                ·
                  refine ⟨14842597857650031869731075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19790130476866709159641433 14842597857650031869731075)
                  ·
                    refine ⟨22263896786475047804596613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14842597857650031869731075 22263896786475047804596613)
                    ·
                      refine ⟨4174480647464071463361865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22263896786475047804596613 4174480647464071463361865)
                      ·
                        rfl

theorem cell23_8129772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 4].length) (baseStart_8129772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8129772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8129772 prefixEnd_8129772 := by exact prefixLift 8129772
  have htrace : WordTrace (prefixWord ++ tailWord_8129772) baseStart_8129772 baseEnd_8129772 := by
    simpa [prefixWord, tailWord_8129772, baseEnd_8129772] using wordTrace_append hprefix tailTrace_8129772
  have hstable : (prefixWord ++ tailWord_8129772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8129772).length < 2 ^ (prefixWord ++ tailWord_8129772).sum := by decide
  have hdescent : baseEnd_8129772 < baseStart_8129772 := by decide
  rcases family_descends (prefixWord ++ tailWord_8129772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8129785 : List Nat := [1, 2, 1, 3, 1, 1, 4, 1, 2, 1, 6]
def baseStart_8129785 : Nat := 118140960795 + 8129785 * 2 ^ 59
def prefixEnd_8129785 : Nat := 4983230072969 + 3 ^ 40 * 8129785 * 2
def baseEnd_8129785 : Nat := 4174487322712579912499305

theorem tailTrace_8129785 : CollatzResearch.WordTrace tailWord_8129785 prefixEnd_8129785 4174487322712579912499305 := by
  unfold tailWord_8129785
  simp only [CollatzResearch.WordTrace]
  refine ⟨296517618852184876582422809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197678412568123251054948539 296517618852184876582422809)
  ·
    refine ⟨222388214139138657436817107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296517618852184876582422809 222388214139138657436817107)
    ·
      refine ⟨333582321208707986155225661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222388214139138657436817107 333582321208707986155225661)
      ·
        refine ⟨125093370453265494808209623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 333582321208707986155225661 125093370453265494808209623)
        ·
          refine ⟨187640055679898242212314435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125093370453265494808209623 187640055679898242212314435)
          ·
            refine ⟨281460083519847363318471653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187640055679898242212314435 281460083519847363318471653)
            ·
              refine ⟨52773765659971380622213435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 281460083519847363318471653 52773765659971380622213435)
              ·
                refine ⟨79160648489957070933320153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52773765659971380622213435 79160648489957070933320153)
                ·
                  refine ⟨59370486367467803199990115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79160648489957070933320153 59370486367467803199990115)
                  ·
                    refine ⟨89055729551201704799985173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59370486367467803199990115 89055729551201704799985173)
                    ·
                      refine ⟨4174487322712579912499305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 89055729551201704799985173 4174487322712579912499305)
                      ·
                        rfl

theorem cell23_8129785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 1, 2, 1, 6].length) (baseStart_8129785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8129785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8129785 prefixEnd_8129785 := by exact prefixLift 8129785
  have htrace : WordTrace (prefixWord ++ tailWord_8129785) baseStart_8129785 baseEnd_8129785 := by
    simpa [prefixWord, tailWord_8129785, baseEnd_8129785] using wordTrace_append hprefix tailTrace_8129785
  have hstable : (prefixWord ++ tailWord_8129785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8129785).length < 2 ^ (prefixWord ++ tailWord_8129785).sum := by decide
  have hdescent : baseEnd_8129785 < baseStart_8129785 := by decide
  rcases family_descends (prefixWord ++ tailWord_8129785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8129846 : List Nat := [5, 1, 2, 3, 1, 1, 1, 1, 8]
def baseStart_8129846 : Nat := 118140960795 + 8129846 * 2 ^ 59
def prefixEnd_8129846 : Nat := 4983230072969 + 3 ^ 40 * 8129846 * 2
def baseEnd_8129846 : Nat := 463835405003611574870725

theorem tailTrace_8129846 : CollatzResearch.WordTrace tailWord_8129846 prefixEnd_8129846 463835405003611574870725 := by
  unfold tailWord_8129846
  simp only [CollatzResearch.WordTrace]
  refine ⟨18532490231560242750024587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 197679895803309256000262261 18532490231560242750024587)
  ·
    refine ⟨27798735347340364125036881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18532490231560242750024587 27798735347340364125036881)
    ·
      refine ⟨20849051510505273093777661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27798735347340364125036881 20849051510505273093777661)
      ·
        refine ⟨7818394316439477410166623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20849051510505273093777661 7818394316439477410166623)
        ·
          refine ⟨11727591474659216115249935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7818394316439477410166623 11727591474659216115249935)
          ·
            refine ⟨17591387211988824172874903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11727591474659216115249935 17591387211988824172874903)
            ·
              refine ⟨26387080817983236259312355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17591387211988824172874903 26387080817983236259312355)
              ·
                refine ⟨39580621226974854388968533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26387080817983236259312355 39580621226974854388968533)
                ·
                  refine ⟨463835405003611574870725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39580621226974854388968533 463835405003611574870725)
                  ·
                    rfl

theorem cell23_8129846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 1, 8].length) (baseStart_8129846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8129846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8129846 prefixEnd_8129846 := by exact prefixLift 8129846
  have htrace : WordTrace (prefixWord ++ tailWord_8129846) baseStart_8129846 baseEnd_8129846 := by
    simpa [prefixWord, tailWord_8129846, baseEnd_8129846] using wordTrace_append hprefix tailTrace_8129846
  have hstable : (prefixWord ++ tailWord_8129846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8129846).length < 2 ^ (prefixWord ++ tailWord_8129846).sum := by decide
  have hdescent : baseEnd_8129846 < baseStart_8129846 := by decide
  rcases family_descends (prefixWord ++ tailWord_8129846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8129856 : List Nat := [2, 1, 1, 2, 2, 1, 3, 6, 1, 1, 3]
def baseStart_8129856 : Nat := 118140960795 + 8129856 * 2 ^ 59
def prefixEnd_8129856 : Nat := 4983230072969 + 3 ^ 40 * 8129856 * 2
def baseEnd_8129856 : Nat := 4174523779839049134711479

theorem tailTrace_8129856 : CollatzResearch.WordTrace tailWord_8129856 prefixEnd_8129856 4174523779839049134711479 := by
  unfold tailWord_8129856
  simp only [CollatzResearch.WordTrace]
  refine ⟨148260104217463827854128711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197680138956618437138838281 148260104217463827854128711)
  ·
    refine ⟨222390156326195741781193067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148260104217463827854128711 222390156326195741781193067)
    ·
      refine ⟨333585234489293612671789601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222390156326195741781193067 333585234489293612671789601)
      ·
        refine ⟨250188925866970209503842201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 333585234489293612671789601 250188925866970209503842201)
        ·
          refine ⟨187641694400227657127881651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 250188925866970209503842201 187641694400227657127881651)
          ·
            refine ⟨281462541600341485691822477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187641694400227657127881651 281462541600341485691822477)
            ·
              refine ⟨105548453100128057134433429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 281462541600341485691822477 105548453100128057134433429)
              ·
                refine ⟨4947583739068502678176567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 105548453100128057134433429 4947583739068502678176567)
                ·
                  refine ⟨7421375608602754017264851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4947583739068502678176567 7421375608602754017264851)
                  ·
                    refine ⟨11132063412904131025897277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7421375608602754017264851 11132063412904131025897277)
                    ·
                      refine ⟨4174523779839049134711479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11132063412904131025897277 4174523779839049134711479)
                      ·
                        rfl

theorem cell23_8129856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 6, 1, 1, 3].length) (baseStart_8129856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8129856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8129856 prefixEnd_8129856 := by exact prefixLift 8129856
  have htrace : WordTrace (prefixWord ++ tailWord_8129856) baseStart_8129856 baseEnd_8129856 := by
    simpa [prefixWord, tailWord_8129856, baseEnd_8129856] using wordTrace_append hprefix tailTrace_8129856
  have hstable : (prefixWord ++ tailWord_8129856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8129856).length < 2 ^ (prefixWord ++ tailWord_8129856).sum := by decide
  have hdescent : baseEnd_8129856 < baseStart_8129856 := by decide
  rcases family_descends (prefixWord ++ tailWord_8129856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8129879 : List Nat := [1, 1, 3, 2, 3, 2, 1, 4, 1, 1, 4]
def baseStart_8129879 : Nat := 118140960795 + 8129879 * 2 ^ 59
def prefixEnd_8129879 : Nat := 4983230072969 + 3 ^ 40 * 8129879 * 2
def baseEnd_8129879 : Nat := 4174535589894102544723873

theorem tailTrace_8129879 : CollatzResearch.WordTrace tailWord_8129879 prefixEnd_8129879 4174535589894102544723873 := by
  unfold tailWord_8129879
  simp only [CollatzResearch.WordTrace]
  refine ⟨296521047313844330636344691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197680698209229553757563127 296521047313844330636344691)
  ·
    refine ⟨444781570970766495954517037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296521047313844330636344691 444781570970766495954517037)
    ·
      refine ⟨166793089114037435982943889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 444781570970766495954517037 166793089114037435982943889)
      ·
        refine ⟨125094816835528076987207917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166793089114037435982943889 125094816835528076987207917)
        ·
          refine ⟨46910556313323028870202969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125094816835528076987207917 46910556313323028870202969)
          ·
            refine ⟨35182917234992271652652227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46910556313323028870202969 35182917234992271652652227)
            ·
              refine ⟨52774375852488407478978341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35182917234992271652652227 52774375852488407478978341)
              ·
                refine ⟨9895195472341576402308439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52774375852488407478978341 9895195472341576402308439)
                ·
                  refine ⟨14842793208512364603462659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9895195472341576402308439 14842793208512364603462659)
                  ·
                    refine ⟨22264189812768546905193989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14842793208512364603462659 22264189812768546905193989)
                    ·
                      refine ⟨4174535589894102544723873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22264189812768546905193989 4174535589894102544723873)
                      ·
                        rfl

theorem cell23_8129879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 4, 1, 1, 4].length) (baseStart_8129879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8129879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8129879 prefixEnd_8129879 := by exact prefixLift 8129879
  have htrace : WordTrace (prefixWord ++ tailWord_8129879) baseStart_8129879 baseEnd_8129879 := by
    simpa [prefixWord, tailWord_8129879, baseEnd_8129879] using wordTrace_append hprefix tailTrace_8129879
  have hstable : (prefixWord ++ tailWord_8129879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8129879).length < 2 ^ (prefixWord ++ tailWord_8129879).sum := by decide
  have hdescent : baseEnd_8129879 < baseStart_8129879 := by decide
  rcases family_descends (prefixWord ++ tailWord_8129879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8129913 : List Nat := [1, 2, 1, 3, 2, 1, 2, 6, 1, 2, 2]
def baseStart_8129913 : Nat := 118140960795 + 8129913 * 2 ^ 59
def prefixEnd_8129913 : Nat := 4983230072969 + 3 ^ 40 * 8129913 * 2
def baseEnd_8129913 : Nat := 4174553048236355411698717

theorem tailTrace_8129913 : CollatzResearch.WordTrace tailWord_8129913 prefixEnd_8129913 4174553048236355411698717 := by
  unfold tailWord_8129913
  simp only [CollatzResearch.WordTrace]
  refine ⟨296522287395721154443082393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197681524930480769628721595 296522287395721154443082393)
  ·
    refine ⟨222391715546790865832311795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296522287395721154443082393 222391715546790865832311795)
    ·
      refine ⟨333587573320186298748467693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222391715546790865832311795 333587573320186298748467693)
      ·
        refine ⟨125095339995069862030675385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 333587573320186298748467693 125095339995069862030675385)
        ·
          refine ⟨93821504996302396523006539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125095339995069862030675385 93821504996302396523006539)
          ·
            refine ⟨140732257494453594784509809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93821504996302396523006539 140732257494453594784509809)
            ·
              refine ⟨105549193120840196088382357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140732257494453594784509809 105549193120840196088382357)
              ·
                refine ⟨4947618427539384191642923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 105549193120840196088382357 4947618427539384191642923)
                ·
                  refine ⟨7421427641309076287464385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4947618427539384191642923 7421427641309076287464385)
                  ·
                    refine ⟨5566070730981807215598289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7421427641309076287464385 5566070730981807215598289)
                    ·
                      refine ⟨4174553048236355411698717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5566070730981807215598289 4174553048236355411698717)
                      ·
                        rfl

theorem cell23_8129913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 6, 1, 2, 2].length) (baseStart_8129913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8129913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8129913 prefixEnd_8129913 := by exact prefixLift 8129913
  have htrace : WordTrace (prefixWord ++ tailWord_8129913) baseStart_8129913 baseEnd_8129913 := by
    simpa [prefixWord, tailWord_8129913, baseEnd_8129913] using wordTrace_append hprefix tailTrace_8129913
  have hstable : (prefixWord ++ tailWord_8129913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8129913).length < 2 ^ (prefixWord ++ tailWord_8129913).sum := by decide
  have hdescent : baseEnd_8129913 < baseStart_8129913 := by decide
  rcases family_descends (prefixWord ++ tailWord_8129913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8129923 : List Nat := [1, 1, 1, 3, 5, 3, 2, 1, 2, 4]
def baseStart_8129923 : Nat := 118140960795 + 8129923 * 2 ^ 59
def prefixEnd_8129923 : Nat := 4983230072969 + 3 ^ 40 * 8129923 * 2
def baseEnd_8129923 : Nat := 1391519394347633457524557

theorem tailTrace_8129923 : CollatzResearch.WordTrace tailWord_8129923 prefixEnd_8129923 1391519394347633457524557 := by
  unfold tailWord_8129923
  simp only [CollatzResearch.WordTrace]
  refine ⟨296522652125684926150946423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197681768083789950767297615 296522652125684926150946423)
  ·
    refine ⟨444783978188527389226419635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296522652125684926150946423 444783978188527389226419635)
    ·
      refine ⟨667175967282791083839629453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 444783978188527389226419635 667175967282791083839629453)
      ·
        refine ⟨250190987731046656439861045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 667175967282791083839629453 250190987731046656439861045)
        ·
          refine ⟨23455405099785624041236973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 250190987731046656439861045 23455405099785624041236973)
          ·
            refine ⟨8795776912419609015463865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23455405099785624041236973 8795776912419609015463865)
            ·
              refine ⟨6596832684314706761597899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8795776912419609015463865 6596832684314706761597899)
              ·
                refine ⟨9895249026472060142396849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6596832684314706761597899 9895249026472060142396849)
                ·
                  refine ⟨7421436769854045106797637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9895249026472060142396849 7421436769854045106797637)
                  ·
                    refine ⟨1391519394347633457524557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7421436769854045106797637 1391519394347633457524557)
                    ·
                      rfl

theorem cell23_8129923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 2, 1, 2, 4].length) (baseStart_8129923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8129923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8129923 prefixEnd_8129923 := by exact prefixLift 8129923
  have htrace : WordTrace (prefixWord ++ tailWord_8129923) baseStart_8129923 baseEnd_8129923 := by
    simpa [prefixWord, tailWord_8129923, baseEnd_8129923] using wordTrace_append hprefix tailTrace_8129923
  have hstable : (prefixWord ++ tailWord_8129923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8129923).length < 2 ^ (prefixWord ++ tailWord_8129923).sum := by decide
  have hdescent : baseEnd_8129923 < baseStart_8129923 := by decide
  rcases family_descends (prefixWord ++ tailWord_8129923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8129950 : List Nat := [4, 3, 1, 2, 3, 1, 1, 1, 1, 1, 5]
def baseStart_8129950 : Nat := 118140960795 + 8129950 * 2 ^ 59
def prefixEnd_8129950 : Nat := 4983230072969 + 3 ^ 40 * 8129950 * 2
def baseEnd_8129950 : Nat := 4174572047020571766936047

theorem tailTrace_8129950 : CollatzResearch.WordTrace tailWord_8129950 prefixEnd_8129950 4174572047020571766936047 := by
  unfold tailWord_8129950
  simp only [CollatzResearch.WordTrace]
  refine ⟨37065454612073388720272413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 197682424597724739841452869 37065454612073388720272413)
  ·
    refine ⟨13899545479527520770102155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37065454612073388720272413 13899545479527520770102155)
    ·
      refine ⟨20849318219291281155153233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13899545479527520770102155 20849318219291281155153233)
      ·
        refine ⟨15636988664468460866364925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20849318219291281155153233 15636988664468460866364925)
        ·
          refine ⟨5863870749175672824886847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15636988664468460866364925 5863870749175672824886847)
          ·
            refine ⟨8795806123763509237330271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5863870749175672824886847 8795806123763509237330271)
            ·
              refine ⟨13193709185645263855995407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8795806123763509237330271 13193709185645263855995407)
              ·
                refine ⟨19790563778467895783993111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13193709185645263855995407 19790563778467895783993111)
                ·
                  refine ⟨29685845667701843675989667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19790563778467895783993111 29685845667701843675989667)
                  ·
                    refine ⟨44528768501552765513984501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29685845667701843675989667 44528768501552765513984501)
                    ·
                      refine ⟨4174572047020571766936047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44528768501552765513984501 4174572047020571766936047)
                      ·
                        rfl

theorem cell23_8129950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 1, 1, 1, 1, 5].length) (baseStart_8129950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8129950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8129950 prefixEnd_8129950 := by exact prefixLift 8129950
  have htrace : WordTrace (prefixWord ++ tailWord_8129950) baseStart_8129950 baseEnd_8129950 := by
    simpa [prefixWord, tailWord_8129950, baseEnd_8129950] using wordTrace_append hprefix tailTrace_8129950
  have hstable : (prefixWord ++ tailWord_8129950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8129950).length < 2 ^ (prefixWord ++ tailWord_8129950).sum := by decide
  have hdescent : baseEnd_8129950 < baseStart_8129950 := by decide
  rcases family_descends (prefixWord ++ tailWord_8129950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8130026 : List Nat := [3, 1, 3, 1, 4, 1, 2, 1, 7]
def baseStart_8130026 : Nat := 118140960795 + 8130026 * 2 ^ 59
def prefixEnd_8130026 : Nat := 4983230072969 + 3 ^ 40 * 8130026 * 2
def baseEnd_8130026 : Nat := 463845674616701496620633

theorem tailTrace_8130026 : CollatzResearch.WordTrace tailWord_8130026 prefixEnd_8130026 463845674616701496620633 := by
  unfold tailWord_8130026
  simp only [CollatzResearch.WordTrace]
  refine ⟨74131602211077943685486483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197684272562874516494630621 74131602211077943685486483)
  ·
    refine ⟨111197403316616915528229725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74131602211077943685486483 111197403316616915528229725)
    ·
      refine ⟨41699026243731343323086147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111197403316616915528229725 41699026243731343323086147)
      ·
        refine ⟨62548539365597014984629221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41699026243731343323086147 62548539365597014984629221)
        ·
          refine ⟨11727851131049440309617979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62548539365597014984629221 11727851131049440309617979)
          ·
            refine ⟨17591776696574160464426969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11727851131049440309617979 17591776696574160464426969)
            ·
              refine ⟨13193832522430620348320227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17591776696574160464426969 13193832522430620348320227)
              ·
                refine ⟨19790748783645930522480341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13193832522430620348320227 19790748783645930522480341)
                ·
                  refine ⟨463845674616701496620633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19790748783645930522480341 463845674616701496620633)
                  ·
                    rfl

theorem cell23_8130026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 2, 1, 7].length) (baseStart_8130026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8130026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8130026 prefixEnd_8130026 := by exact prefixLift 8130026
  have htrace : WordTrace (prefixWord ++ tailWord_8130026) baseStart_8130026 baseEnd_8130026 := by
    simpa [prefixWord, tailWord_8130026, baseEnd_8130026] using wordTrace_append hprefix tailTrace_8130026
  have hstable : (prefixWord ++ tailWord_8130026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8130026).length < 2 ^ (prefixWord ++ tailWord_8130026).sum := by decide
  have hdescent : baseEnd_8130026 < baseStart_8130026 := by decide
  rcases family_descends (prefixWord ++ tailWord_8130026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8130060 : List Nat := [2, 2, 1, 2, 6, 1, 1, 3, 5]
def baseStart_8130060 : Nat := 118140960795 + 8130060 * 2 ^ 59
def prefixEnd_8130060 : Nat := 4983230072969 + 3 ^ 40 * 8130060 * 2
def baseEnd_8130060 : Nat := 463847614432507370728949

theorem tailTrace_8130060 : CollatzResearch.WordTrace tailWord_8130060 prefixEnd_8130060 463847614432507370728949 := by
  unfold tailWord_8130060
  simp only [CollatzResearch.WordTrace]
  refine ⟨148263824463094299274341817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197685099284125732365789089 148263824463094299274341817)
  ·
    refine ⟨111197868347320724455756363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148263824463094299274341817 111197868347320724455756363)
    ·
      refine ⟨166796802520981086683634545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111197868347320724455756363 166796802520981086683634545)
      ·
        refine ⟨125097601890735815012725909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166796802520981086683634545 125097601890735815012725909)
        ·
          refine ⟨5863950088628241328721527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 125097601890735815012725909 5863950088628241328721527)
          ·
            refine ⟨8795925132942361993082291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5863950088628241328721527 8795925132942361993082291)
            ·
              refine ⟨13193887699413542989623437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8795925132942361993082291 13193887699413542989623437)
              ·
                refine ⟨4947707887280078621108789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13193887699413542989623437 4947707887280078621108789)
                ·
                  refine ⟨463847614432507370728949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4947707887280078621108789 463847614432507370728949)
                  ·
                    rfl

theorem cell23_8130060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 1, 3, 5].length) (baseStart_8130060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8130060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8130060 prefixEnd_8130060 := by exact prefixLift 8130060
  have htrace : WordTrace (prefixWord ++ tailWord_8130060) baseStart_8130060 baseEnd_8130060 := by
    simpa [prefixWord, tailWord_8130060, baseEnd_8130060] using wordTrace_append hprefix tailTrace_8130060
  have hstable : (prefixWord ++ tailWord_8130060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8130060).length < 2 ^ (prefixWord ++ tailWord_8130060).sum := by decide
  have hdescent : baseEnd_8130060 < baseStart_8130060 := by decide
  rcases family_descends (prefixWord ++ tailWord_8130060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8130076 : List Nat := [2, 2, 3, 1, 2, 1, 3, 2, 2, 1, 4]
def baseStart_8130076 : Nat := 118140960795 + 8130076 * 2 ^ 59
def prefixEnd_8130076 : Nat := 4983230072969 + 3 ^ 40 * 8130076 * 2
def baseEnd_8130076 : Nat := 4174636745583038273960467

theorem tailTrace_8130076 : CollatzResearch.WordTrace tailWord_8130076 prefixEnd_8130076 4174636745583038273960467 := by
  unfold tailWord_8130076
  simp only [CollatzResearch.WordTrace]
  refine ⟨148264116247065316640633041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197685488329420422187510721 148264116247065316640633041)
  ·
    refine ⟨111198087185298987480474781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148264116247065316640633041 111198087185298987480474781)
    ·
      refine ⟨41699282694487120305178043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111198087185298987480474781 41699282694487120305178043)
      ·
        refine ⟨62548924041730680457767065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41699282694487120305178043 62548924041730680457767065)
        ·
          refine ⟨46911693031298010343325299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62548924041730680457767065 46911693031298010343325299)
          ·
            refine ⟨70367539546947015514987949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46911693031298010343325299 70367539546947015514987949)
            ·
              refine ⟨26387827330105130818120481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70367539546947015514987949 26387827330105130818120481)
              ·
                refine ⟨19790870497578848113590361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26387827330105130818120481 19790870497578848113590361)
                ·
                  refine ⟨14843152873184136085192771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19790870497578848113590361 14843152873184136085192771)
                  ·
                    refine ⟨22264729309776204127789157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14843152873184136085192771 22264729309776204127789157)
                    ·
                      refine ⟨4174636745583038273960467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22264729309776204127789157 4174636745583038273960467)
                      ·
                        rfl

theorem cell23_8130076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 2, 2, 1, 4].length) (baseStart_8130076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8130076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8130076 prefixEnd_8130076 := by exact prefixLift 8130076
  have htrace : WordTrace (prefixWord ++ tailWord_8130076) baseStart_8130076 baseEnd_8130076 := by
    simpa [prefixWord, tailWord_8130076, baseEnd_8130076] using wordTrace_append hprefix tailTrace_8130076
  have hstable : (prefixWord ++ tailWord_8130076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8130076).length < 2 ^ (prefixWord ++ tailWord_8130076).sum := by decide
  have hdescent : baseEnd_8130076 < baseStart_8130076 := by decide
  rcases family_descends (prefixWord ++ tailWord_8130076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8130113 : List Nat := [1, 2, 5, 1, 1, 1, 4, 1, 2, 2, 3]
def baseStart_8130113 : Nat := 118140960795 + 8130113 * 2 ^ 59
def prefixEnd_8130113 : Nat := 4983230072969 + 3 ^ 40 * 8130113 * 2
def baseEnd_8130113 : Nat := 4174655744367254629197797

theorem tailTrace_8130113 : CollatzResearch.WordTrace tailWord_8130113 prefixEnd_8130113 4174655744367254629197797 := by
  unfold tailWord_8130113
  simp only [CollatzResearch.WordTrace]
  refine ⟨296529581994996588600362993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197686387996664392400241995 296529581994996588600362993)
  ·
    refine ⟨222397186496247441450272245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296529581994996588600362993 222397186496247441450272245)
    ·
      refine ⟨20849736234023197635963023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 222397186496247441450272245 20849736234023197635963023)
      ·
        refine ⟨31274604351034796453944535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20849736234023197635963023 31274604351034796453944535)
        ·
          refine ⟨46911906526552194680916803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31274604351034796453944535 46911906526552194680916803)
          ·
            refine ⟨70367859789828292021375205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46911906526552194680916803 70367859789828292021375205)
            ·
              refine ⟨13193973710592804754007851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70367859789828292021375205 13193973710592804754007851)
              ·
                refine ⟨19790960565889207131011777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13193973710592804754007851 19790960565889207131011777)
                ·
                  refine ⟨14843220424416905348258833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19790960565889207131011777 14843220424416905348258833)
                  ·
                    refine ⟨11132415318312679011194125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14843220424416905348258833 11132415318312679011194125)
                    ·
                      refine ⟨4174655744367254629197797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11132415318312679011194125 4174655744367254629197797)
                      ·
                        rfl

theorem cell23_8130113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 4, 1, 2, 2, 3].length) (baseStart_8130113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8130113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8130113 prefixEnd_8130113 := by exact prefixLift 8130113
  have htrace : WordTrace (prefixWord ++ tailWord_8130113) baseStart_8130113 baseEnd_8130113 := by
    simpa [prefixWord, tailWord_8130113, baseEnd_8130113] using wordTrace_append hprefix tailTrace_8130113
  have hstable : (prefixWord ++ tailWord_8130113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8130113).length < 2 ^ (prefixWord ++ tailWord_8130113).sum := by decide
  have hdescent : baseEnd_8130113 < baseStart_8130113 := by decide
  rcases family_descends (prefixWord ++ tailWord_8130113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8130136 : List Nat := [2, 1, 2, 2, 1, 2, 1, 2, 3, 5, 2]
def baseStart_8130136 : Nat := 118140960795 + 8130136 * 2 ^ 59
def prefixEnd_8130136 : Nat := 4983230072969 + 3 ^ 40 * 8130136 * 2
def baseEnd_8130136 : Nat := 4174667554422308039210191

theorem tailTrace_8130136 : CollatzResearch.WordTrace tailWord_8130136 prefixEnd_8130136 4174667554422308039210191 := by
  unfold tailWord_8130136
  simp only [CollatzResearch.WordTrace]
  refine ⟨148265210436956631764225131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197686947249275509018966841 148265210436956631764225131)
  ·
    refine ⟨222397815655434947646337697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148265210436956631764225131 222397815655434947646337697)
    ·
      refine ⟨166798361741576210734753273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222397815655434947646337697 166798361741576210734753273)
      ·
        refine ⟨125098771306182158051064955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166798361741576210734753273 125098771306182158051064955)
        ·
          refine ⟨187648156959273237076597433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125098771306182158051064955 187648156959273237076597433)
          ·
            refine ⟨140736117719454927807448075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 187648156959273237076597433 140736117719454927807448075)
            ·
              refine ⟨211104176579182391711172113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140736117719454927807448075 211104176579182391711172113)
              ·
                refine ⟨158328132434386793783379085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 211104176579182391711172113 158328132434386793783379085)
                ·
                  refine ⟨59373049662895047668767157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 158328132434386793783379085 59373049662895047668767157)
                  ·
                    refine ⟨5566223405896410718946921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59373049662895047668767157 5566223405896410718946921)
                    ·
                      refine ⟨4174667554422308039210191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5566223405896410718946921 4174667554422308039210191)
                      ·
                        rfl

theorem cell23_8130136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 2, 3, 5, 2].length) (baseStart_8130136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8130136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8130136 prefixEnd_8130136 := by exact prefixLift 8130136
  have htrace : WordTrace (prefixWord ++ tailWord_8130136) baseStart_8130136 baseEnd_8130136 := by
    simpa [prefixWord, tailWord_8130136, baseEnd_8130136] using wordTrace_append hprefix tailTrace_8130136
  have hstable : (prefixWord ++ tailWord_8130136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8130136).length < 2 ^ (prefixWord ++ tailWord_8130136).sum := by decide
  have hdescent : baseEnd_8130136 < baseStart_8130136 := by decide
  rcases family_descends (prefixWord ++ tailWord_8130136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8130176 : List Nat := [2, 1, 1, 2, 1, 4, 2, 2, 4, 4]
def baseStart_8130176 : Nat := 118140960795 + 8130176 * 2 ^ 59
def prefixEnd_8130176 : Nat := 4983230072969 + 3 ^ 40 * 8130176 * 2
def baseEnd_8130176 : Nat := 1391562697882829294236669

theorem tailTrace_8130176 : CollatzResearch.WordTrace tailWord_8130176 prefixEnd_8130176 1391562697882829294236669 := by
  unfold tailWord_8130176
  simp only [CollatzResearch.WordTrace]
  refine ⟨148265939896884175179953191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197687919862512233573270921 148265939896884175179953191)
  ·
    refine ⟨222398909845326262769929787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148265939896884175179953191 222398909845326262769929787)
    ·
      refine ⟨333598364767989394154894681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222398909845326262769929787 333598364767989394154894681)
      ·
        refine ⟨250198773575992045616171011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 333598364767989394154894681 250198773575992045616171011)
        ·
          refine ⟨375298160363988068424256517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250198773575992045616171011 375298160363988068424256517)
          ·
            refine ⟨70368405068247762829548097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 375298160363988068424256517 70368405068247762829548097)
            ·
              refine ⟨52776303801185822122161073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70368405068247762829548097 52776303801185822122161073)
              ·
                refine ⟨39582227850889366591620805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52776303801185822122161073 39582227850889366591620805)
                ·
                  refine ⟨7421667722041756235928901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39582227850889366591620805 7421667722041756235928901)
                  ·
                    refine ⟨1391562697882829294236669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7421667722041756235928901 1391562697882829294236669)
                    ·
                      rfl

theorem cell23_8130176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 2, 4, 4].length) (baseStart_8130176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8130176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8130176 prefixEnd_8130176 := by exact prefixLift 8130176
  have htrace : WordTrace (prefixWord ++ tailWord_8130176) baseStart_8130176 baseEnd_8130176 := by
    simpa [prefixWord, tailWord_8130176, baseEnd_8130176] using wordTrace_append hprefix tailTrace_8130176
  have hstable : (prefixWord ++ tailWord_8130176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8130176).length < 2 ^ (prefixWord ++ tailWord_8130176).sum := by decide
  have hdescent : baseEnd_8130176 < baseStart_8130176 := by decide
  rcases family_descends (prefixWord ++ tailWord_8130176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8130177 : List Nat := [1, 2, 4, 2, 1, 3, 2, 3, 1, 1, 3]
def baseStart_8130177 : Nat := 118140960795 + 8130177 * 2 ^ 59
def prefixEnd_8130177 : Nat := 4983230072969 + 3 ^ 40 * 8130177 * 2
def baseEnd_8130177 : Nat := 4174688607129142378797503

theorem tailTrace_8130177 : CollatzResearch.WordTrace tailWord_8130177 prefixEnd_8130177 4174688607129142378797503 := by
  unfold tailWord_8130177
  simp only [CollatzResearch.WordTrace]
  refine ⟨296531916266764727530692785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197687944177843151687128523 296531916266764727530692785)
  ·
    refine ⟨222398937200073545648019589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296531916266764727530692785 222398937200073545648019589)
    ·
      refine ⟨41699800725013789809003673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 222398937200073545648019589 41699800725013789809003673)
      ·
        refine ⟨31274850543760342356752755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41699800725013789809003673 31274850543760342356752755)
        ·
          refine ⟨46912275815640513535129133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31274850543760342356752755 46912275815640513535129133)
          ·
            refine ⟨17592103430865192575673425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46912275815640513535129133 17592103430865192575673425)
            ·
              refine ⟨13194077573148894431755069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17592103430865192575673425 13194077573148894431755069)
              ·
                refine ⟨4947779089930835411908151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13194077573148894431755069 4947779089930835411908151)
                ·
                  refine ⟨7421668634896253117862227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4947779089930835411908151 7421668634896253117862227)
                  ·
                    refine ⟨11132502952344379676793341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7421668634896253117862227 11132502952344379676793341)
                    ·
                      refine ⟨4174688607129142378797503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11132502952344379676793341 4174688607129142378797503)
                      ·
                        rfl

theorem cell23_8130177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 2, 3, 1, 1, 3].length) (baseStart_8130177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8130177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8130177 prefixEnd_8130177 := by exact prefixLift 8130177
  have htrace : WordTrace (prefixWord ++ tailWord_8130177) baseStart_8130177 baseEnd_8130177 := by
    simpa [prefixWord, tailWord_8130177, baseEnd_8130177] using wordTrace_append hprefix tailTrace_8130177
  have hstable : (prefixWord ++ tailWord_8130177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8130177).length < 2 ^ (prefixWord ++ tailWord_8130177).sum := by decide
  have hdescent : baseEnd_8130177 < baseStart_8130177 := by decide
  rcases family_descends (prefixWord ++ tailWord_8130177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8130179 : List Nat := [1, 1, 1, 3, 3, 1, 1, 2, 3, 1, 6]
def baseStart_8130179 : Nat := 118140960795 + 8130179 * 2 ^ 59
def prefixEnd_8130179 : Nat := 4983230072969 + 3 ^ 40 * 8130179 * 2
def baseEnd_8130179 : Nat := 4174689634090451370972493

theorem tailTrace_8130179 : CollatzResearch.WordTrace tailWord_8130179 prefixEnd_8130179 4174689634090451370972493 := by
  unfold tailWord_8130179
  simp only [CollatzResearch.WordTrace]
  refine ⟨296531989212757481872265591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197687992808504987914843727 296531989212757481872265591)
  ·
    refine ⟨444797983819136222808398387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296531989212757481872265591 444797983819136222808398387)
    ·
      refine ⟨667196975728704334212597581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 444797983819136222808398387 667196975728704334212597581)
      ·
        refine ⟨250198865898264125329724093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 667196975728704334212597581 250198865898264125329724093)
        ·
          refine ⟨93824574711849046998646535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 250198865898264125329724093 93824574711849046998646535)
          ·
            refine ⟨140736862067773570497969803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93824574711849046998646535 140736862067773570497969803)
            ·
              refine ⟨211105293101660355746954705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140736862067773570497969803 211105293101660355746954705)
              ·
                refine ⟨158328969826245266810216029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 211105293101660355746954705 158328969826245266810216029)
                ·
                  refine ⟨59373363684841975053831011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 158328969826245266810216029 59373363684841975053831011)
                  ·
                    refine ⟨89060045527262962580746517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59373363684841975053831011 89060045527262962580746517)
                    ·
                      refine ⟨4174689634090451370972493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 89060045527262962580746517 4174689634090451370972493)
                      ·
                        rfl

theorem cell23_8130179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 2, 3, 1, 6].length) (baseStart_8130179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8130179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8130179 prefixEnd_8130179 := by exact prefixLift 8130179
  have htrace : WordTrace (prefixWord ++ tailWord_8130179) baseStart_8130179 baseEnd_8130179 := by
    simpa [prefixWord, tailWord_8130179, baseEnd_8130179] using wordTrace_append hprefix tailTrace_8130179
  have hstable : (prefixWord ++ tailWord_8130179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8130179).length < 2 ^ (prefixWord ++ tailWord_8130179).sum := by decide
  have hdescent : baseEnd_8130179 < baseStart_8130179 := by decide
  rcases family_descends (prefixWord ++ tailWord_8130179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8130183 : List Nat := [1, 1, 4, 2, 1, 4, 1, 3, 1, 1, 4]
def baseStart_8130183 : Nat := 118140960795 + 8130183 * 2 ^ 59
def prefixEnd_8130183 : Nat := 4983230072969 + 3 ^ 40 * 8130183 * 2
def baseEnd_8130183 : Nat := 4174691688013069355322475

theorem tailTrace_8130183 : CollatzResearch.WordTrace tailWord_8130183 prefixEnd_8130183 4174691688013069355322475 := by
  unfold tailWord_8130183
  simp only [CollatzResearch.WordTrace]
  refine ⟨296532135104742990555411203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197688090069828660370274135 296532135104742990555411203)
  ·
    refine ⟨444798202657114485833116805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296532135104742990555411203 444798202657114485833116805)
    ·
      refine ⟨83399662998208966093709401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 444798202657114485833116805 83399662998208966093709401)
      ·
        refine ⟨62549747248656724570282051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83399662998208966093709401 62549747248656724570282051)
        ·
          refine ⟨93824620872985086855423077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62549747248656724570282051 93824620872985086855423077)
          ·
            refine ⟨17592116413684703785391827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93824620872985086855423077 17592116413684703785391827)
            ·
              refine ⟨26388174620527055678087741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17592116413684703785391827 26388174620527055678087741)
              ·
                refine ⟨9895565482697645879282903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26388174620527055678087741 9895565482697645879282903)
                ·
                  refine ⟨14843348224046468818924355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9895565482697645879282903 14843348224046468818924355)
                  ·
                    refine ⟨22265022336069703228386533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14843348224046468818924355 22265022336069703228386533)
                    ·
                      refine ⟨4174691688013069355322475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22265022336069703228386533 4174691688013069355322475)
                      ·
                        rfl

theorem cell23_8130183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 3, 1, 1, 4].length) (baseStart_8130183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8130183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8130183 prefixEnd_8130183 := by exact prefixLift 8130183
  have htrace : WordTrace (prefixWord ++ tailWord_8130183) baseStart_8130183 baseEnd_8130183 := by
    simpa [prefixWord, tailWord_8130183, baseEnd_8130183] using wordTrace_append hprefix tailTrace_8130183
  have hstable : (prefixWord ++ tailWord_8130183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8130183).length < 2 ^ (prefixWord ++ tailWord_8130183).sum := by decide
  have hdescent : baseEnd_8130183 < baseStart_8130183 := by decide
  rcases family_descends (prefixWord ++ tailWord_8130183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8130200 : List Nat := [2, 1, 2, 4, 1, 2, 1, 3, 3, 2, 2]
def baseStart_8130200 : Nat := 118140960795 + 8130200 * 2 ^ 59
def prefixEnd_8130200 : Nat := 4983230072969 + 3 ^ 40 * 8130200 * 2
def baseEnd_8130200 : Nat := 4174700417184195788809897

theorem tailTrace_8130200 : CollatzResearch.WordTrace tailWord_8130200 prefixEnd_8130200 4174700417184195788809897 := by
  unfold tailWord_8130200
  simp only [CollatzResearch.WordTrace]
  refine ⟨148266377572840701229390027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197688503430454268305853369 148266377572840701229390027)
  ·
    refine ⟨222399566359261051844085041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148266377572840701229390027 222399566359261051844085041)
    ·
      refine ⟨166799674769445788883063781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222399566359261051844085041 166799674769445788883063781)
      ·
        refine ⟨31274939019271085415574459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 166799674769445788883063781 31274939019271085415574459)
        ·
          refine ⟨46912408528906628123361689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31274939019271085415574459 46912408528906628123361689)
          ·
            refine ⟨35184306396679971092521267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46912408528906628123361689 35184306396679971092521267)
            ·
              refine ⟨52776459595019956638781901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35184306396679971092521267 52776459595019956638781901)
              ·
                refine ⟨19791172348132483739543213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52776459595019956638781901 19791172348132483739543213)
                ·
                  refine ⟨7421689630549681402328705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19791172348132483739543213 7421689630549681402328705)
                  ·
                    refine ⟨5566267222912261051746529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7421689630549681402328705 5566267222912261051746529)
                    ·
                      refine ⟨4174700417184195788809897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5566267222912261051746529 4174700417184195788809897)
                      ·
                        rfl

theorem cell23_8130200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 3, 3, 2, 2].length) (baseStart_8130200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8130200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8130200 prefixEnd_8130200 := by exact prefixLift 8130200
  have htrace : WordTrace (prefixWord ++ tailWord_8130200) baseStart_8130200 baseEnd_8130200 := by
    simpa [prefixWord, tailWord_8130200, baseEnd_8130200] using wordTrace_append hprefix tailTrace_8130200
  have hstable : (prefixWord ++ tailWord_8130200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8130200).length < 2 ^ (prefixWord ++ tailWord_8130200).sum := by decide
  have hdescent : baseEnd_8130200 < baseStart_8130200 := by decide
  rcases family_descends (prefixWord ++ tailWord_8130200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8130233 : List Nat := [1, 2, 1, 4, 1, 1, 3, 2, 4, 1, 3]
def baseStart_8130233 : Nat := 118140960795 + 8130233 * 2 ^ 59
def prefixEnd_8130233 : Nat := 4983230072969 + 3 ^ 40 * 8130233 * 2
def baseEnd_8130233 : Nat := 4174717362045794159697245

theorem tailTrace_8130233 : CollatzResearch.WordTrace tailWord_8130233 prefixEnd_8130233 4174717362045794159697245 := by
  unfold tailWord_8130233
  simp only [CollatzResearch.WordTrace]
  refine ⟨296533958754561849094731353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197689305836374566063154235 296533958754561849094731353)
  ·
    refine ⟨222400469065921386821048515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296533958754561849094731353 222400469065921386821048515)
    ·
      refine ⟨333600703598882080231572773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222400469065921386821048515 333600703598882080231572773)
      ·
        refine ⟨62550131924790390043419895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 333600703598882080231572773 62550131924790390043419895)
        ·
          refine ⟨93825197887185585065129843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62550131924790390043419895 93825197887185585065129843)
          ·
            refine ⟨140737796830778377597694765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93825197887185585065129843 140737796830778377597694765)
            ·
              refine ⟨52776673811541891599135537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 140737796830778377597694765 52776673811541891599135537)
              ·
                refine ⟨39582505358656418699351653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52776673811541891599135537 39582505358656418699351653)
                ·
                  refine ⟨7421719754748078506128435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39582505358656418699351653 7421719754748078506128435)
                  ·
                    refine ⟨11132579632122117759192653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7421719754748078506128435 11132579632122117759192653)
                    ·
                      refine ⟨4174717362045794159697245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11132579632122117759192653 4174717362045794159697245)
                      ·
                        rfl

theorem cell23_8130233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 2, 4, 1, 3].length) (baseStart_8130233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8130233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8130233 prefixEnd_8130233 := by exact prefixLift 8130233
  have htrace : WordTrace (prefixWord ++ tailWord_8130233) baseStart_8130233 baseEnd_8130233 := by
    simpa [prefixWord, tailWord_8130233, baseEnd_8130233] using wordTrace_append hprefix tailTrace_8130233
  have hstable : (prefixWord ++ tailWord_8130233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8130233).length < 2 ^ (prefixWord ++ tailWord_8130233).sum := by decide
  have hdescent : baseEnd_8130233 < baseStart_8130233 := by decide
  rcases family_descends (prefixWord ++ tailWord_8130233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8130234 : List Nat := [3, 1, 1, 1, 2, 6, 1, 3, 1, 2, 2]
def baseStart_8130234 : Nat := 118140960795 + 8130234 * 2 ^ 59
def prefixEnd_8130234 : Nat := 4983230072969 + 3 ^ 40 * 8130234 * 2
def baseEnd_8130234 : Nat := 4174717875526448655784741

theorem tailTrace_8130234 : CollatzResearch.WordTrace tailWord_8130234 prefixEnd_8130234 4174717875526448655784741 := by
  unfold tailWord_8130234
  simp only [CollatzResearch.WordTrace]
  refine ⟨74133498806889556566379439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197689330151705484177011837 74133498806889556566379439)
  ·
    refine ⟨111200248210334334849569159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74133498806889556566379439 111200248210334334849569159)
    ·
      refine ⟨166800372315501502274353739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111200248210334334849569159 166800372315501502274353739)
      ·
        refine ⟨250200558473252253411530609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166800372315501502274353739 250200558473252253411530609)
        ·
          refine ⟨187650418854939190058647957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 250200558473252253411530609 187650418854939190058647957)
          ·
            refine ⟨8796113383825274533999123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 187650418854939190058647957 8796113383825274533999123)
            ·
              refine ⟨13194170075737911800998685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8796113383825274533999123 13194170075737911800998685)
              ·
                refine ⟨4947813778401716925374507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13194170075737911800998685 4947813778401716925374507)
                ·
                  refine ⟨7421720667602575388061761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4947813778401716925374507 7421720667602575388061761)
                  ·
                    refine ⟨5566290500701931541046321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7421720667602575388061761 5566290500701931541046321)
                    ·
                      refine ⟨4174717875526448655784741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5566290500701931541046321 4174717875526448655784741)
                      ·
                        rfl

theorem cell23_8130234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 1, 3, 1, 2, 2].length) (baseStart_8130234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8130234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8130234 prefixEnd_8130234 := by exact prefixLift 8130234
  have htrace : WordTrace (prefixWord ++ tailWord_8130234) baseStart_8130234 baseEnd_8130234 := by
    simpa [prefixWord, tailWord_8130234, baseEnd_8130234] using wordTrace_append hprefix tailTrace_8130234
  have hstable : (prefixWord ++ tailWord_8130234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8130234).length < 2 ^ (prefixWord ++ tailWord_8130234).sum := by decide
  have hdescent : baseEnd_8130234 < baseStart_8130234 := by decide
  rcases family_descends (prefixWord ++ tailWord_8130234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8130276 : List Nat := [2, 3, 1, 1, 1, 3, 1, 1, 4, 1, 5]
def baseStart_8130276 : Nat := 118140960795 + 8130276 * 2 ^ 59
def prefixEnd_8130276 : Nat := 4983230072969 + 3 ^ 40 * 8130276 * 2
def baseEnd_8130276 : Nat := 4174739441713937491459547

theorem tailTrace_8130276 : CollatzResearch.WordTrace tailWord_8130276 prefixEnd_8130276 4174739441713937491459547 := by
  unfold tailWord_8130276
  simp only [CollatzResearch.WordTrace]
  refine ⟨148267763546703033719273341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197690351395604044959031121 148267763546703033719273341)
  ·
    refine ⟨55600411330013637644727503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148267763546703033719273341 55600411330013637644727503)
    ·
      refine ⟨83400616995020456467091255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55600411330013637644727503 83400616995020456467091255)
      ·
        refine ⟨125100925492530684700636883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83400616995020456467091255 125100925492530684700636883)
        ·
          refine ⟨187651388238796027050955325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125100925492530684700636883 187651388238796027050955325)
          ·
            refine ⟨70369270589548510144108247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 187651388238796027050955325 70369270589548510144108247)
            ·
              refine ⟨105553905884322765216162371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70369270589548510144108247 105553905884322765216162371)
              ·
                refine ⟨158330858826484147824243557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105553905884322765216162371 158330858826484147824243557)
                ·
                  refine ⟨29687036029965777717045667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 158330858826484147824243557 29687036029965777717045667)
                  ·
                    refine ⟨44530554044948666575568501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29687036029965777717045667 44530554044948666575568501)
                    ·
                      refine ⟨4174739441713937491459547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44530554044948666575568501 4174739441713937491459547)
                      ·
                        rfl

theorem cell23_8130276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 1, 4, 1, 5].length) (baseStart_8130276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8130276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8130276 prefixEnd_8130276 := by exact prefixLift 8130276
  have htrace : WordTrace (prefixWord ++ tailWord_8130276) baseStart_8130276 baseEnd_8130276 := by
    simpa [prefixWord, tailWord_8130276, baseEnd_8130276] using wordTrace_append hprefix tailTrace_8130276
  have hstable : (prefixWord ++ tailWord_8130276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8130276).length < 2 ^ (prefixWord ++ tailWord_8130276).sum := by decide
  have hdescent : baseEnd_8130276 < baseStart_8130276 := by decide
  rcases family_descends (prefixWord ++ tailWord_8130276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8130290 : List Nat := [3, 2, 1, 3, 1, 1, 3, 2, 1, 4, 2]
def baseStart_8130290 : Nat := 118140960795 + 8130290 * 2 ^ 59
def prefixEnd_8130290 : Nat := 4983230072969 + 3 ^ 40 * 8130290 * 2
def baseEnd_8130290 : Nat := 4174746630443100436684483

theorem tailTrace_8130290 : CollatzResearch.WordTrace tailWord_8130290 prefixEnd_8130290 4174746630443100436684483 := by
  unfold tailWord_8130290
  simp only [CollatzResearch.WordTrace]
  refine ⟨74134009428838836957389081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197690691810236898553037549 74134009428838836957389081)
  ·
    refine ⟨55600507071629127718041811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74134009428838836957389081 55600507071629127718041811)
    ·
      refine ⟨83400760607443691577062717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55600507071629127718041811 83400760607443691577062717)
      ·
        refine ⟨31275285227791384341398519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83400760607443691577062717 31275285227791384341398519)
        ·
          refine ⟨46912927841687076512097779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31275285227791384341398519 46912927841687076512097779)
          ·
            refine ⟨70369391762530614768146669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46912927841687076512097779 70369391762530614768146669)
            ·
              refine ⟨26388521910948980538055001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70369391762530614768146669 26388521910948980538055001)
              ·
                refine ⟨19791391433211735403541251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26388521910948980538055001 19791391433211735403541251)
                ·
                  refine ⟨29687087149817603105311877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19791391433211735403541251 29687087149817603105311877)
                  ·
                    refine ⟨5566328840590800582245977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29687087149817603105311877 5566328840590800582245977)
                    ·
                      refine ⟨4174746630443100436684483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5566328840590800582245977 4174746630443100436684483)
                      ·
                        rfl

theorem cell23_8130290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 2, 1, 4, 2].length) (baseStart_8130290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8130290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8130290 prefixEnd_8130290 := by exact prefixLift 8130290
  have htrace : WordTrace (prefixWord ++ tailWord_8130290) baseStart_8130290 baseEnd_8130290 := by
    simpa [prefixWord, tailWord_8130290, baseEnd_8130290] using wordTrace_append hprefix tailTrace_8130290
  have hstable : (prefixWord ++ tailWord_8130290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8130290).length < 2 ^ (prefixWord ++ tailWord_8130290).sum := by decide
  have hdescent : baseEnd_8130290 < baseStart_8130290 := by decide
  rcases family_descends (prefixWord ++ tailWord_8130290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8130294 : List Nat := [5, 1, 1, 1, 1, 4, 3, 1, 1, 3, 2]
def baseStart_8130294 : Nat := 118140960795 + 8130294 * 2 ^ 59
def prefixEnd_8130294 : Nat := 4983230072969 + 3 ^ 40 * 8130294 * 2
def baseEnd_8130294 : Nat := 4174748684365718421034465

theorem tailTrace_8130294 : CollatzResearch.WordTrace tailWord_8130294 prefixEnd_8130294 4174748684365718421034465 := by
  unfold tailWord_8130294
  simp only [CollatzResearch.WordTrace]
  refine ⟨18533511475458803532043871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 197690789071560571008467957 18533511475458803532043871)
  ·
    refine ⟨27800267213188205298065807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18533511475458803532043871 27800267213188205298065807)
    ·
      refine ⟨41700400819782307947098711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27800267213188205298065807 41700400819782307947098711)
      ·
        refine ⟨62550601229673461920648067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41700400819782307947098711 62550601229673461920648067)
        ·
          refine ⟨93825901844510192880972101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62550601229673461920648067 93825901844510192880972101)
          ·
            refine ⟨17592356595845661165182269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93825901844510192880972101 17592356595845661165182269)
            ·
              refine ⟨6597133723442122936943351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17592356595845661165182269 6597133723442122936943351)
              ·
                refine ⟨9895700585163184405415027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6597133723442122936943351 9895700585163184405415027)
                ·
                  refine ⟨14843550877744776608122541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9895700585163184405415027 14843550877744776608122541)
                  ·
                    refine ⟨5566331579154291228045953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14843550877744776608122541 5566331579154291228045953)
                    ·
                      refine ⟨4174748684365718421034465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5566331579154291228045953 4174748684365718421034465)
                      ·
                        rfl

theorem cell23_8130294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 3, 1, 1, 3, 2].length) (baseStart_8130294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8130294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8130294 prefixEnd_8130294 := by exact prefixLift 8130294
  have htrace : WordTrace (prefixWord ++ tailWord_8130294) baseStart_8130294 baseEnd_8130294 := by
    simpa [prefixWord, tailWord_8130294, baseEnd_8130294] using wordTrace_append hprefix tailTrace_8130294
  have hstable : (prefixWord ++ tailWord_8130294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8130294).length < 2 ^ (prefixWord ++ tailWord_8130294).sum := by decide
  have hdescent : baseEnd_8130294 < baseStart_8130294 := by decide
  rcases family_descends (prefixWord ++ tailWord_8130294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8130473 : List Nat := [1, 2, 1, 1, 1, 1, 4, 5, 1, 1, 5]
def baseStart_8130473 : Nat := 118140960795 + 8130473 * 2 ^ 59
def prefixEnd_8130473 : Nat := 4983230072969 + 3 ^ 40 * 8130473 * 2
def baseEnd_8130473 : Nat := 4174840597402873220696141

theorem tailTrace_8130473 : CollatzResearch.WordTrace tailWord_8130473 prefixEnd_8130473 4174840597402873220696141 := by
  unfold tailWord_8130473
  simp only [CollatzResearch.WordTrace]
  refine ⟨296542712273692370083468073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197695141515794913388978715 296542712273692370083468073)
  ·
    refine ⟨222407034205269277562601055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296542712273692370083468073 222407034205269277562601055)
    ·
      refine ⟨333610551307903916343901583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222407034205269277562601055 333610551307903916343901583)
      ·
        refine ⟨500415826961855874515852375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 333610551307903916343901583 500415826961855874515852375)
        ·
          refine ⟨750623740442783811773778563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 500415826961855874515852375 750623740442783811773778563)
          ·
            refine ⟨1125935610664175717660667845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 750623740442783811773778563 1125935610664175717660667845)
            ·
              refine ⟨211112926999532947061375221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1125935610664175717660667845 211112926999532947061375221)
              ·
                refine ⟨19791836906206213787003927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 211112926999532947061375221 19791836906206213787003927)
                ·
                  refine ⟨29687755359309320680505891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19791836906206213787003927 29687755359309320680505891)
                  ·
                    refine ⟨44531633038963981020758837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29687755359309320680505891 44531633038963981020758837)
                    ·
                      refine ⟨4174840597402873220696141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44531633038963981020758837 4174840597402873220696141)
                      ·
                        rfl

theorem cell23_8130473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 5, 1, 1, 5].length) (baseStart_8130473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8130473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8130473 prefixEnd_8130473 := by exact prefixLift 8130473
  have htrace : WordTrace (prefixWord ++ tailWord_8130473) baseStart_8130473 baseEnd_8130473 := by
    simpa [prefixWord, tailWord_8130473, baseEnd_8130473] using wordTrace_append hprefix tailTrace_8130473
  have hstable : (prefixWord ++ tailWord_8130473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8130473).length < 2 ^ (prefixWord ++ tailWord_8130473).sum := by decide
  have hdescent : baseEnd_8130473 < baseStart_8130473 := by decide
  rcases family_descends (prefixWord ++ tailWord_8130473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8130481 : List Nat := [1, 2, 2, 4, 2, 1, 4, 2, 1, 1, 3]
def baseStart_8130481 : Nat := 118140960795 + 8130481 * 2 ^ 59
def prefixEnd_8130481 : Nat := 4983230072969 + 3 ^ 40 * 8130481 * 2
def baseEnd_8130481 : Nat := 4174844705248109189396105

theorem tailTrace_8130481 : CollatzResearch.WordTrace tailWord_8130481 prefixEnd_8130481 4174844705248109189396105 := by
  unfold tailWord_8130481
  simp only [CollatzResearch.WordTrace]
  refine ⟨296543004057663387449759297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197695336038442258299839531 296543004057663387449759297)
  ·
    refine ⟨222407253043247540587319473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296543004057663387449759297 222407253043247540587319473)
    ·
      refine ⟨166805439782435655440489605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222407253043247540587319473 166805439782435655440489605)
      ·
        refine ⟨31276019959206685395091801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 166805439782435655440489605 31276019959206685395091801)
        ·
          refine ⟨23457014969405014046318851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31276019959206685395091801 23457014969405014046318851)
          ·
            refine ⟨35185522454107521069478277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23457014969405014046318851 35185522454107521069478277)
            ·
              refine ⟨6597285460145160200527177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35185522454107521069478277 6597285460145160200527177)
              ·
                refine ⟨4947964095108870150395383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6597285460145160200527177 4947964095108870150395383)
                ·
                  refine ⟨7421946142663305225593075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4947964095108870150395383 7421946142663305225593075)
                  ·
                    refine ⟨11132919213994957838389613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7421946142663305225593075 11132919213994957838389613)
                    ·
                      refine ⟨4174844705248109189396105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11132919213994957838389613 4174844705248109189396105)
                      ·
                        rfl

theorem cell23_8130481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 4, 2, 1, 1, 3].length) (baseStart_8130481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8130481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8130481 prefixEnd_8130481 := by exact prefixLift 8130481
  have htrace : WordTrace (prefixWord ++ tailWord_8130481) baseStart_8130481 baseEnd_8130481 := by
    simpa [prefixWord, tailWord_8130481, baseEnd_8130481] using wordTrace_append hprefix tailTrace_8130481
  have hstable : (prefixWord ++ tailWord_8130481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8130481).length < 2 ^ (prefixWord ++ tailWord_8130481).sum := by decide
  have hdescent : baseEnd_8130481 < baseStart_8130481 := by decide
  rcases family_descends (prefixWord ++ tailWord_8130481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8130483 : List Nat := [1, 1, 1, 2, 3, 1, 3, 2, 3, 2, 4]
def baseStart_8130483 : Nat := 118140960795 + 8130483 * 2 ^ 59
def prefixEnd_8130483 : Nat := 4983230072969 + 3 ^ 40 * 8130483 * 2
def baseEnd_8130483 : Nat := 4174845732209418181571095

theorem tailTrace_8130483 : CollatzResearch.WordTrace tailWord_8130483 prefixEnd_8130483 4174845732209418181571095 := by
  unfold tailWord_8130483
  simp only [CollatzResearch.WordTrace]
  refine ⟨296543077003656141791332103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197695384669104094527554735 296543077003656141791332103)
  ·
    refine ⟨444814615505484212686998155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296543077003656141791332103 444814615505484212686998155)
    ·
      refine ⟨667221923258226319030497233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 444814615505484212686998155 667221923258226319030497233)
      ·
        refine ⟨500416442443669739272872925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 667221923258226319030497233 500416442443669739272872925)
        ·
          refine ⟨187656165916376152227327347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 500416442443669739272872925 187656165916376152227327347)
          ·
            refine ⟨281484248874564228340991021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187656165916376152227327347 281484248874564228340991021)
            ·
              refine ⟨105556593327961585627871633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 281484248874564228340991021 105556593327961585627871633)
              ·
                refine ⟨79167444995971189220903725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105556593327961585627871633 79167444995971189220903725)
                ·
                  refine ⟨29687791873489195957838897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79167444995971189220903725 29687791873489195957838897)
                  ·
                    refine ⟨22265843905116896968379173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29687791873489195957838897 22265843905116896968379173)
                    ·
                      refine ⟨4174845732209418181571095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22265843905116896968379173 4174845732209418181571095)
                      ·
                        rfl

theorem cell23_8130483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 2, 3, 2, 4].length) (baseStart_8130483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8130483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8130483 prefixEnd_8130483 := by exact prefixLift 8130483
  have htrace : WordTrace (prefixWord ++ tailWord_8130483) baseStart_8130483 baseEnd_8130483 := by
    simpa [prefixWord, tailWord_8130483, baseEnd_8130483] using wordTrace_append hprefix tailTrace_8130483
  have hstable : (prefixWord ++ tailWord_8130483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8130483).length < 2 ^ (prefixWord ++ tailWord_8130483).sum := by decide
  have hdescent : baseEnd_8130483 < baseStart_8130483 := by decide
  rcases family_descends (prefixWord ++ tailWord_8130483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8130487 : List Nat := [1, 1, 3, 1, 3, 1, 1, 5, 3, 2, 2]
def baseStart_8130487 : Nat := 118140960795 + 8130487 * 2 ^ 59
def prefixEnd_8130487 : Nat := 4983230072969 + 3 ^ 40 * 8130487 * 2
def baseEnd_8130487 : Nat := 4174847786132036165921077

theorem tailTrace_8130487 : CollatzResearch.WordTrace tailWord_8130487 prefixEnd_8130487 4174847786132036165921077 := by
  unfold tailWord_8130487
  simp only [CollatzResearch.WordTrace]
  refine ⟨296543222895641650474477715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197695481930427766982985143 296543222895641650474477715)
  ·
    refine ⟨444814834343462475711716573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296543222895641650474477715 444814834343462475711716573)
    ·
      refine ⟨166805562878798428391893715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 444814834343462475711716573 166805562878798428391893715)
      ·
        refine ⟨250208344318197642587840573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166805562878798428391893715 250208344318197642587840573)
        ·
          refine ⟨93828129119324115970440215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 250208344318197642587840573 93828129119324115970440215)
          ·
            refine ⟨140742193678986173955660323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93828129119324115970440215 140742193678986173955660323)
            ·
              refine ⟨211113290518479260933490485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140742193678986173955660323 211113290518479260933490485)
              ·
                refine ⟨19791870986107430712514733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 211113290518479260933490485 19791870986107430712514733)
                ·
                  refine ⟨7421951619790286517193025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19791870986107430712514733 7421951619790286517193025)
                  ·
                    refine ⟨5566463714842714887894769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7421951619790286517193025 5566463714842714887894769)
                    ·
                      refine ⟨4174847786132036165921077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5566463714842714887894769 4174847786132036165921077)
                      ·
                        rfl

theorem cell23_8130487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 5, 3, 2, 2].length) (baseStart_8130487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8130487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8130487 prefixEnd_8130487 := by exact prefixLift 8130487
  have htrace : WordTrace (prefixWord ++ tailWord_8130487) baseStart_8130487 baseEnd_8130487 := by
    simpa [prefixWord, tailWord_8130487, baseEnd_8130487] using wordTrace_append hprefix tailTrace_8130487
  have hstable : (prefixWord ++ tailWord_8130487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8130487).length < 2 ^ (prefixWord ++ tailWord_8130487).sum := by decide
  have hdescent : baseEnd_8130487 < baseStart_8130487 := by decide
  rcases family_descends (prefixWord ++ tailWord_8130487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8130504 : List Nat := [2, 1, 3, 1, 4, 2, 1, 2, 3, 2, 2]
def baseStart_8130504 : Nat := 118140960795 + 8130504 * 2 ^ 59
def prefixEnd_8130504 : Nat := 4983230072969 + 3 ^ 40 * 8130504 * 2
def baseEnd_8130504 : Nat := 4174856515303162599408499

theorem tailTrace_8130504 : CollatzResearch.WordTrace tailWord_8130504 prefixEnd_8130504 4174856515303162599408499 := by
  unfold tailWord_8130504
  simp only [CollatzResearch.WordTrace]
  refine ⟨148271921468290031188923283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197695895291053374918564377 148271921468290031188923283)
  ·
    refine ⟨222407882202435046783384925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148271921468290031188923283 222407882202435046783384925)
    ·
      refine ⟨83402955825913142543769347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 222407882202435046783384925 83402955825913142543769347)
      ·
        refine ⟨125104433738869713815654021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83402955825913142543769347 125104433738869713815654021)
        ·
          refine ⟨23457081326038071340435129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 125104433738869713815654021 23457081326038071340435129)
          ·
            refine ⟨17592810994528553505326347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23457081326038071340435129 17592810994528553505326347)
            ·
              refine ⟨26389216491792830257989521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17592810994528553505326347 26389216491792830257989521)
              ·
                refine ⟨19791912368844622693492141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26389216491792830257989521 19791912368844622693492141)
                ·
                  refine ⟨7421967138316733510059553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19791912368844622693492141 7421967138316733510059553)
                  ·
                    refine ⟨5566475353737550132544665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7421967138316733510059553 5566475353737550132544665)
                    ·
                      refine ⟨4174856515303162599408499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5566475353737550132544665 4174856515303162599408499)
                      ·
                        rfl

theorem cell23_8130504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 2, 3, 2, 2].length) (baseStart_8130504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8130504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8130504 prefixEnd_8130504 := by exact prefixLift 8130504
  have htrace : WordTrace (prefixWord ++ tailWord_8130504) baseStart_8130504 baseEnd_8130504 := by
    simpa [prefixWord, tailWord_8130504, baseEnd_8130504] using wordTrace_append hprefix tailTrace_8130504
  have hstable : (prefixWord ++ tailWord_8130504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8130504).length < 2 ^ (prefixWord ++ tailWord_8130504).sum := by decide
  have hdescent : baseEnd_8130504 < baseStart_8130504 := by decide
  rcases family_descends (prefixWord ++ tailWord_8130504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8130510 : List Nat := [4, 1, 1, 1, 2, 2, 5, 7]
def baseStart_8130510 : Nat := 118140960795 + 8130510 * 2 ^ 59
def prefixEnd_8130510 : Nat := 4983230072969 + 3 ^ 40 * 8130510 * 2
def baseEnd_8130510 : Nat := 154624429488410725034573

theorem tailTrace_8130510 : CollatzResearch.WordTrace tailWord_8130510 prefixEnd_8130510 154624429488410725034573 := by
  unfold tailWord_8130510
  simp only [CollatzResearch.WordTrace]
  refine ⟨37068007721819790675320623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 197696041183038883601709989 37068007721819790675320623)
  ·
    refine ⟨55602011582729686012980935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37068007721819790675320623 55602011582729686012980935)
    ·
      refine ⟨83403017374094529019471403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55602011582729686012980935 83403017374094529019471403)
      ·
        refine ⟨125104526061141793529207105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83403017374094529019471403 125104526061141793529207105)
        ·
          refine ⟨93828394545856345146905329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125104526061141793529207105 93828394545856345146905329)
          ·
            refine ⟨70371295909392258860178997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93828394545856345146905329 70371295909392258860178997)
            ·
              refine ⟨6597308991505524268141781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 70371295909392258860178997 6597308991505524268141781)
              ·
                refine ⟨154624429488410725034573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6597308991505524268141781 154624429488410725034573)
                ·
                  rfl

theorem cell23_8130510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 5, 7].length) (baseStart_8130510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8130510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8130510 prefixEnd_8130510 := by exact prefixLift 8130510
  have htrace : WordTrace (prefixWord ++ tailWord_8130510) baseStart_8130510 baseEnd_8130510 := by
    simpa [prefixWord, tailWord_8130510, baseEnd_8130510] using wordTrace_append hprefix tailTrace_8130510
  have hstable : (prefixWord ++ tailWord_8130510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8130510).length < 2 ^ (prefixWord ++ tailWord_8130510).sum := by decide
  have hdescent : baseEnd_8130510 < baseStart_8130510 := by decide
  rcases family_descends (prefixWord ++ tailWord_8130510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8130518 : List Nat := [5, 2, 1, 1, 4, 1, 2, 1, 1, 5]
def baseStart_8130518 : Nat := 118140960795 + 8130518 * 2 ^ 59
def prefixEnd_8130518 : Nat := 4983230072969 + 3 ^ 40 * 8130518 * 2
def baseEnd_8130518 : Nat := 1391621234677441848211145

theorem tailTrace_8130518 : CollatzResearch.WordTrace tailWord_8130518 prefixEnd_8130518 1391621234677441848211145 := by
  unfold tailWord_8130518
  simp only [CollatzResearch.WordTrace]
  refine ⟨18534022097408083923053513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 197696235705686228512570805 18534022097408083923053513)
  ·
    refine ⟨13900516573056062942290135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18534022097408083923053513 13900516573056062942290135)
    ·
      refine ⟨20850774859584094413435203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13900516573056062942290135 20850774859584094413435203)
      ·
        refine ⟨31276162289376141620152805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20850774859584094413435203 31276162289376141620152805)
        ·
          refine ⟨5864280429258026553778651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31276162289376141620152805 5864280429258026553778651)
          ·
            refine ⟨8796420643887039830667977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5864280429258026553778651 8796420643887039830667977)
            ·
              refine ⟨6597315482915279873000983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8796420643887039830667977 6597315482915279873000983)
              ·
                refine ⟨9895973224372919809501475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6597315482915279873000983 9895973224372919809501475)
                ·
                  refine ⟨14843959836559379714252213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9895973224372919809501475 14843959836559379714252213)
                  ·
                    refine ⟨1391621234677441848211145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14843959836559379714252213 1391621234677441848211145)
                    ·
                      rfl

theorem cell23_8130518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 2, 1, 1, 5].length) (baseStart_8130518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8130518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8130518 prefixEnd_8130518 := by exact prefixLift 8130518
  have htrace : WordTrace (prefixWord ++ tailWord_8130518) baseStart_8130518 baseEnd_8130518 := by
    simpa [prefixWord, tailWord_8130518, baseEnd_8130518] using wordTrace_append hprefix tailTrace_8130518
  have hstable : (prefixWord ++ tailWord_8130518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8130518).length < 2 ^ (prefixWord ++ tailWord_8130518).sum := by decide
  have hdescent : baseEnd_8130518 < baseStart_8130518 := by decide
  rcases family_descends (prefixWord ++ tailWord_8130518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8130520 : List Nat := [2, 1, 2, 2, 2, 2, 1, 4, 1, 3, 3]
def baseStart_8130520 : Nat := 118140960795 + 8130520 * 2 ^ 59
def prefixEnd_8130520 : Nat := 4983230072969 + 3 ^ 40 * 8130520 * 2
def baseEnd_8130520 : Nat := 4174864730993634536808425

theorem tailTrace_8130520 : CollatzResearch.WordTrace tailWord_8130520 prefixEnd_8130520 4174864730993634536808425 := by
  unfold tailWord_8130520
  simp only [CollatzResearch.WordTrace]
  refine ⟨148272213252261048555214507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197696284336348064740286009 148272213252261048555214507)
  ·
    refine ⟨222408319878391572832821761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148272213252261048555214507 222408319878391572832821761)
    ·
      refine ⟨166806239908793679624616321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222408319878391572832821761 166806239908793679624616321)
      ·
        refine ⟨125104679931595259718462241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166806239908793679624616321 125104679931595259718462241)
        ·
          refine ⟨93828509948696444788846681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125104679931595259718462241 93828509948696444788846681)
          ·
            refine ⟨70371382461522333591635011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93828509948696444788846681 70371382461522333591635011)
            ·
              refine ⟨105557073692283500387452517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70371382461522333591635011 105557073692283500387452517)
              ·
                refine ⟨19791951317303156322647347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 105557073692283500387452517 19791951317303156322647347)
                ·
                  refine ⟨29687926975954734483971021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19791951317303156322647347 29687926975954734483971021)
                  ·
                    refine ⟨11132972615983025431489133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29687926975954734483971021 11132972615983025431489133)
                    ·
                      refine ⟨4174864730993634536808425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11132972615983025431489133 4174864730993634536808425)
                      ·
                        rfl

theorem cell23_8130520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 4, 1, 3, 3].length) (baseStart_8130520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8130520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8130520 prefixEnd_8130520 := by exact prefixLift 8130520
  have htrace : WordTrace (prefixWord ++ tailWord_8130520) baseStart_8130520 baseEnd_8130520 := by
    simpa [prefixWord, tailWord_8130520, baseEnd_8130520] using wordTrace_append hprefix tailTrace_8130520
  have hstable : (prefixWord ++ tailWord_8130520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8130520).length < 2 ^ (prefixWord ++ tailWord_8130520).sum := by decide
  have hdescent : baseEnd_8130520 < baseStart_8130520 := by decide
  rcases family_descends (prefixWord ++ tailWord_8130520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8130521 : List Nat := [1, 2, 1, 2, 7, 1, 2, 1, 1, 1, 4]
def baseStart_8130521 : Nat := 118140960795 + 8130521 * 2 ^ 59
def prefixEnd_8130521 : Nat := 4983230072969 + 3 ^ 40 * 8130521 * 2
def baseEnd_8130521 : Nat := 4174865244474289032895921

theorem tailTrace_8130521 : CollatzResearch.WordTrace tailWord_8130521 prefixEnd_8130521 4174865244474289032895921 := by
  unfold tailWord_8130521
  simp only [CollatzResearch.WordTrace]
  refine ⟨296544462977518474281215417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197696308651678982854143611 296544462977518474281215417)
  ·
    refine ⟨222408347233138855710911563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296544462977518474281215417 222408347233138855710911563)
    ·
      refine ⟨333612520849708283566367345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222408347233138855710911563 333612520849708283566367345)
      ·
        refine ⟨250209390637281212674775509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 333612520849708283566367345 250209390637281212674775509)
        ·
          refine ⟨5864282593061278422065051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 250209390637281212674775509 5864282593061278422065051)
          ·
            refine ⟨8796423889591917633097577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5864282593061278422065051 8796423889591917633097577)
            ·
              refine ⟨6597317917193938224823183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8796423889591917633097577 6597317917193938224823183)
              ·
                refine ⟨9895976875790907337234775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6597317917193938224823183 9895976875790907337234775)
                ·
                  refine ⟨14843965313686361005852163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9895976875790907337234775 14843965313686361005852163)
                  ·
                    refine ⟨22265947970529541508778245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14843965313686361005852163 22265947970529541508778245)
                    ·
                      refine ⟨4174865244474289032895921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22265947970529541508778245 4174865244474289032895921)
                      ·
                        rfl

theorem cell23_8130521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 2, 1, 1, 1, 4].length) (baseStart_8130521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8130521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8130521 prefixEnd_8130521 := by exact prefixLift 8130521
  have htrace : WordTrace (prefixWord ++ tailWord_8130521) baseStart_8130521 baseEnd_8130521 := by
    simpa [prefixWord, tailWord_8130521, baseEnd_8130521] using wordTrace_append hprefix tailTrace_8130521
  have hstable : (prefixWord ++ tailWord_8130521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8130521).length < 2 ^ (prefixWord ++ tailWord_8130521).sum := by decide
  have hdescent : baseEnd_8130521 < baseStart_8130521 := by decide
  rcases family_descends (prefixWord ++ tailWord_8130521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8130563 : List Nat := [1, 1, 1, 3, 2, 1, 1, 2, 3, 3, 5]
def baseStart_8130563 : Nat := 118140960795 + 8130563 * 2 ^ 59
def prefixEnd_8130563 : Nat := 4983230072969 + 3 ^ 40 * 8130563 * 2
def baseEnd_8130563 : Nat := 4174886810661777868570727

theorem tailTrace_8130563 : CollatzResearch.WordTrace tailWord_8130563 prefixEnd_8130563 4174886810661777868570727 := by
  unfold tailWord_8130563
  simp only [CollatzResearch.WordTrace]
  refine ⟨296545994843366315454244343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197697329895577543636162895 296545994843366315454244343)
  ·
    refine ⟨444818992265049473181366515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296545994843366315454244343 444818992265049473181366515)
    ·
      refine ⟨667228488397574209772049773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 444818992265049473181366515 667228488397574209772049773)
      ·
        refine ⟨250210683149090328664518665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 667228488397574209772049773 250210683149090328664518665)
        ·
          refine ⟨187658012361817746498388999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 250210683149090328664518665 187658012361817746498388999)
          ·
            refine ⟨281487018542726619747583499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187658012361817746498388999 281487018542726619747583499)
            ·
              refine ⟨422230527814089929621375249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 281487018542726619747583499 422230527814089929621375249)
              ·
                refine ⟨316672895860567447216031437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 422230527814089929621375249 316672895860567447216031437)
                ·
                  refine ⟨118752335947712792706011789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 316672895860567447216031437 118752335947712792706011789)
                  ·
                    refine ⟨44532125980392297264754421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 118752335947712792706011789 44532125980392297264754421)
                    ·
                      refine ⟨4174886810661777868570727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44532125980392297264754421 4174886810661777868570727)
                      ·
                        rfl

theorem cell23_8130563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 2, 3, 3, 5].length) (baseStart_8130563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8130563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8130563 prefixEnd_8130563 := by exact prefixLift 8130563
  have htrace : WordTrace (prefixWord ++ tailWord_8130563) baseStart_8130563 baseEnd_8130563 := by
    simpa [prefixWord, tailWord_8130563, baseEnd_8130563] using wordTrace_append hprefix tailTrace_8130563
  have hstable : (prefixWord ++ tailWord_8130563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8130563).length < 2 ^ (prefixWord ++ tailWord_8130563).sum := by decide
  have hdescent : baseEnd_8130563 < baseStart_8130563 := by decide
  rcases family_descends (prefixWord ++ tailWord_8130563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8130594 : List Nat := [3, 3, 1, 1, 1, 2, 1, 3, 4, 2, 2]
def baseStart_8130594 : Nat := 118140960795 + 8130594 * 2 ^ 59
def prefixEnd_8130594 : Nat := 4983230072969 + 3 ^ 40 * 8130594 * 2
def baseEnd_8130594 : Nat := 4174902728562067247283085

theorem tailTrace_8130594 : CollatzResearch.WordTrace tailWord_8130594 prefixEnd_8130594 4174902728562067247283085 := by
  unfold tailWord_8130594
  simp only [CollatzResearch.WordTrace]
  refine ⟨74136781376563501937155709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197698083670836005165748557 74136781376563501937155709)
  ·
    refine ⟨27801293016211313226433391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74136781376563501937155709 27801293016211313226433391)
    ·
      refine ⟨41701939524316969839650087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27801293016211313226433391 41701939524316969839650087)
      ·
        refine ⟨62552909286475454759475131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41701939524316969839650087 62552909286475454759475131)
        ·
          refine ⟨93829363929713182139212697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62552909286475454759475131 93829363929713182139212697)
          ·
            refine ⟨70372022947284886604409523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93829363929713182139212697 70372022947284886604409523)
            ·
              refine ⟨105558034420927329906614285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70372022947284886604409523 105558034420927329906614285)
              ·
                refine ⟨39584262907847748714980357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105558034420927329906614285 39584262907847748714980357)
                ·
                  refine ⟨7422049295221452884058817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39584262907847748714980357 7422049295221452884058817)
                  ·
                    refine ⟨5566536971416089663044113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7422049295221452884058817 5566536971416089663044113)
                    ·
                      refine ⟨4174902728562067247283085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5566536971416089663044113 4174902728562067247283085)
                      ·
                        rfl

theorem cell23_8130594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 3, 4, 2, 2].length) (baseStart_8130594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8130594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8130594 prefixEnd_8130594 := by exact prefixLift 8130594
  have htrace : WordTrace (prefixWord ++ tailWord_8130594) baseStart_8130594 baseEnd_8130594 := by
    simpa [prefixWord, tailWord_8130594, baseEnd_8130594] using wordTrace_append hprefix tailTrace_8130594
  have hstable : (prefixWord ++ tailWord_8130594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8130594).length < 2 ^ (prefixWord ++ tailWord_8130594).sum := by decide
  have hdescent : baseEnd_8130594 < baseStart_8130594 := by decide
  rcases family_descends (prefixWord ++ tailWord_8130594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8130603 : List Nat := [1, 1, 1, 1, 2, 1, 4, 1, 2, 1, 8]
def baseStart_8130603 : Nat := 118140960795 + 8130603 * 2 ^ 59
def prefixEnd_8130603 : Nat := 4983230072969 + 3 ^ 40 * 8130603 * 2
def baseEnd_8130603 : Nat := 4174907349887957712070543

theorem tailTrace_8130603 : CollatzResearch.WordTrace tailWord_8130603 prefixEnd_8130603 4174907349887957712070543 := by
  unfold tailWord_8130603
  simp only [CollatzResearch.WordTrace]
  refine ⟨296547453763221402285700463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197698302508814268190466975 296547453763221402285700463)
  ·
    refine ⟨444821180644832103428550695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296547453763221402285700463 444821180644832103428550695)
    ·
      refine ⟨667231770967248155142826043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 444821180644832103428550695 667231770967248155142826043)
      ·
        refine ⟨1000847656450872232714239065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 667231770967248155142826043 1000847656450872232714239065)
        ·
          refine ⟨750635742338154174535679299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1000847656450872232714239065 750635742338154174535679299)
          ·
            refine ⟨1125953613507231261803518949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 750635742338154174535679299 1125953613507231261803518949)
            ·
              refine ⟨211116302532605861588159803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1125953613507231261803518949 211116302532605861588159803)
              ·
                refine ⟨316674453798908792382239705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 211116302532605861588159803 316674453798908792382239705)
                ·
                  refine ⟨237505840349181594286679779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 316674453798908792382239705 237505840349181594286679779)
                  ·
                    refine ⟨356258760523772391430019669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 237505840349181594286679779 356258760523772391430019669)
                    ·
                      refine ⟨4174907349887957712070543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 356258760523772391430019669 4174907349887957712070543)
                      ·
                        rfl

theorem cell23_8130603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 1, 2, 1, 8].length) (baseStart_8130603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8130603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8130603 prefixEnd_8130603 := by exact prefixLift 8130603
  have htrace : WordTrace (prefixWord ++ tailWord_8130603) baseStart_8130603 baseEnd_8130603 := by
    simpa [prefixWord, tailWord_8130603, baseEnd_8130603] using wordTrace_append hprefix tailTrace_8130603
  have hstable : (prefixWord ++ tailWord_8130603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8130603).length < 2 ^ (prefixWord ++ tailWord_8130603).sum := by decide
  have hdescent : baseEnd_8130603 < baseStart_8130603 := by decide
  rcases family_descends (prefixWord ++ tailWord_8130603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8130611 : List Nat := [1, 1, 1, 2, 4, 1, 6, 1, 2, 2, 2]
def baseStart_8130611 : Nat := 118140960795 + 8130611 * 2 ^ 59
def prefixEnd_8130611 : Nat := 4983230072969 + 3 ^ 40 * 8130611 * 2
def baseEnd_8130611 : Nat := 4174911457733193680770507

theorem tailTrace_8130611 : CollatzResearch.WordTrace tailWord_8130611 prefixEnd_8130611 4174911457733193680770507 := by
  unfold tailWord_8130611
  simp only [CollatzResearch.WordTrace]
  refine ⟨296547745547192419651991687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197698497031461613101327791 296547745547192419651991687)
  ·
    refine ⟨444821618320788629477987531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296547745547192419651991687 444821618320788629477987531)
    ·
      refine ⟨667232427481182944216981297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 444821618320788629477987531 667232427481182944216981297)
      ·
        refine ⟨500424320610887208162735973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 667232427481182944216981297 500424320610887208162735973)
        ·
          refine ⟨93829560114541351530512995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 500424320610887208162735973 93829560114541351530512995)
          ·
            refine ⟨140744340171812027295769493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93829560114541351530512995 140744340171812027295769493)
            ·
              refine ⟨6597390945553688779489195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 140744340171812027295769493 6597390945553688779489195)
              ·
                refine ⟨9896086418330533169233793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6597390945553688779489195 9896086418330533169233793)
                ·
                  refine ⟨7422064813747899876925345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9896086418330533169233793 7422064813747899876925345)
                  ·
                    refine ⟨5566548610310924907694009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7422064813747899876925345 5566548610310924907694009)
                    ·
                      refine ⟨4174911457733193680770507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5566548610310924907694009 4174911457733193680770507)
                      ·
                        rfl

theorem cell23_8130611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 6, 1, 2, 2, 2].length) (baseStart_8130611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8130611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8130611 prefixEnd_8130611 := by exact prefixLift 8130611
  have htrace : WordTrace (prefixWord ++ tailWord_8130611) baseStart_8130611 baseEnd_8130611 := by
    simpa [prefixWord, tailWord_8130611, baseEnd_8130611] using wordTrace_append hprefix tailTrace_8130611
  have hstable : (prefixWord ++ tailWord_8130611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8130611).length < 2 ^ (prefixWord ++ tailWord_8130611).sum := by decide
  have hdescent : baseEnd_8130611 < baseStart_8130611 := by decide
  rcases family_descends (prefixWord ++ tailWord_8130611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8130684 : List Nat := [2, 2, 2, 1, 1, 6, 1, 1, 2, 1, 4]
def baseStart_8130684 : Nat := 118140960795 + 8130684 * 2 ^ 59
def prefixEnd_8130684 : Nat := 4983230072969 + 3 ^ 40 * 8130684 * 2
def baseEnd_8130684 : Nat := 4174948941820971895157671

theorem tailTrace_8130684 : CollatzResearch.WordTrace tailWord_8130684 prefixEnd_8130684 4174948941820971895157671 := by
  unfold tailWord_8130684
  simp only [CollatzResearch.WordTrace]
  refine ⟨148275204037963976559699553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197700272050618635412932737 148275204037963976559699553)
  ·
    refine ⟨111206403028472982419774665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148275204037963976559699553 111206403028472982419774665)
    ·
      refine ⟨83404802271354736814830999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111206403028472982419774665 83404802271354736814830999)
      ·
        refine ⟨125107203407032105222246499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83404802271354736814830999 125107203407032105222246499)
        ·
          refine ⟨187660805110548157833369749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125107203407032105222246499 187660805110548157833369749)
          ·
            refine ⟨8796600239556944898439207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 187660805110548157833369749 8796600239556944898439207)
            ·
              refine ⟨13194900359335417347658811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8796600239556944898439207 13194900359335417347658811)
              ·
                refine ⟨19792350539003126021488217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13194900359335417347658811 19792350539003126021488217)
                ·
                  refine ⟨14844262904252344516116163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19792350539003126021488217 14844262904252344516116163)
                  ·
                    refine ⟨22266394356378516774174245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14844262904252344516116163 22266394356378516774174245)
                    ·
                      refine ⟨4174948941820971895157671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22266394356378516774174245 4174948941820971895157671)
                      ·
                        rfl

theorem cell23_8130684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 1, 1, 2, 1, 4].length) (baseStart_8130684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8130684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8130684 prefixEnd_8130684 := by exact prefixLift 8130684
  have htrace : WordTrace (prefixWord ++ tailWord_8130684) baseStart_8130684 baseEnd_8130684 := by
    simpa [prefixWord, tailWord_8130684, baseEnd_8130684] using wordTrace_append hprefix tailTrace_8130684
  have hstable : (prefixWord ++ tailWord_8130684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8130684).length < 2 ^ (prefixWord ++ tailWord_8130684).sum := by decide
  have hdescent : baseEnd_8130684 < baseStart_8130684 := by decide
  rcases family_descends (prefixWord ++ tailWord_8130684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8130744 : List Nat := [2, 1, 2, 1, 2, 1, 4, 3, 2, 3, 2]
def baseStart_8130744 : Nat := 118140960795 + 8130744 * 2 ^ 59
def prefixEnd_8130744 : Nat := 4983230072969 + 3 ^ 40 * 8130744 * 2
def baseEnd_8130744 : Nat := 4174979750660241660407395

theorem tailTrace_8130744 : CollatzResearch.WordTrace tailWord_8130744 prefixEnd_8130744 4174979750660241660407395 := by
  unfold tailWord_8130744
  simp only [CollatzResearch.WordTrace]
  refine ⟨148276298227855291683291643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197701730970473722244388857 148276298227855291683291643)
  ·
    refine ⟨222414447341782937524937465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148276298227855291683291643 222414447341782937524937465)
    ·
      refine ⟨166810835506337203143703099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222414447341782937524937465 166810835506337203143703099)
      ·
        refine ⟨250216253259505804715554649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166810835506337203143703099 250216253259505804715554649)
        ·
          refine ⟨187662189944629353536665987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 250216253259505804715554649 187662189944629353536665987)
          ·
            refine ⟨281493284916944030304998981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187662189944629353536665987 281493284916944030304998981)
            ·
              refine ⟨52779990921927005682187309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 281493284916944030304998981 52779990921927005682187309)
              ·
                refine ⟨19792496595722627130820241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52779990921927005682187309 19792496595722627130820241)
                ·
                  refine ⟨14844372446791970348115181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19792496595722627130820241 14844372446791970348115181)
                  ·
                    refine ⟨5566639667546988880543193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14844372446791970348115181 5566639667546988880543193)
                    ·
                      refine ⟨4174979750660241660407395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5566639667546988880543193 4174979750660241660407395)
                      ·
                        rfl

theorem cell23_8130744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 3, 2, 3, 2].length) (baseStart_8130744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8130744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8130744 prefixEnd_8130744 := by exact prefixLift 8130744
  have htrace : WordTrace (prefixWord ++ tailWord_8130744) baseStart_8130744 baseEnd_8130744 := by
    simpa [prefixWord, tailWord_8130744, baseEnd_8130744] using wordTrace_append hprefix tailTrace_8130744
  have hstable : (prefixWord ++ tailWord_8130744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8130744).length < 2 ^ (prefixWord ++ tailWord_8130744).sum := by decide
  have hdescent : baseEnd_8130744 < baseStart_8130744 := by decide
  rcases family_descends (prefixWord ++ tailWord_8130744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8130767 : List Nat := [1, 1, 2, 1, 1, 3, 3, 3, 4, 4]
def baseStart_8130767 : Nat := 118140960795 + 8130767 * 2 ^ 59
def prefixEnd_8130767 : Nat := 4983230072969 + 3 ^ 40 * 8130767 * 2
def baseEnd_8130767 : Nat := 1391663853571765023473263

theorem tailTrace_8130767 : CollatzResearch.WordTrace tailWord_8130767 prefixEnd_8130767 1391663853571765023473263 := by
  unfold tailWord_8130767
  simp only [CollatzResearch.WordTrace]
  refine ⟨296553435334627258294670555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197702290223084838863113703 296553435334627258294670555)
  ·
    refine ⟨444830153001940887442005833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296553435334627258294670555 444830153001940887442005833)
    ·
      refine ⟨333622614751455665581504375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 444830153001940887442005833 333622614751455665581504375)
      ·
        refine ⟨500433922127183498372256563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 333622614751455665581504375 500433922127183498372256563)
        ·
          refine ⟨750650883190775247558384845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 500433922127183498372256563 750650883190775247558384845)
          ·
            refine ⟨281494081196540717834394317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 750650883190775247558384845 281494081196540717834394317)
            ·
              refine ⟨105560280448702769187897869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 281494081196540717834394317 105560280448702769187897869)
              ·
                refine ⟨39585105168263538445461701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105560280448702769187897869 39585105168263538445461701)
                ·
                  refine ⟨7422207219049413458524069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39585105168263538445461701 7422207219049413458524069)
                  ·
                    refine ⟨1391663853571765023473263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7422207219049413458524069 1391663853571765023473263)
                    ·
                      rfl

theorem cell23_8130767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 3, 4, 4].length) (baseStart_8130767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8130767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8130767 prefixEnd_8130767 := by exact prefixLift 8130767
  have htrace : WordTrace (prefixWord ++ tailWord_8130767) baseStart_8130767 baseEnd_8130767 := by
    simpa [prefixWord, tailWord_8130767, baseEnd_8130767] using wordTrace_append hprefix tailTrace_8130767
  have hstable : (prefixWord ++ tailWord_8130767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8130767).length < 2 ^ (prefixWord ++ tailWord_8130767).sum := by decide
  have hdescent : baseEnd_8130767 < baseStart_8130767 := by decide
  rcases family_descends (prefixWord ++ tailWord_8130767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8130777 : List Nat := [1, 2, 1, 2, 3, 1, 4, 2, 1, 1, 5]
def baseStart_8130777 : Nat := 118140960795 + 8130777 * 2 ^ 59
def prefixEnd_8130777 : Nat := 4983230072969 + 3 ^ 40 * 8130777 * 2
def baseEnd_8130777 : Nat := 4174996695521840031294743

theorem tailTrace_8130777 : CollatzResearch.WordTrace tailWord_8130777 prefixEnd_8130777 4174996695521840031294743 := by
  unfold tailWord_8130777
  simp only [CollatzResearch.WordTrace]
  refine ⟨296553800064591030002534585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197702533376394020001689723 296553800064591030002534585)
  ·
    refine ⟨222415350048443272501900939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296553800064591030002534585 222415350048443272501900939)
    ·
      refine ⟨333623025072664908752851409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222415350048443272501900939 333623025072664908752851409)
      ·
        refine ⟨250217268804498681564638557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 333623025072664908752851409 250217268804498681564638557)
        ·
          refine ⟨93831475801687005586739459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 250217268804498681564638557 93831475801687005586739459)
          ·
            refine ⟨140747213702530508380109189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93831475801687005586739459 140747213702530508380109189)
            ·
              refine ⟨26390102569224470321270473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 140747213702530508380109189 26390102569224470321270473)
              ·
                refine ⟨19792576926918352740952855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26390102569224470321270473 19792576926918352740952855)
                ·
                  refine ⟨29688865390377529111429283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19792576926918352740952855 29688865390377529111429283)
                  ·
                    refine ⟨44533298085566293667143925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29688865390377529111429283 44533298085566293667143925)
                    ·
                      refine ⟨4174996695521840031294743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44533298085566293667143925 4174996695521840031294743)
                      ·
                        rfl

theorem cell23_8130777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 2, 1, 1, 5].length) (baseStart_8130777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8130777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8130777 prefixEnd_8130777 := by exact prefixLift 8130777
  have htrace : WordTrace (prefixWord ++ tailWord_8130777) baseStart_8130777 baseEnd_8130777 := by
    simpa [prefixWord, tailWord_8130777, baseEnd_8130777] using wordTrace_append hprefix tailTrace_8130777
  have hstable : (prefixWord ++ tailWord_8130777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8130777).length < 2 ^ (prefixWord ++ tailWord_8130777).sum := by decide
  have hdescent : baseEnd_8130777 < baseStart_8130777 := by decide
  rcases family_descends (prefixWord ++ tailWord_8130777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8130784 : List Nat := [2, 1, 1, 3, 1, 3, 3, 3, 2, 4]
def baseStart_8130784 : Nat := 118140960795 + 8130784 * 2 ^ 59
def prefixEnd_8130784 : Nat := 4983230072969 + 3 ^ 40 * 8130784 * 2
def baseEnd_8130784 : Nat := 1391666763295473834635737

theorem tailTrace_8130784 : CollatzResearch.WordTrace tailWord_8130784 prefixEnd_8130784 1391666763295473834635737 := by
  unfold tailWord_8130784
  simp only [CollatzResearch.WordTrace]
  refine ⟨148277027687782835099019703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197702703583710446798692937 148277027687782835099019703)
  ·
    refine ⟨222415541531674252648529555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148277027687782835099019703 222415541531674252648529555)
    ·
      refine ⟨333623312297511378972794333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222415541531674252648529555 333623312297511378972794333)
      ·
        refine ⟨125108742111566767114797875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 333623312297511378972794333 125108742111566767114797875)
        ·
          refine ⟨187663113167350150672196813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125108742111566767114797875 187663113167350150672196813)
          ·
            refine ⟨70373667437756306502073805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 187663113167350150672196813 70373667437756306502073805)
            ·
              refine ⟨26390125289158614938277677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70373667437756306502073805 26390125289158614938277677)
              ·
                refine ⟨9896296983434480601854129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26390125289158614938277677 9896296983434480601854129)
                ·
                  refine ⟨7422222737575860451390597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9896296983434480601854129 7422222737575860451390597)
                  ·
                    refine ⟨1391666763295473834635737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7422222737575860451390597 1391666763295473834635737)
                    ·
                      rfl

theorem cell23_8130784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 3, 2, 4].length) (baseStart_8130784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8130784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8130784 prefixEnd_8130784 := by exact prefixLift 8130784
  have htrace : WordTrace (prefixWord ++ tailWord_8130784) baseStart_8130784 baseEnd_8130784 := by
    simpa [prefixWord, tailWord_8130784, baseEnd_8130784] using wordTrace_append hprefix tailTrace_8130784
  have hstable : (prefixWord ++ tailWord_8130784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8130784).length < 2 ^ (prefixWord ++ tailWord_8130784).sum := by decide
  have hdescent : baseEnd_8130784 < baseStart_8130784 := by decide
  rcases family_descends (prefixWord ++ tailWord_8130784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8130791 : List Nat := [1, 1, 5, 3, 1, 1, 3, 2, 1, 1, 4]
def baseStart_8130791 : Nat := 118140960795 + 8130791 * 2 ^ 59
def prefixEnd_8130791 : Nat := 4983230072969 + 3 ^ 40 * 8130791 * 2
def baseEnd_8130791 : Nat := 4175003884251002976519679

theorem tailTrace_8130791 : CollatzResearch.WordTrace tailWord_8130791 prefixEnd_8130791 4175003884251002976519679 := by
  unfold tailWord_8130791
  simp only [CollatzResearch.WordTrace]
  refine ⟨296554310686540310393544227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197702873791026873595696151 296554310686540310393544227)
  ·
    refine ⟨444831466029810465590316341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296554310686540310393544227 444831466029810465590316341)
    ·
      refine ⟨41702949940294731149092157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 444831466029810465590316341 41702949940294731149092157)
      ·
        refine ⟨15638606227610524180909559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41702949940294731149092157 15638606227610524180909559)
        ·
          refine ⟨23457909341415786271364339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15638606227610524180909559 23457909341415786271364339)
          ·
            refine ⟨35186864012123679407046509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23457909341415786271364339 35186864012123679407046509)
            ·
              refine ⟨13195074004546379777642441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35186864012123679407046509 13195074004546379777642441)
              ·
                refine ⟨9896305503409784833231831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13195074004546379777642441 9896305503409784833231831)
                ·
                  refine ⟨14844458255114677249847747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9896305503409784833231831 14844458255114677249847747)
                  ·
                    refine ⟨22266687382672015874771621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14844458255114677249847747 22266687382672015874771621)
                    ·
                      refine ⟨4175003884251002976519679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22266687382672015874771621 4175003884251002976519679)
                      ·
                        rfl

theorem cell23_8130791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 3, 2, 1, 1, 4].length) (baseStart_8130791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8130791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8130791 prefixEnd_8130791 := by exact prefixLift 8130791
  have htrace : WordTrace (prefixWord ++ tailWord_8130791) baseStart_8130791 baseEnd_8130791 := by
    simpa [prefixWord, tailWord_8130791, baseEnd_8130791] using wordTrace_append hprefix tailTrace_8130791
  have hstable : (prefixWord ++ tailWord_8130791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8130791).length < 2 ^ (prefixWord ++ tailWord_8130791).sum := by decide
  have hdescent : baseEnd_8130791 < baseStart_8130791 := by decide
  rcases family_descends (prefixWord ++ tailWord_8130791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8130794 : List Nat := [3, 1, 3, 1, 1, 2, 3, 1, 3, 2, 3]
def baseStart_8130794 : Nat := 118140960795 + 8130794 * 2 ^ 59
def prefixEnd_8130794 : Nat := 4983230072969 + 3 ^ 40 * 8130794 * 2
def baseEnd_8130794 : Nat := 4175005424692966464782165

theorem tailTrace_8130794 : CollatzResearch.WordTrace tailWord_8130794 prefixEnd_8130794 4175005424692966464782165 := by
  unfold tailWord_8130794
  simp only [CollatzResearch.WordTrace]
  refine ⟨74138605026382360476475859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197702946737019627937268957 74138605026382360476475859)
  ·
    refine ⟨111207907539573540714713789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74138605026382360476475859 111207907539573540714713789)
    ·
      refine ⟨41702965327340077768017671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111207907539573540714713789 41702965327340077768017671)
      ·
        refine ⟨62554447991010116652026507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41702965327340077768017671 62554447991010116652026507)
        ·
          refine ⟨93831671986515174978039761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62554447991010116652026507 93831671986515174978039761)
          ·
            refine ⟨70373753989886381233529821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93831671986515174978039761 70373753989886381233529821)
            ·
              refine ⟨26390157746207392962573683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70373753989886381233529821 26390157746207392962573683)
              ·
                refine ⟨39585236619311089443860525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26390157746207392962573683 39585236619311089443860525)
                ·
                  refine ⟨14844463732241658541447697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39585236619311089443860525 14844463732241658541447697)
                  ·
                    refine ⟨11133347799181243906085773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14844463732241658541447697 11133347799181243906085773)
                    ·
                      refine ⟨4175005424692966464782165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11133347799181243906085773 4175005424692966464782165)
                      ·
                        rfl

theorem cell23_8130794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 1, 3, 2, 3].length) (baseStart_8130794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8130794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8130794 prefixEnd_8130794 := by exact prefixLift 8130794
  have htrace : WordTrace (prefixWord ++ tailWord_8130794) baseStart_8130794 baseEnd_8130794 := by
    simpa [prefixWord, tailWord_8130794, baseEnd_8130794] using wordTrace_append hprefix tailTrace_8130794
  have hstable : (prefixWord ++ tailWord_8130794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8130794).length < 2 ^ (prefixWord ++ tailWord_8130794).sum := by decide
  have hdescent : baseEnd_8130794 < baseStart_8130794 := by decide
  rcases family_descends (prefixWord ++ tailWord_8130794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8130818 : List Nat := [3, 4, 1, 1, 2, 2, 2, 2, 2, 4]
def baseStart_8130818 : Nat := 118140960795 + 8130818 * 2 ^ 59
def prefixEnd_8130818 : Nat := 4983230072969 + 3 ^ 40 * 8130818 * 2
def baseEnd_8130818 : Nat := 1391672582742891456960685

theorem tailTrace_8130818 : CollatzResearch.WordTrace tailWord_8130818 prefixEnd_8130818 1391672582742891456960685 := by
  unfold tailWord_8130818
  simp only [CollatzResearch.WordTrace]
  refine ⟨74138823864360623501194277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197703530304961662669851405 74138823864360623501194277)
  ·
    refine ⟨13901029474567616906473927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74138823864360623501194277 13901029474567616906473927)
    ·
      refine ⟨20851544211851425359710891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13901029474567616906473927 20851544211851425359710891)
      ·
        refine ⟨31277316317777138039566337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20851544211851425359710891 31277316317777138039566337)
        ·
          refine ⟨23457987238332853529674753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31277316317777138039566337 23457987238332853529674753)
          ·
            refine ⟨17593490428749640147256065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23457987238332853529674753 17593490428749640147256065)
            ·
              refine ⟨13195117821562230110442049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17593490428749640147256065 13195117821562230110442049)
              ·
                refine ⟨9896338366171672582831537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13195117821562230110442049 9896338366171672582831537)
                ·
                  refine ⟨7422253774628754437123653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9896338366171672582831537 7422253774628754437123653)
                  ·
                    refine ⟨1391672582742891456960685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7422253774628754437123653 1391672582742891456960685)
                    ·
                      rfl

theorem cell23_8130818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 2, 2, 2, 4].length) (baseStart_8130818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8130818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8130818 prefixEnd_8130818 := by exact prefixLift 8130818
  have htrace : WordTrace (prefixWord ++ tailWord_8130818) baseStart_8130818 baseEnd_8130818 := by
    simpa [prefixWord, tailWord_8130818, baseEnd_8130818] using wordTrace_append hprefix tailTrace_8130818
  have hstable : (prefixWord ++ tailWord_8130818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8130818).length < 2 ^ (prefixWord ++ tailWord_8130818).sum := by decide
  have hdescent : baseEnd_8130818 < baseStart_8130818 := by decide
  rcases family_descends (prefixWord ++ tailWord_8130818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8130825 : List Nat := [1, 2, 1, 1, 3, 4, 4, 2, 1, 2, 2]
def baseStart_8130825 : Nat := 118140960795 + 8130825 * 2 ^ 59
def prefixEnd_8130825 : Nat := 4983230072969 + 3 ^ 40 * 8130825 * 2
def baseEnd_8130825 : Nat := 4175021342593255843494523

theorem tailTrace_8130825 : CollatzResearch.WordTrace tailWord_8130825 prefixEnd_8130825 4175021342593255843494523 := by
  unfold tailWord_8130825
  simp only [CollatzResearch.WordTrace]
  refine ⟨296555550768417134200281929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197703700512278089466854619 296555550768417134200281929)
  ·
    refine ⟨222416663076312850650211447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296555550768417134200281929 222416663076312850650211447)
    ·
      refine ⟨333624994614469275975317171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222416663076312850650211447 333624994614469275975317171)
      ·
        refine ⟨500437491921703913962975757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 333624994614469275975317171 500437491921703913962975757)
        ·
          refine ⟨187664059470638967736115909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 500437491921703913962975757 187664059470638967736115909)
          ·
            refine ⟨35187011150744806450521733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 187664059470638967736115909 35187011150744806450521733)
            ·
              refine ⟨6597564590764651209472825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35187011150744806450521733 6597564590764651209472825)
              ·
                refine ⟨4948173443073488407104619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6597564590764651209472825 4948173443073488407104619)
                ·
                  refine ⟨7422260164610232610656929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4948173443073488407104619 7422260164610232610656929)
                  ·
                    refine ⟨5566695123457674457992697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7422260164610232610656929 5566695123457674457992697)
                    ·
                      refine ⟨4175021342593255843494523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5566695123457674457992697 4175021342593255843494523)
                      ·
                        rfl

theorem cell23_8130825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 4, 2, 1, 2, 2].length) (baseStart_8130825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8130825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8130825 prefixEnd_8130825 := by exact prefixLift 8130825
  have htrace : WordTrace (prefixWord ++ tailWord_8130825) baseStart_8130825 baseEnd_8130825 := by
    simpa [prefixWord, tailWord_8130825, baseEnd_8130825] using wordTrace_append hprefix tailTrace_8130825
  have hstable : (prefixWord ++ tailWord_8130825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8130825).length < 2 ^ (prefixWord ++ tailWord_8130825).sum := by decide
  have hdescent : baseEnd_8130825 < baseStart_8130825 := by decide
  rcases family_descends (prefixWord ++ tailWord_8130825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8130851 : List Nat := [1, 1, 1, 4, 2, 2, 2, 4, 1, 3, 2]
def baseStart_8130851 : Nat := 118140960795 + 8130851 * 2 ^ 59
def prefixEnd_8130851 : Nat := 4983230072969 + 3 ^ 40 * 8130851 * 2
def baseEnd_8130851 : Nat := 4175034693090272741769403

theorem tailTrace_8130851 : CollatzResearch.WordTrace tailWord_8130851 prefixEnd_8130851 4175034693090272741769403 := by
  unfold tailWord_8130851
  simp only [CollatzResearch.WordTrace]
  refine ⟨296556499066322940640728407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197704332710881960427152271 296556499066322940640728407)
  ·
    refine ⟨444834748599484410961092611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296556499066322940640728407 444834748599484410961092611)
    ·
      refine ⟨667252122899226616441638917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 444834748599484410961092611 667252122899226616441638917)
      ·
        refine ⟨125109773043604990582807297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 667252122899226616441638917 125109773043604990582807297)
        ·
          refine ⟨93832329782703742937105473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125109773043604990582807297 93832329782703742937105473)
          ·
            refine ⟨70374247337027807202829105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93832329782703742937105473 70374247337027807202829105)
            ·
              refine ⟨52780685502770855402121829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70374247337027807202829105 52780685502770855402121829)
              ·
                refine ⟨9896378531769535387897843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52780685502770855402121829 9896378531769535387897843)
                ·
                  refine ⟨14844567797654303081846765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9896378531769535387897843 14844567797654303081846765)
                  ·
                    refine ⟨5566712924120363655692537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14844567797654303081846765 5566712924120363655692537)
                    ·
                      refine ⟨4175034693090272741769403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5566712924120363655692537 4175034693090272741769403)
                      ·
                        rfl

theorem cell23_8130851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 4, 1, 3, 2].length) (baseStart_8130851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8130851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8130851 prefixEnd_8130851 := by exact prefixLift 8130851
  have htrace : WordTrace (prefixWord ++ tailWord_8130851) baseStart_8130851 baseEnd_8130851 := by
    simpa [prefixWord, tailWord_8130851, baseEnd_8130851] using wordTrace_append hprefix tailTrace_8130851
  have hstable : (prefixWord ++ tailWord_8130851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8130851).length < 2 ^ (prefixWord ++ tailWord_8130851).sum := by decide
  have hdescent : baseEnd_8130851 < baseStart_8130851 := by decide
  rcases family_descends (prefixWord ++ tailWord_8130851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8130862 : List Nat := [4, 1, 3, 3, 1, 2, 2, 1, 1, 2, 3]
def baseStart_8130862 : Nat := 118140960795 + 8130862 * 2 ^ 59
def prefixEnd_8130862 : Nat := 4983230072969 + 3 ^ 40 * 8130862 * 2
def baseEnd_8130862 : Nat := 4175040341377472198731853

theorem tailTrace_8130862 : CollatzResearch.WordTrace tailWord_8130862 prefixEnd_8130862 4175040341377472198731853 := by
  unfold tailWord_8130862
  simp only [CollatzResearch.WordTrace]
  refine ⟨37069612533660386189922355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 197704600179522059679585893 37069612533660386189922355)
  ·
    refine ⟨55604418800490579284883533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37069612533660386189922355 55604418800490579284883533)
    ·
      refine ⟨20851657050183967231831325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55604418800490579284883533 20851657050183967231831325)
      ·
        refine ⟨7819371393818987711936747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20851657050183967231831325 7819371393818987711936747)
        ·
          refine ⟨11729057090728481567905121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7819371393818987711936747 11729057090728481567905121)
          ·
            refine ⟨8796792818046361175928841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11729057090728481567905121 8796792818046361175928841)
            ·
              refine ⟨6597594613534770881946631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8796792818046361175928841 6597594613534770881946631)
              ·
                refine ⟨9896391920302156322919947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6597594613534770881946631 9896391920302156322919947)
                ·
                  refine ⟨14844587880453234484379921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9896391920302156322919947 14844587880453234484379921)
                  ·
                    refine ⟨11133440910339925863284941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14844587880453234484379921 11133440910339925863284941)
                    ·
                      refine ⟨4175040341377472198731853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11133440910339925863284941 4175040341377472198731853)
                      ·
                        rfl

theorem cell23_8130862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 2, 1, 1, 2, 3].length) (baseStart_8130862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8130862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8130862 prefixEnd_8130862 := by exact prefixLift 8130862
  have htrace : WordTrace (prefixWord ++ tailWord_8130862) baseStart_8130862 baseEnd_8130862 := by
    simpa [prefixWord, tailWord_8130862, baseEnd_8130862] using wordTrace_append hprefix tailTrace_8130862
  have hstable : (prefixWord ++ tailWord_8130862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8130862).length < 2 ^ (prefixWord ++ tailWord_8130862).sum := by decide
  have hdescent : baseEnd_8130862 < baseStart_8130862 := by decide
  rcases family_descends (prefixWord ++ tailWord_8130862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8130864 : List Nat := [2, 1, 1, 1, 2, 2, 2, 3, 3, 4, 2]
def baseStart_8130864 : Nat := 118140960795 + 8130864 * 2 ^ 59
def prefixEnd_8130864 : Nat := 4983230072969 + 3 ^ 40 * 8130864 * 2
def baseEnd_8130864 : Nat := 4175041368338781190906843

theorem tailTrace_8130864 : CollatzResearch.WordTrace tailWord_8130864 prefixEnd_8130864 4175041368338781190906843 := by
  unfold tailWord_8130864
  simp only [CollatzResearch.WordTrace]
  refine ⟨148278486607637921930475823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197704648810183895907301097 148278486607637921930475823)
  ·
    refine ⟨222417729911456882895713735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148278486607637921930475823 222417729911456882895713735)
    ·
      refine ⟨333626594867185324343570603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222417729911456882895713735 333626594867185324343570603)
      ·
        refine ⟨500439892300777986515355905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 333626594867185324343570603 500439892300777986515355905)
        ·
          refine ⟨375329919225583489886516929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 500439892300777986515355905 375329919225583489886516929)
          ·
            refine ⟨281497439419187617414887697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 375329919225583489886516929 281497439419187617414887697)
            ·
              refine ⟨211123079564390713061165773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 281497439419187617414887697 211123079564390713061165773)
              ·
                refine ⟨79171154836646517397937165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 211123079564390713061165773 79171154836646517397937165)
                ·
                  refine ⟨29689183063742444024226437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79171154836646517397937165 29689183063742444024226437)
                  ·
                    refine ⟨5566721824451708254542457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29689183063742444024226437 5566721824451708254542457)
                    ·
                      refine ⟨4175041368338781190906843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5566721824451708254542457 4175041368338781190906843)
                      ·
                        rfl

theorem cell23_8130864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 3, 3, 4, 2].length) (baseStart_8130864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8130864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8130864 prefixEnd_8130864 := by exact prefixLift 8130864
  have htrace : WordTrace (prefixWord ++ tailWord_8130864) baseStart_8130864 baseEnd_8130864 := by
    simpa [prefixWord, tailWord_8130864, baseEnd_8130864] using wordTrace_append hprefix tailTrace_8130864
  have hstable : (prefixWord ++ tailWord_8130864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8130864).length < 2 ^ (prefixWord ++ tailWord_8130864).sum := by decide
  have hdescent : baseEnd_8130864 < baseStart_8130864 := by decide
  rcases family_descends (prefixWord ++ tailWord_8130864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8130867 : List Nat := [1, 1, 1, 2, 5, 1, 2, 1, 1, 3, 5]
def baseStart_8130867 : Nat := 118140960795 + 8130867 * 2 ^ 59
def prefixEnd_8130867 : Nat := 4983230072969 + 3 ^ 40 * 8130867 * 2
def baseEnd_8130867 : Nat := 4175042908780744679169329

theorem tailTrace_8130867 : CollatzResearch.WordTrace tailWord_8130867 prefixEnd_8130867 4175042908780744679169329 := by
  unfold tailWord_8130867
  simp only [CollatzResearch.WordTrace]
  refine ⟨296557082634264975373310855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197704721756176650248873903 296557082634264975373310855)
  ·
    refine ⟨444835623951397463059966283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296557082634264975373310855 444835623951397463059966283)
    ·
      refine ⟨667253435927096194589949425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 444835623951397463059966283 667253435927096194589949425)
      ·
        refine ⟨500440076945322145942462069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 667253435927096194589949425 500440076945322145942462069)
        ·
          refine ⟨46916257213623951182105819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 500440076945322145942462069 46916257213623951182105819)
          ·
            refine ⟨70374385820435926773158729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46916257213623951182105819 70374385820435926773158729)
            ·
              refine ⟨52780789365326945079869047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70374385820435926773158729 52780789365326945079869047)
              ·
                refine ⟨79171184047990417619803571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52780789365326945079869047 79171184047990417619803571)
                ·
                  refine ⟨118756776071985626429705357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79171184047990417619803571 118756776071985626429705357)
                  ·
                    refine ⟨44533791026994609911139509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 118756776071985626429705357 44533791026994609911139509)
                    ·
                      refine ⟨4175042908780744679169329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44533791026994609911139509 4175042908780744679169329)
                      ·
                        rfl

theorem cell23_8130867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 1, 1, 3, 5].length) (baseStart_8130867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8130867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8130867 prefixEnd_8130867 := by exact prefixLift 8130867
  have htrace : WordTrace (prefixWord ++ tailWord_8130867) baseStart_8130867 baseEnd_8130867 := by
    simpa [prefixWord, tailWord_8130867, baseEnd_8130867] using wordTrace_append hprefix tailTrace_8130867
  have hstable : (prefixWord ++ tailWord_8130867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8130867).length < 2 ^ (prefixWord ++ tailWord_8130867).sum := by decide
  have hdescent : baseEnd_8130867 < baseStart_8130867 := by decide
  rcases family_descends (prefixWord ++ tailWord_8130867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8130898 : List Nat := [3, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2]
def baseStart_8130898 : Nat := 118140960795 + 8130898 * 2 ^ 59
def prefixEnd_8130898 : Nat := 4983230072969 + 3 ^ 40 * 8130898 * 2
def baseEnd_8130898 : Nat := 4175058826681034057881687

theorem tailTrace_8130898 : CollatzResearch.WordTrace tailWord_8130898 prefixEnd_8130898 4175058826681034057881687 := by
  unfold tailWord_8130898
  simp only [CollatzResearch.WordTrace]
  refine ⟨74139553324288166916922337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197705475531435111778459565 74139553324288166916922337)
  ·
    refine ⟨55604664993216125187691753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74139553324288166916922337 55604664993216125187691753)
    ·
      refine ⟨41703498744912093890768815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55604664993216125187691753 41703498744912093890768815)
      ·
        refine ⟨62555248117368140836153223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41703498744912093890768815 62555248117368140836153223)
        ·
          refine ⟨93832872176052211254229835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62555248117368140836153223 93832872176052211254229835)
          ·
            refine ⟨140749308264078316881344753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93832872176052211254229835 140749308264078316881344753)
            ·
              refine ⟨105561981198058737661008565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140749308264078316881344753 105561981198058737661008565)
              ·
                refine ⟨9896435737318006655719553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 105561981198058737661008565 9896435737318006655719553)
                ·
                  refine ⟨7422326802988504991789665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9896435737318006655719553 7422326802988504991789665)
                  ·
                    refine ⟨5566745102241378743842249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7422326802988504991789665 5566745102241378743842249)
                    ·
                      refine ⟨4175058826681034057881687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5566745102241378743842249 4175058826681034057881687)
                      ·
                        rfl

theorem cell23_8130898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2].length) (baseStart_8130898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8130898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8130898 prefixEnd_8130898 := by exact prefixLift 8130898
  have htrace : WordTrace (prefixWord ++ tailWord_8130898) baseStart_8130898 baseEnd_8130898 := by
    simpa [prefixWord, tailWord_8130898, baseEnd_8130898] using wordTrace_append hprefix tailTrace_8130898
  have hstable : (prefixWord ++ tailWord_8130898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8130898).length < 2 ^ (prefixWord ++ tailWord_8130898).sum := by decide
  have hdescent : baseEnd_8130898 < baseStart_8130898 := by decide
  rcases family_descends (prefixWord ++ tailWord_8130898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8130910 : List Nat := [4, 4, 2, 1, 2, 1, 1, 3, 1, 2, 2]
def baseStart_8130910 : Nat := 118140960795 + 8130910 * 2 ^ 59
def prefixEnd_8130910 : Nat := 4983230072969 + 3 ^ 40 * 8130910 * 2
def baseEnd_8130910 : Nat := 4175064988448888010931633

theorem tailTrace_8130910 : CollatzResearch.WordTrace tailWord_8130910 prefixEnd_8130910 4175064988448888010931633 := by
  unfold tailWord_8130910
  simp only [CollatzResearch.WordTrace]
  refine ⟨37069831371638649214640773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 197705767315406129144750789 37069831371638649214640773)
  ·
    refine ⟨6950593382182246727745145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37069831371638649214640773 6950593382182246727745145)
    ·
      refine ⟨5212945036636685045808859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6950593382182246727745145 5212945036636685045808859)
      ·
        refine ⟨7819417554955027568713289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5212945036636685045808859 7819417554955027568713289)
        ·
          refine ⟨5864563166216270676534967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7819417554955027568713289 5864563166216270676534967)
          ·
            refine ⟨8796844749324406014802451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5864563166216270676534967 8796844749324406014802451)
            ·
              refine ⟨13195267123986609022203677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8796844749324406014802451 13195267123986609022203677)
              ·
                refine ⟨4948225171494978383326379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13195267123986609022203677 4948225171494978383326379)
                ·
                  refine ⟨7422337757242467574989569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4948225171494978383326379 7422337757242467574989569)
                  ·
                    refine ⟨5566753317931850681242177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7422337757242467574989569 5566753317931850681242177)
                    ·
                      refine ⟨4175064988448888010931633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5566753317931850681242177 4175064988448888010931633)
                      ·
                        rfl

theorem cell23_8130910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 1, 3, 1, 2, 2].length) (baseStart_8130910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8130910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8130910 prefixEnd_8130910 := by exact prefixLift 8130910
  have htrace : WordTrace (prefixWord ++ tailWord_8130910) baseStart_8130910 baseEnd_8130910 := by
    simpa [prefixWord, tailWord_8130910, baseEnd_8130910] using wordTrace_append hprefix tailTrace_8130910
  have hstable : (prefixWord ++ tailWord_8130910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8130910).length < 2 ^ (prefixWord ++ tailWord_8130910).sum := by decide
  have hdescent : baseEnd_8130910 < baseStart_8130910 := by decide
  rcases family_descends (prefixWord ++ tailWord_8130910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8130987 : List Nat := [1, 1, 1, 1, 2, 1, 1, 2, 1, 3, 9]
def baseStart_8130987 : Nat := 118140960795 + 8130987 * 2 ^ 59
def prefixEnd_8130987 : Nat := 4983230072969 + 3 ^ 40 * 8130987 * 2
def baseEnd_8130987 : Nat := 4175104526459284209668777

theorem tailTrace_8130987 : CollatzResearch.WordTrace tailWord_8130987 prefixEnd_8130987 4175104526459284209668777 := by
  unfold tailWord_8130987
  simp only [CollatzResearch.WordTrace]
  refine ⟨296561459393830235867679215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197707639595886823911786143 296561459393830235867679215)
  ·
    refine ⟨444842189090745353801518823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296561459393830235867679215 444842189090745353801518823)
    ·
      refine ⟨667263283636118030702278235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 444842189090745353801518823 667263283636118030702278235)
      ·
        refine ⟨1000894925454177046053417353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 667263283636118030702278235 1000894925454177046053417353)
        ·
          refine ⟨750671194090632784540063015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1000894925454177046053417353 750671194090632784540063015)
          ·
            refine ⟨1126006791135949176810094523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 750671194090632784540063015 1126006791135949176810094523)
            ·
              refine ⟨1689010186703923765215141785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1126006791135949176810094523 1689010186703923765215141785)
              ·
                refine ⟨1266757640027942823911356339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1689010186703923765215141785 1266757640027942823911356339)
                ·
                  refine ⟨1900136460041914235867034509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1266757640027942823911356339 1900136460041914235867034509)
                  ·
                    refine ⟨712551172515717838450137941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1900136460041914235867034509 712551172515717838450137941)
                    ·
                      refine ⟨4175104526459284209668777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 712551172515717838450137941 4175104526459284209668777)
                      ·
                        rfl

theorem cell23_8130987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 3, 9].length) (baseStart_8130987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8130987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8130987 prefixEnd_8130987 := by exact prefixLift 8130987
  have htrace : WordTrace (prefixWord ++ tailWord_8130987) baseStart_8130987 baseEnd_8130987 := by
    simpa [prefixWord, tailWord_8130987, baseEnd_8130987] using wordTrace_append hprefix tailTrace_8130987
  have hstable : (prefixWord ++ tailWord_8130987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8130987).length < 2 ^ (prefixWord ++ tailWord_8130987).sum := by decide
  have hdescent : baseEnd_8130987 < baseStart_8130987 := by decide
  rcases family_descends (prefixWord ++ tailWord_8130987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8131041 : List Nat := [1, 2, 3, 1, 2, 2, 3, 3, 1, 5]
def baseStart_8131041 : Nat := 118140960795 + 8131041 * 2 ^ 59
def prefixEnd_8131041 : Nat := 4983230072969 + 3 ^ 40 * 8131041 * 2
def baseEnd_8131041 : Nat := 1391710751471542332797843

theorem tailTrace_8131041 : CollatzResearch.WordTrace tailWord_8131041 prefixEnd_8131041 1391710751471542332797843 := by
  unfold tailWord_8131041
  simp only [CollatzResearch.WordTrace]
  refine ⟨296563428935634603090144977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197708952623756402060096651 296563428935634603090144977)
  ·
    refine ⟨222422571701725952317608733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296563428935634603090144977 222422571701725952317608733)
    ·
      refine ⟨83408464388147232119103275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 222422571701725952317608733 83408464388147232119103275)
      ·
        refine ⟨125112696582220848178654913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83408464388147232119103275 125112696582220848178654913)
        ·
          refine ⟨93834522436665636133991185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125112696582220848178654913 93834522436665636133991185)
          ·
            refine ⟨70375891827499227100493389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93834522436665636133991185 70375891827499227100493389)
            ·
              refine ⟨26390959435312210162685021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70375891827499227100493389 26390959435312210162685021)
              ·
                refine ⟨9896609788242078811006883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26390959435312210162685021 9896609788242078811006883)
                ·
                  refine ⟨14844914682363118216510325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9896609788242078811006883 14844914682363118216510325)
                  ·
                    refine ⟨1391710751471542332797843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14844914682363118216510325 1391710751471542332797843)
                    ·
                      rfl

theorem cell23_8131041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 3, 1, 5].length) (baseStart_8131041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8131041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8131041 prefixEnd_8131041 := by exact prefixLift 8131041
  have htrace : WordTrace (prefixWord ++ tailWord_8131041) baseStart_8131041 baseEnd_8131041 := by
    simpa [prefixWord, tailWord_8131041, baseEnd_8131041] using wordTrace_append hprefix tailTrace_8131041
  have hstable : (prefixWord ++ tailWord_8131041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8131041).length < 2 ^ (prefixWord ++ tailWord_8131041).sum := by decide
  have hdescent : baseEnd_8131041 < baseStart_8131041 := by decide
  rcases family_descends (prefixWord ++ tailWord_8131041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8131045 : List Nat := [1, 3, 1, 5, 3, 1, 1, 2, 6]
def baseStart_8131045 : Nat := 118140960795 + 8131045 * 2 ^ 59
def prefixEnd_8131045 : Nat := 4983230072969 + 3 ^ 40 * 8131045 * 2
def baseEnd_8131045 : Nat := 463903812037471664749279

theorem tailTrace_8131045 : CollatzResearch.WordTrace tailWord_8131045 prefixEnd_8131045 463903812037471664749279 := by
  unfold tailWord_8131045
  simp only [CollatzResearch.WordTrace]
  refine ⟨296563574827620111773290589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197709049885080074515527059 296563574827620111773290589)
  ·
    refine ⟨111211340560357541914983971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 296563574827620111773290589 111211340560357541914983971)
    ·
      refine ⟨166817010840536312872475957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111211340560357541914983971 166817010840536312872475957)
      ·
        refine ⟨15639094766300279331794621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 166817010840536312872475957 15639094766300279331794621)
        ·
          refine ⟨5864660537362604749422983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15639094766300279331794621 5864660537362604749422983)
          ·
            refine ⟨8796990806043907124134475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5864660537362604749422983 8796990806043907124134475)
            ·
              refine ⟨13195486209065860686201713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8796990806043907124134475 13195486209065860686201713)
              ·
                refine ⟨9896614656799395514651285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13195486209065860686201713 9896614656799395514651285)
                ·
                  refine ⟨463903812037471664749279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9896614656799395514651285 463903812037471664749279)
                  ·
                    rfl

theorem cell23_8131045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 1, 2, 6].length) (baseStart_8131045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8131045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8131045 prefixEnd_8131045 := by exact prefixLift 8131045
  have htrace : WordTrace (prefixWord ++ tailWord_8131045) baseStart_8131045 baseEnd_8131045 := by
    simpa [prefixWord, tailWord_8131045, baseEnd_8131045] using wordTrace_append hprefix tailTrace_8131045
  have hstable : (prefixWord ++ tailWord_8131045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8131045).length < 2 ^ (prefixWord ++ tailWord_8131045).sum := by decide
  have hdescent : baseEnd_8131045 < baseStart_8131045 := by decide
  rcases family_descends (prefixWord ++ tailWord_8131045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8131098 : List Nat := [3, 1, 1, 3, 1, 1, 4, 3, 1, 2, 3]
def baseStart_8131098 : Nat := 118140960795 + 8131098 * 2 ^ 59
def prefixEnd_8131098 : Nat := 4983230072969 + 3 ^ 40 * 8131098 * 2
def baseEnd_8131098 : Nat := 4175161522811933275380767

theorem tailTrace_8131098 : CollatzResearch.WordTrace tailWord_8131098 prefixEnd_8131098 4175161522811933275380767 := by
  unfold tailWord_8131098
  simp only [CollatzResearch.WordTrace]
  refine ⟨74141376974107025456242487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197710338597618734549979965 74141376974107025456242487)
  ·
    refine ⟨111212065461160538184363731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74141376974107025456242487 111212065461160538184363731)
    ·
      refine ⟨166818098191740807276545597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111212065461160538184363731 166818098191740807276545597)
      ·
        refine ⟨62556786821902802728704599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166818098191740807276545597 62556786821902802728704599)
        ·
          refine ⟨93835180232854204093056899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62556786821902802728704599 93835180232854204093056899)
          ·
            refine ⟨140752770349281306139585349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93835180232854204093056899 140752770349281306139585349)
            ·
              refine ⟨26391144440490244901172253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 140752770349281306139585349 26391144440490244901172253)
              ·
                refine ⟨9896679165183841837939595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26391144440490244901172253 9896679165183841837939595)
                ·
                  refine ⟨14845018747775762756909393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9896679165183841837939595 14845018747775762756909393)
                  ·
                    refine ⟨11133764060831822067682045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14845018747775762756909393 11133764060831822067682045)
                    ·
                      refine ⟨4175161522811933275380767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11133764060831822067682045 4175161522811933275380767)
                      ·
                        rfl

theorem cell23_8131098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 3, 1, 2, 3].length) (baseStart_8131098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8131098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8131098 prefixEnd_8131098 := by exact prefixLift 8131098
  have htrace : WordTrace (prefixWord ++ tailWord_8131098) baseStart_8131098 baseEnd_8131098 := by
    simpa [prefixWord, tailWord_8131098, baseEnd_8131098] using wordTrace_append hprefix tailTrace_8131098
  have hstable : (prefixWord ++ tailWord_8131098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8131098).length < 2 ^ (prefixWord ++ tailWord_8131098).sum := by decide
  have hdescent : baseEnd_8131098 < baseStart_8131098 := by decide
  rcases family_descends (prefixWord ++ tailWord_8131098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8131101 : List Nat := [1, 4, 2, 2, 1, 4, 9]
def baseStart_8131101 : Nat := 118140960795 + 8131101 * 2 ^ 59
def prefixEnd_8131101 : Nat := 4983230072969 + 3 ^ 40 * 8131101 * 2
def baseEnd_8131101 : Nat := 51545223003134527946213

theorem tailTrace_8131101 : CollatzResearch.WordTrace tailWord_8131101 prefixEnd_8131101 51545223003134527946213 := by
  unfold tailWord_8131101
  simp only [CollatzResearch.WordTrace]
  refine ⟨296565617315417233337329157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197710411543611488891552771 296565617315417233337329157)
  ·
    refine ⟨55606053246640731250749217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 296565617315417233337329157 55606053246640731250749217)
    ·
      refine ⟨41704539934980548438061913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55606053246640731250749217 41704539934980548438061913)
      ·
        refine ⟨31278404951235411328546435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41704539934980548438061913 31278404951235411328546435)
        ·
          refine ⟨46917607426853116992819653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31278404951235411328546435 46917607426853116992819653)
          ·
            refine ⟨8797051392534959436153685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46917607426853116992819653 8797051392534959436153685)
            ·
              refine ⟨51545223003134527946213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8797051392534959436153685 51545223003134527946213)
              ·
                rfl

theorem cell23_8131101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 9].length) (baseStart_8131101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8131101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8131101 prefixEnd_8131101 := by exact prefixLift 8131101
  have htrace : WordTrace (prefixWord ++ tailWord_8131101) baseStart_8131101 baseEnd_8131101 := by
    simpa [prefixWord, tailWord_8131101, baseEnd_8131101] using wordTrace_append hprefix tailTrace_8131101
  have hstable : (prefixWord ++ tailWord_8131101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8131101).length < 2 ^ (prefixWord ++ tailWord_8131101).sum := by decide
  have hdescent : baseEnd_8131101 < baseStart_8131101 := by decide
  rcases family_descends (prefixWord ++ tailWord_8131101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8131112 : List Nat := [2, 1, 5, 2, 1, 1, 3, 1, 3, 2, 2]
def baseStart_8131112 : Nat := 118140960795 + 8131112 * 2 ^ 59
def prefixEnd_8131112 : Nat := 4983230072969 + 3 ^ 40 * 8131112 * 2
def baseEnd_8131112 : Nat := 4175168711541096220605703

theorem tailTrace_8131112 : CollatzResearch.WordTrace tailWord_8131112 prefixEnd_8131112 4175168711541096220605703 := by
  unfold tailWord_8131112
  simp only [CollatzResearch.WordTrace]
  refine ⟨148283009259188691107989795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197710679012251588143986393 148283009259188691107989795)
  ·
    refine ⟨222424513888783036661984693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148283009259188691107989795 222424513888783036661984693)
    ·
      refine ⟨20852298177073409687061065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 222424513888783036661984693 20852298177073409687061065)
      ·
        refine ⟨15639223632805057265295799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20852298177073409687061065 15639223632805057265295799)
        ·
          refine ⟨23458835449207585897943699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15639223632805057265295799 23458835449207585897943699)
          ·
            refine ⟨35188253173811378846915549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23458835449207585897943699 35188253173811378846915549)
            ·
              refine ⟨13195594940179267067593331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35188253173811378846915549 13195594940179267067593331)
              ·
                refine ⟨19793392410268900601389997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13195594940179267067593331 19793392410268900601389997)
                ·
                  refine ⟨7422522153850837725521249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19793392410268900601389997 7422522153850837725521249)
                  ·
                    refine ⟨5566891615388128294140937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7422522153850837725521249 5566891615388128294140937)
                    ·
                      refine ⟨4175168711541096220605703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5566891615388128294140937 4175168711541096220605703)
                      ·
                        rfl

theorem cell23_8131112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 3, 1, 3, 2, 2].length) (baseStart_8131112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8131112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8131112 prefixEnd_8131112 := by exact prefixLift 8131112
  have htrace : WordTrace (prefixWord ++ tailWord_8131112) baseStart_8131112 baseEnd_8131112 := by
    simpa [prefixWord, tailWord_8131112, baseEnd_8131112] using wordTrace_append hprefix tailTrace_8131112
  have hstable : (prefixWord ++ tailWord_8131112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8131112).length < 2 ^ (prefixWord ++ tailWord_8131112).sum := by decide
  have hdescent : baseEnd_8131112 < baseStart_8131112 := by decide
  rcases family_descends (prefixWord ++ tailWord_8131112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8131118 : List Nat := [4, 1, 3, 1, 3, 1, 2, 8]
def baseStart_8131118 : Nat := 118140960795 + 8131118 * 2 ^ 59
def prefixEnd_8131118 : Nat := 4983230072969 + 3 ^ 40 * 8131118 * 2
def baseEnd_8131118 : Nat := 154635992312037896190025

theorem tailTrace_8131118 : CollatzResearch.WordTrace tailWord_8131118 prefixEnd_8131118 154635992312037896190025 := by
  unfold tailWord_8131118
  simp only [CollatzResearch.WordTrace]
  refine ⟨37070779669544455655087251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 197710824904237096827132005 37070779669544455655087251)
  ·
    refine ⟨55606169504316683482630877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37070779669544455655087251 55606169504316683482630877)
    ·
      refine ⟨20852313564118756305986579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55606169504316683482630877 20852313564118756305986579)
      ·
        refine ⟨31278470346178134458979869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20852313564118756305986579 31278470346178134458979869)
        ·
          refine ⟨11729426379816800422117451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31278470346178134458979869 11729426379816800422117451)
          ·
            refine ⟨17594139569725200633176177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11729426379816800422117451 17594139569725200633176177)
            ·
              refine ⟨13195604677293900474882133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17594139569725200633176177 13195604677293900474882133)
              ·
                refine ⟨154635992312037896190025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13195604677293900474882133 154635992312037896190025)
                ·
                  rfl

theorem cell23_8131118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 2, 8].length) (baseStart_8131118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8131118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8131118 prefixEnd_8131118 := by exact prefixLift 8131118
  have htrace : WordTrace (prefixWord ++ tailWord_8131118) baseStart_8131118 baseEnd_8131118 := by
    simpa [prefixWord, tailWord_8131118, baseEnd_8131118] using wordTrace_append hprefix tailTrace_8131118
  have hstable : (prefixWord ++ tailWord_8131118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8131118).length < 2 ^ (prefixWord ++ tailWord_8131118).sum := by decide
  have hdescent : baseEnd_8131118 < baseStart_8131118 := by decide
  rcases family_descends (prefixWord ++ tailWord_8131118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8131171 : List Nat := [1, 1, 1, 5, 1, 2, 1, 1, 1, 6, 3]
def baseStart_8131171 : Nat := 118140960795 + 8131171 * 2 ^ 59
def prefixEnd_8131171 : Nat := 4983230072969 + 3 ^ 40 * 8131171 * 2
def baseEnd_8131171 : Nat := 4175199006899711489767931

theorem tailTrace_8131171 : CollatzResearch.WordTrace tailWord_8131171 prefixEnd_8131171 4175199006899711489767931 := by
  unfold tailWord_8131171
  simp only [CollatzResearch.WordTrace]
  refine ⟨296568170425163635292377367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197712113616775756861584911 296568170425163635292377367)
  ·
    refine ⟨444852255637745452938566051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296568170425163635292377367 444852255637745452938566051)
    ·
      refine ⟨667278383456618179407849077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 444852255637745452938566051 667278383456618179407849077)
      ·
        refine ⟨62557348449057954319485851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 667278383456618179407849077 62557348449057954319485851)
        ·
          refine ⟨93836022673586931479228777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62557348449057954319485851 93836022673586931479228777)
          ·
            refine ⟨70377017005190198609421583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93836022673586931479228777 70377017005190198609421583)
            ·
              refine ⟨105565525507785297914132375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70377017005190198609421583 105565525507785297914132375)
              ·
                refine ⟨158348288261677946871198563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105565525507785297914132375 158348288261677946871198563)
                ·
                  refine ⟨237522432392516920306797845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 158348288261677946871198563 237522432392516920306797845)
                  ·
                    refine ⟨11133864018399230639381149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 237522432392516920306797845 11133864018399230639381149)
                    ·
                      refine ⟨4175199006899711489767931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11133864018399230639381149 4175199006899711489767931)
                      ·
                        rfl

theorem cell23_8131171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 1, 1, 6, 3].length) (baseStart_8131171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8131171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8131171 prefixEnd_8131171 := by exact prefixLift 8131171
  have htrace : WordTrace (prefixWord ++ tailWord_8131171) baseStart_8131171 baseEnd_8131171 := by
    simpa [prefixWord, tailWord_8131171, baseEnd_8131171] using wordTrace_append hprefix tailTrace_8131171
  have hstable : (prefixWord ++ tailWord_8131171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8131171).length < 2 ^ (prefixWord ++ tailWord_8131171).sum := by decide
  have hdescent : baseEnd_8131171 < baseStart_8131171 := by decide
  rcases family_descends (prefixWord ++ tailWord_8131171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8131241 : List Nat := [1, 2, 1, 1, 1, 1, 2, 6, 1, 3, 4]
def baseStart_8131241 : Nat := 118140960795 + 8131241 * 2 ^ 59
def prefixEnd_8131241 : Nat := 4983230072969 + 3 ^ 40 * 8131241 * 2
def baseEnd_8131241 : Nat := 4175234950545526215892609

theorem tailTrace_8131241 : CollatzResearch.WordTrace tailWord_8131241 prefixEnd_8131241 4175234950545526215892609 := by
  unfold tailWord_8131241
  simp only [CollatzResearch.WordTrace]
  refine ⟨296570723534910037247425577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197713815689940024831617051 296570723534910037247425577)
  ·
    refine ⟨222428042651182527935569183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296570723534910037247425577 222428042651182527935569183)
    ·
      refine ⟨333642063976773791903353775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222428042651182527935569183 333642063976773791903353775)
      ·
        refine ⟨500463095965160687855030663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 333642063976773791903353775 500463095965160687855030663)
        ·
          refine ⟨750694643947741031782545995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 500463095965160687855030663 750694643947741031782545995)
          ·
            refine ⟨1126041965921611547673818993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 750694643947741031782545995 1126041965921611547673818993)
            ·
              refine ⟨844531474441208660755364245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1126041965921611547673818993 844531474441208660755364245)
              ·
                refine ⟨39587412864431655972907699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 844531474441208660755364245 39587412864431655972907699)
                ·
                  refine ⟨59381119296647483959361549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39587412864431655972907699 59381119296647483959361549)
                  ·
                    refine ⟨22267919736242806484760581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59381119296647483959361549 22267919736242806484760581)
                    ·
                      refine ⟨4175234950545526215892609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22267919736242806484760581 4175234950545526215892609)
                      ·
                        rfl

theorem cell23_8131241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 6, 1, 3, 4].length) (baseStart_8131241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8131241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8131241 prefixEnd_8131241 := by exact prefixLift 8131241
  have htrace : WordTrace (prefixWord ++ tailWord_8131241) baseStart_8131241 baseEnd_8131241 := by
    simpa [prefixWord, tailWord_8131241, baseEnd_8131241] using wordTrace_append hprefix tailTrace_8131241
  have hstable : (prefixWord ++ tailWord_8131241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8131241).length < 2 ^ (prefixWord ++ tailWord_8131241).sum := by decide
  have hdescent : baseEnd_8131241 < baseStart_8131241 := by decide
  rcases family_descends (prefixWord ++ tailWord_8131241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8131258 : List Nat := [3, 1, 1, 1, 2, 3, 2, 3, 2, 1, 4]
def baseStart_8131258 : Nat := 118140960795 + 8131258 * 2 ^ 59
def prefixEnd_8131258 : Nat := 4983230072969 + 3 ^ 40 * 8131258 * 2
def baseEnd_8131258 : Nat := 4175243679716652649380031

theorem tailTrace_8131258 : CollatzResearch.WordTrace tailWord_8131258 prefixEnd_8131258 4175243679716652649380031 := by
  unfold tailWord_8131258
  simp only [CollatzResearch.WordTrace]
  refine ⟨74142835893962112287698607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197714229050565632767196285 74142835893962112287698607)
  ·
    refine ⟨111214253840943168431547911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74142835893962112287698607 111214253840943168431547911)
    ·
      refine ⟨166821380761414752647321867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111214253840943168431547911 166821380761414752647321867)
      ·
        refine ⟨250232071142122128970982801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166821380761414752647321867 250232071142122128970982801)
        ·
          refine ⟨187674053356591596728237101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 250232071142122128970982801 187674053356591596728237101)
          ·
            refine ⟨70377770008721848773088913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 187674053356591596728237101 70377770008721848773088913)
            ·
              refine ⟨52783327506541386579816685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70377770008721848773088913 52783327506541386579816685)
              ·
                refine ⟨19793747814953019967431257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52783327506541386579816685 19793747814953019967431257)
                ·
                  refine ⟨14845310861214764975573443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19793747814953019967431257 14845310861214764975573443)
                  ·
                    refine ⟨22267966291822147463360165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14845310861214764975573443 22267966291822147463360165)
                    ·
                      refine ⟨4175243679716652649380031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22267966291822147463360165 4175243679716652649380031)
                      ·
                        rfl

theorem cell23_8131258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 3, 2, 1, 4].length) (baseStart_8131258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8131258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8131258 prefixEnd_8131258 := by exact prefixLift 8131258
  have htrace : WordTrace (prefixWord ++ tailWord_8131258) baseStart_8131258 baseEnd_8131258 := by
    simpa [prefixWord, tailWord_8131258, baseEnd_8131258] using wordTrace_append hprefix tailTrace_8131258
  have hstable : (prefixWord ++ tailWord_8131258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8131258).length < 2 ^ (prefixWord ++ tailWord_8131258).sum := by decide
  have hdescent : baseEnd_8131258 < baseStart_8131258 := by decide
  rcases family_descends (prefixWord ++ tailWord_8131258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8131271 : List Nat := [1, 1, 4, 1, 1, 1, 2, 3, 2, 1, 6]
def baseStart_8131271 : Nat := 118140960795 + 8131271 * 2 ^ 59
def prefixEnd_8131271 : Nat := 4983230072969 + 3 ^ 40 * 8131271 * 2
def baseEnd_8131271 : Nat := 4175250354965161098517471

theorem tailTrace_8131271 : CollatzResearch.WordTrace tailWord_8131271 prefixEnd_8131271 4175250354965161098517471 := by
  unfold tailWord_8131271
  simp only [CollatzResearch.WordTrace]
  refine ⟨296571817724801352371017667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197714545149867568247345111 296571817724801352371017667)
  ·
    refine ⟨444857726587202028556526501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296571817724801352371017667 444857726587202028556526501)
    ·
      refine ⟨83410823735100380354348719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 444857726587202028556526501 83410823735100380354348719)
      ·
        refine ⟨125116235602650570531523079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83410823735100380354348719 125116235602650570531523079)
        ·
          refine ⟨187674353403975855797284619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125116235602650570531523079 187674353403975855797284619)
          ·
            refine ⟨281511530105963783695926929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187674353403975855797284619 281511530105963783695926929)
            ·
              refine ⟨211133647579472837771945197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 281511530105963783695926929 211133647579472837771945197)
              ·
                refine ⟨79175117842302314164479449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 211133647579472837771945197 79175117842302314164479449)
                ·
                  refine ⟨59381338381726735623359587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79175117842302314164479449 59381338381726735623359587)
                  ·
                    refine ⟨89072007572590103435039381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59381338381726735623359587 89072007572590103435039381)
                    ·
                      refine ⟨4175250354965161098517471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 89072007572590103435039381 4175250354965161098517471)
                      ·
                        rfl

theorem cell23_8131271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 3, 2, 1, 6].length) (baseStart_8131271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8131271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8131271 prefixEnd_8131271 := by exact prefixLift 8131271
  have htrace : WordTrace (prefixWord ++ tailWord_8131271) baseStart_8131271 baseEnd_8131271 := by
    simpa [prefixWord, tailWord_8131271, baseEnd_8131271] using wordTrace_append hprefix tailTrace_8131271
  have hstable : (prefixWord ++ tailWord_8131271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8131271).length < 2 ^ (prefixWord ++ tailWord_8131271).sum := by decide
  have hdescent : baseEnd_8131271 < baseStart_8131271 := by decide
  rcases family_descends (prefixWord ++ tailWord_8131271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8131281 : List Nat := [1, 2, 2, 1, 2, 3, 1, 3, 8]
def baseStart_8131281 : Nat := 118140960795 + 8131281 * 2 ^ 59
def prefixEnd_8131281 : Nat := 4983230072969 + 3 ^ 40 * 8131281 * 2
def baseEnd_8131281 : Nat := 463917276641300673265825

theorem tailTrace_8131281 : CollatzResearch.WordTrace tailWord_8131281 prefixEnd_8131281 463917276641300673265825 := by
  unfold tailWord_8131281
  simp only [CollatzResearch.WordTrace]
  refine ⟨296572182454765124078881697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197714788303176749385921131 296572182454765124078881697)
  ·
    refine ⟨222429136841073843059161273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296572182454765124078881697 222429136841073843059161273)
    ·
      refine ⟨166821852630805382294370955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222429136841073843059161273 166821852630805382294370955)
      ·
        refine ⟨250232778946208073441556433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166821852630805382294370955 250232778946208073441556433)
        ·
          refine ⟨187674584209656055081167325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 250232778946208073441556433 187674584209656055081167325)
          ·
            refine ⟨70377969078621020655437747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 187674584209656055081167325 70377969078621020655437747)
            ·
              refine ⟨105566953617931530983156621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70377969078621020655437747 105566953617931530983156621)
              ·
                refine ⟨39587607606724324118683733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105566953617931530983156621 39587607606724324118683733)
                ·
                  refine ⟨463917276641300673265825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39587607606724324118683733 463917276641300673265825)
                  ·
                    rfl

theorem cell23_8131281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 3, 8].length) (baseStart_8131281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8131281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8131281 prefixEnd_8131281 := by exact prefixLift 8131281
  have htrace : WordTrace (prefixWord ++ tailWord_8131281) baseStart_8131281 baseEnd_8131281 := by
    simpa [prefixWord, tailWord_8131281, baseEnd_8131281] using wordTrace_append hprefix tailTrace_8131281
  have hstable : (prefixWord ++ tailWord_8131281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8131281).length < 2 ^ (prefixWord ++ tailWord_8131281).sum := by decide
  have hdescent : baseEnd_8131281 < baseStart_8131281 := by decide
  rcases family_descends (prefixWord ++ tailWord_8131281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8131321 : List Nat := [1, 2, 1, 3, 1, 1, 1, 2, 1, 3, 7]
def baseStart_8131321 : Nat := 118140960795 + 8131321 * 2 ^ 59
def prefixEnd_8131321 : Nat := 4983230072969 + 3 ^ 40 * 8131321 * 2
def baseEnd_8131321 : Nat := 4175276028997885902892241

theorem tailTrace_8131321 : CollatzResearch.WordTrace tailWord_8131321 prefixEnd_8131321 4175276028997885902892241 := by
  unfold tailWord_8131321
  simp only [CollatzResearch.WordTrace]
  refine ⟨296573641374620210910337817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197715760916413473940225211 296573641374620210910337817)
  ·
    refine ⟨222430231030965158182753363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296573641374620210910337817 222430231030965158182753363)
    ·
      refine ⟨333645346546447737274130045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222430231030965158182753363 333645346546447737274130045)
      ·
        refine ⟨125117004954917901477798767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 333645346546447737274130045 125117004954917901477798767)
        ·
          refine ⟨187675507432376852216698151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125117004954917901477798767 187675507432376852216698151)
          ·
            refine ⟨281513261148565278325047227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187675507432376852216698151 281513261148565278325047227)
            ·
              refine ⟨422269891722847917487570841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 281513261148565278325047227 422269891722847917487570841)
              ·
                refine ⟨316702418792135938115678131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 422269891722847917487570841 316702418792135938115678131)
                ·
                  refine ⟨475053628188203907173517197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 316702418792135938115678131 475053628188203907173517197)
                  ·
                    refine ⟨178145110570576465190068949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 475053628188203907173517197 178145110570576465190068949)
                    ·
                      refine ⟨4175276028997885902892241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 178145110570576465190068949 4175276028997885902892241)
                      ·
                        rfl

theorem cell23_8131321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 2, 1, 3, 7].length) (baseStart_8131321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8131321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8131321 prefixEnd_8131321 := by exact prefixLift 8131321
  have htrace : WordTrace (prefixWord ++ tailWord_8131321) baseStart_8131321 baseEnd_8131321 := by
    simpa [prefixWord, tailWord_8131321, baseEnd_8131321] using wordTrace_append hprefix tailTrace_8131321
  have hstable : (prefixWord ++ tailWord_8131321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8131321).length < 2 ^ (prefixWord ++ tailWord_8131321).sum := by decide
  have hdescent : baseEnd_8131321 < baseStart_8131321 := by decide
  rcases family_descends (prefixWord ++ tailWord_8131321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8131365 : List Nat := [1, 3, 1, 2, 3, 1, 2, 4, 1, 1, 4]
def baseStart_8131365 : Nat := 118140960795 + 8131365 * 2 ^ 59
def prefixEnd_8131365 : Nat := 4983230072969 + 3 ^ 40 * 8131365 * 2
def baseEnd_8131365 : Nat := 4175298622146683730742039

theorem tailTrace_8131365 : CollatzResearch.WordTrace tailWord_8131365 prefixEnd_8131365 4175298622146683730742039 := by
  unfold tailWord_8131365
  simp only [CollatzResearch.WordTrace]
  refine ⟨296575246186460806424939549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197716830790973870949959699 296575246186460806424939549)
  ·
    refine ⟨111215717319922802409352331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 296575246186460806424939549 111215717319922802409352331)
    ·
      refine ⟨166823575979884203614028497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111215717319922802409352331 166823575979884203614028497)
      ·
        refine ⟨125117681984913152710521373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166823575979884203614028497 125117681984913152710521373)
        ·
          refine ⟨46919130744342432266445515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125117681984913152710521373 46919130744342432266445515)
          ·
            refine ⟨70378696116513648399668273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46919130744342432266445515 70378696116513648399668273)
            ·
              refine ⟨52784022087385236299751205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70378696116513648399668273 52784022087385236299751205)
              ·
                refine ⟨9897004141384731806203351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52784022087385236299751205 9897004141384731806203351)
                ·
                  refine ⟨14845506212077097709305027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9897004141384731806203351 14845506212077097709305027)
                  ·
                    refine ⟨22268259318115646563957541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14845506212077097709305027 22268259318115646563957541)
                    ·
                      refine ⟨4175298622146683730742039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22268259318115646563957541 4175298622146683730742039)
                      ·
                        rfl

theorem cell23_8131365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 4, 1, 1, 4].length) (baseStart_8131365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8131365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8131365 prefixEnd_8131365 := by exact prefixLift 8131365
  have htrace : WordTrace (prefixWord ++ tailWord_8131365) baseStart_8131365 baseEnd_8131365 := by
    simpa [prefixWord, tailWord_8131365, baseEnd_8131365] using wordTrace_append hprefix tailTrace_8131365
  have hstable : (prefixWord ++ tailWord_8131365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8131365).length < 2 ^ (prefixWord ++ tailWord_8131365).sum := by decide
  have hdescent : baseEnd_8131365 < baseStart_8131365 := by decide
  rcases family_descends (prefixWord ++ tailWord_8131365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8131409 : List Nat := [1, 2, 2, 1, 6, 1, 3, 1, 2, 4]
def baseStart_8131409 : Nat := 118140960795 + 8131409 * 2 ^ 59
def prefixEnd_8131409 : Nat := 4983230072969 + 3 ^ 40 * 8131409 * 2
def baseEnd_8131409 : Nat := 1391773738431827186197279

theorem tailTrace_8131409 : CollatzResearch.WordTrace tailWord_8131409 prefixEnd_8131409 1391773738431827186197279 := by
  unfold tailWord_8131409
  simp only [CollatzResearch.WordTrace]
  refine ⟨296576850998301401939541281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197717900665534267959694187 296576850998301401939541281)
  ·
    refine ⟨222432638248726051454655961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296576850998301401939541281 222432638248726051454655961)
    ·
      refine ⟨166824478686544538590991971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222432638248726051454655961 166824478686544538590991971)
      ·
        refine ⟨250236718029816807886487957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166824478686544538590991971 250236718029816807886487957)
        ·
          refine ⟨11729846157647662869679123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 250236718029816807886487957 11729846157647662869679123)
          ·
            refine ⟨17594769236471494304518685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11729846157647662869679123 17594769236471494304518685)
            ·
              refine ⟨6598038463676810364194507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17594769236471494304518685 6598038463676810364194507)
              ·
                refine ⟨9897057695515215546291761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6598038463676810364194507 9897057695515215546291761)
                ·
                  refine ⟨7422793271636411659718821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9897057695515215546291761 7422793271636411659718821)
                  ·
                    refine ⟨1391773738431827186197279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7422793271636411659718821 1391773738431827186197279)
                    ·
                      rfl

theorem cell23_8131409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 3, 1, 2, 4].length) (baseStart_8131409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8131409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8131409 prefixEnd_8131409 := by exact prefixLift 8131409
  have htrace : WordTrace (prefixWord ++ tailWord_8131409) baseStart_8131409 baseEnd_8131409 := by
    simpa [prefixWord, tailWord_8131409, baseEnd_8131409] using wordTrace_append hprefix tailTrace_8131409
  have hstable : (prefixWord ++ tailWord_8131409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8131409).length < 2 ^ (prefixWord ++ tailWord_8131409).sum := by decide
  have hdescent : baseEnd_8131409 < baseStart_8131409 := by decide
  rcases family_descends (prefixWord ++ tailWord_8131409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8131432 : List Nat := [2, 1, 4, 2, 1, 2, 1, 2, 4, 1, 3]
def baseStart_8131432 : Nat := 118140960795 + 8131432 * 2 ^ 59
def prefixEnd_8131432 : Nat := 4983230072969 + 3 ^ 40 * 8131432 * 2
def baseEnd_8131432 : Nat := 4175333025350534968604231

theorem tailTrace_8131432 : CollatzResearch.WordTrace tailWord_8131432 prefixEnd_8131432 4175333025350534968604231 := by
  unfold tailWord_8131432
  simp only [CollatzResearch.WordTrace]
  refine ⟨148288844938609038433814275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197718459918145384578419033 148288844938609038433814275)
  ·
    refine ⟨222433267407913557650721413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148288844938609038433814275 222433267407913557650721413)
    ·
      refine ⟨41706237638983792059510265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 222433267407913557650721413 41706237638983792059510265)
      ·
        refine ⟨31279678229237844044632699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41706237638983792059510265 31279678229237844044632699)
        ·
          refine ⟨46919517343856766066949049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31279678229237844044632699 46919517343856766066949049)
          ·
            refine ⟨35189638007892574550211787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46919517343856766066949049 35189638007892574550211787)
            ·
              refine ⟨52784457011838861825317681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35189638007892574550211787 52784457011838861825317681)
              ·
                refine ⟨39588342758879146368988261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52784457011838861825317681 39588342758879146368988261)
                ·
                  refine ⟨7422814267289839944185299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39588342758879146368988261 7422814267289839944185299)
                  ·
                    refine ⟨11134221400934759916277949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7422814267289839944185299 11134221400934759916277949)
                    ·
                      refine ⟨4175333025350534968604231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11134221400934759916277949 4175333025350534968604231)
                      ·
                        rfl

theorem cell23_8131432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 2, 4, 1, 3].length) (baseStart_8131432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8131432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8131432 prefixEnd_8131432 := by exact prefixLift 8131432
  have htrace : WordTrace (prefixWord ++ tailWord_8131432) baseStart_8131432 baseEnd_8131432 := by
    simpa [prefixWord, tailWord_8131432, baseEnd_8131432] using wordTrace_append hprefix tailTrace_8131432
  have hstable : (prefixWord ++ tailWord_8131432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8131432).length < 2 ^ (prefixWord ++ tailWord_8131432).sum := by decide
  have hdescent : baseEnd_8131432 < baseStart_8131432 := by decide
  rcases family_descends (prefixWord ++ tailWord_8131432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8131448 : List Nat := [2, 1, 2, 1, 1, 1, 1, 6, 2, 6]
def baseStart_8131448 : Nat := 118140960795 + 8131448 * 2 ^ 59
def prefixEnd_8131448 : Nat := 4983230072969 + 3 ^ 40 * 8131448 * 2
def baseEnd_8131448 : Nat := 1391780413680335635334719

theorem tailTrace_8131448 : CollatzResearch.WordTrace tailWord_8131448 prefixEnd_8131448 1391780413680335635334719 := by
  unfold tailWord_8131448
  simp only [CollatzResearch.WordTrace]
  refine ⟨148289136722580055800105499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197718848963440074400140665 148289136722580055800105499)
  ·
    refine ⟨222433705083870083700158249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148289136722580055800105499 222433705083870083700158249)
    ·
      refine ⟨166825278812902562775118687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222433705083870083700158249 166825278812902562775118687)
      ·
        refine ⟨250237918219353844162678031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166825278812902562775118687 250237918219353844162678031)
        ·
          refine ⟨375356877329030766244017047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250237918219353844162678031 375356877329030766244017047)
          ·
            refine ⟨563035315993546149366025571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 375356877329030766244017047 563035315993546149366025571)
            ·
              refine ⟨844552973990319224049038357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 563035315993546149366025571 844552973990319224049038357)
              ·
                refine ⟨39588420655796213627298673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 844552973990319224049038357 39588420655796213627298673)
                ·
                  refine ⟨29691315491847160220474005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39588420655796213627298673 29691315491847160220474005)
                  ·
                    refine ⟨1391780413680335635334719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29691315491847160220474005 1391780413680335635334719)
                    ·
                      rfl

theorem cell23_8131448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 6, 2, 6].length) (baseStart_8131448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8131448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8131448 prefixEnd_8131448 := by exact prefixLift 8131448
  have htrace : WordTrace (prefixWord ++ tailWord_8131448) baseStart_8131448 baseEnd_8131448 := by
    simpa [prefixWord, tailWord_8131448, baseEnd_8131448] using wordTrace_append hprefix tailTrace_8131448
  have hstable : (prefixWord ++ tailWord_8131448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8131448).length < 2 ^ (prefixWord ++ tailWord_8131448).sum := by decide
  have hdescent : baseEnd_8131448 < baseStart_8131448 := by decide
  rcases family_descends (prefixWord ++ tailWord_8131448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8131466 : List Nat := [3, 1, 2, 4, 1, 1, 4, 1, 2, 1, 3]
def baseStart_8131466 : Nat := 118140960795 + 8131466 * 2 ^ 59
def prefixEnd_8131466 : Nat := 4983230072969 + 3 ^ 40 * 8131466 * 2
def baseEnd_8131466 : Nat := 4175350483692787835579075

theorem tailTrace_8131466 : CollatzResearch.WordTrace tailWord_8131466 prefixEnd_8131466 4175350483692787835579075 := by
  unfold tailWord_8131466
  simp only [CollatzResearch.WordTrace]
  refine ⟨74144732489773725168591563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197719286639396600449577501 74144732489773725168591563)
  ·
    refine ⟨111217098734660587752887345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74144732489773725168591563 111217098734660587752887345)
    ·
      refine ⟨83412824050995440814665509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111217098734660587752887345 83412824050995440814665509)
      ·
        refine ⟨15639904509561645152749783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83412824050995440814665509 15639904509561645152749783)
        ·
          refine ⟨23459856764342467729124675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15639904509561645152749783 23459856764342467729124675)
          ·
            refine ⟨35189785146513701593687013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23459856764342467729124675 35189785146513701593687013)
            ·
              refine ⟨6598084714971319048816315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35189785146513701593687013 6598084714971319048816315)
              ·
                refine ⟨9897127072456978573224473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6598084714971319048816315 9897127072456978573224473)
                ·
                  refine ⟨7422845304342733929918355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9897127072456978573224473 7422845304342733929918355)
                  ·
                    refine ⟨11134267956514100894877533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7422845304342733929918355 11134267956514100894877533)
                    ·
                      refine ⟨4175350483692787835579075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11134267956514100894877533 4175350483692787835579075)
                      ·
                        rfl

theorem cell23_8131466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 4, 1, 2, 1, 3].length) (baseStart_8131466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8131466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8131466 prefixEnd_8131466 := by exact prefixLift 8131466
  have htrace : WordTrace (prefixWord ++ tailWord_8131466) baseStart_8131466 baseEnd_8131466 := by
    simpa [prefixWord, tailWord_8131466, baseEnd_8131466] using wordTrace_append hprefix tailTrace_8131466
  have hstable : (prefixWord ++ tailWord_8131466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8131466).length < 2 ^ (prefixWord ++ tailWord_8131466).sum := by decide
  have hdescent : baseEnd_8131466 < baseStart_8131466 := by decide
  rcases family_descends (prefixWord ++ tailWord_8131466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8131489 : List Nat := [1, 2, 3, 4, 1, 2, 1, 2, 1, 4, 2]
def baseStart_8131489 : Nat := 118140960795 + 8131489 * 2 ^ 59
def prefixEnd_8131489 : Nat := 4983230072969 + 3 ^ 40 * 8131489 * 2
def baseEnd_8131489 : Nat := 4175362293747841245591469

theorem tailTrace_8131489 : CollatzResearch.WordTrace tailWord_8131489 prefixEnd_8131489 4175362293747841245591469 := by
  unfold tailWord_8131489
  simp only [CollatzResearch.WordTrace]
  refine ⟨296579768838011575602453521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197719845892007717068302347 296579768838011575602453521)
  ·
    refine ⟨222434826628508681701840141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296579768838011575602453521 222434826628508681701840141)
    ·
      refine ⟨83413059985690755638190053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 222434826628508681701840141 83413059985690755638190053)
      ·
        refine ⟨15639948747317016682160635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83413059985690755638190053 15639948747317016682160635)
        ·
          refine ⟨23459923120975525023240953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15639948747317016682160635 23459923120975525023240953)
          ·
            refine ⟨17594942340731643767430715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23459923120975525023240953 17594942340731643767430715)
            ·
              refine ⟨26392413511097465651146073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17594942340731643767430715 26392413511097465651146073)
              ·
                refine ⟨19794310133323099238359555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26392413511097465651146073 19794310133323099238359555)
                ·
                  refine ⟨29691465199984648857539333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19794310133323099238359555 29691465199984648857539333)
                  ·
                    refine ⟨5567149724997121660788625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29691465199984648857539333 5567149724997121660788625)
                    ·
                      refine ⟨4175362293747841245591469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5567149724997121660788625 4175362293747841245591469)
                      ·
                        rfl

theorem cell23_8131489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 2, 1, 4, 2].length) (baseStart_8131489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8131489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8131489 prefixEnd_8131489 := by exact prefixLift 8131489
  have htrace : WordTrace (prefixWord ++ tailWord_8131489) baseStart_8131489 baseEnd_8131489 := by
    simpa [prefixWord, tailWord_8131489, baseEnd_8131489] using wordTrace_append hprefix tailTrace_8131489
  have hstable : (prefixWord ++ tailWord_8131489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8131489).length < 2 ^ (prefixWord ++ tailWord_8131489).sum := by decide
  have hdescent : baseEnd_8131489 < baseStart_8131489 := by decide
  rcases family_descends (prefixWord ++ tailWord_8131489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8131512 : List Nat := [2, 1, 2, 1, 2, 5, 1, 4, 5]
def baseStart_8131512 : Nat := 118140960795 + 8131512 * 2 ^ 59
def prefixEnd_8131512 : Nat := 4983230072969 + 3 ^ 40 * 8131512 * 2
def baseEnd_8131512 : Nat := 463930455978099406178207

theorem tailTrace_8131512 : CollatzResearch.WordTrace tailWord_8131512 prefixEnd_8131512 463930455978099406178207 := by
  unfold tailWord_8131512
  simp only [CollatzResearch.WordTrace]
  refine ⟨148290303858464125265270395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197720405144618833687027193 148290303858464125265270395)
  ·
    refine ⟨222435455787696187897905593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148290303858464125265270395 222435455787696187897905593)
    ·
      refine ⟨166826591840772140923429195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222435455787696187897905593 166826591840772140923429195)
      ·
        refine ⟨250239887761158211385143793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166826591840772140923429195 250239887761158211385143793)
        ·
          refine ⟨187679915820868658538857845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 250239887761158211385143793 187679915820868658538857845)
          ·
            refine ⟨17594992108206436738017923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 187679915820868658538857845 17594992108206436738017923)
            ·
              refine ⟨26392488162309655107026885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17594992108206436738017923 26392488162309655107026885)
              ·
                refine ⟨4948591530433060332567541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26392488162309655107026885 4948591530433060332567541)
                ·
                  refine ⟨463930455978099406178207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4948591530433060332567541 463930455978099406178207)
                  ·
                    rfl

theorem cell23_8131512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 4, 5].length) (baseStart_8131512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8131512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8131512 prefixEnd_8131512 := by exact prefixLift 8131512
  have htrace : WordTrace (prefixWord ++ tailWord_8131512) baseStart_8131512 baseEnd_8131512 := by
    simpa [prefixWord, tailWord_8131512, baseEnd_8131512] using wordTrace_append hprefix tailTrace_8131512
  have hstable : (prefixWord ++ tailWord_8131512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8131512).length < 2 ^ (prefixWord ++ tailWord_8131512).sum := by decide
  have hdescent : baseEnd_8131512 < baseStart_8131512 := by decide
  rcases family_descends (prefixWord ++ tailWord_8131512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8131532 : List Nat := [2, 2, 1, 4, 1, 1, 1, 2, 2, 5, 2]
def baseStart_8131532 : Nat := 118140960795 + 8131532 * 2 ^ 59
def prefixEnd_8131532 : Nat := 4983230072969 + 3 ^ 40 * 8131532 * 2
def baseEnd_8131532 : Nat := 4175384373415984577353771

theorem tailTrace_8131532 : CollatzResearch.WordTrace tailWord_8131532 prefixEnd_8131532 4175384373415984577353771 := by
  unfold tailWord_8131532
  simp only [CollatzResearch.WordTrace]
  refine ⟨148290668588427896973134425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197720891451237195964179233 148290668588427896973134425)
  ·
    refine ⟨111218001441320922729850819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148290668588427896973134425 111218001441320922729850819)
    ·
      refine ⟨166827002161981384094776229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111218001441320922729850819 166827002161981384094776229)
      ·
        refine ⟨31280062905371509517770543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 166827002161981384094776229 31280062905371509517770543)
        ·
          refine ⟨46920094358057264276655815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31280062905371509517770543 46920094358057264276655815)
          ·
            refine ⟨70380141537085896414983723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46920094358057264276655815 70380141537085896414983723)
            ·
              refine ⟨105570212305628844622475585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70380141537085896414983723 105570212305628844622475585)
              ·
                refine ⟨79177659229221633466856689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105570212305628844622475585 79177659229221633466856689)
                ·
                  refine ⟨59383244421916225100142517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79177659229221633466856689 59383244421916225100142517)
                  ·
                    refine ⟨5567179164554646103138361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59383244421916225100142517 5567179164554646103138361)
                    ·
                      refine ⟨4175384373415984577353771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5567179164554646103138361 4175384373415984577353771)
                      ·
                        rfl

theorem cell23_8131532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 2, 2, 5, 2].length) (baseStart_8131532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8131532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8131532 prefixEnd_8131532 := by exact prefixLift 8131532
  have htrace : WordTrace (prefixWord ++ tailWord_8131532) baseStart_8131532 baseEnd_8131532 := by
    simpa [prefixWord, tailWord_8131532, baseEnd_8131532] using wordTrace_append hprefix tailTrace_8131532
  have hstable : (prefixWord ++ tailWord_8131532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8131532).length < 2 ^ (prefixWord ++ tailWord_8131532).sum := by decide
  have hdescent : baseEnd_8131532 < baseStart_8131532 := by decide
  rcases family_descends (prefixWord ++ tailWord_8131532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8131616 : List Nat := [2, 1, 1, 7, 1, 1, 1, 2, 2, 2, 3]
def baseStart_8131616 : Nat := 118140960795 + 8131616 * 2 ^ 59
def prefixEnd_8131616 : Nat := 4983230072969 + 3 ^ 40 * 8131616 * 2
def baseEnd_8131616 : Nat := 4175427505790962248703385

theorem tailTrace_8131616 : CollatzResearch.WordTrace tailWord_8131616 prefixEnd_8131616 4175427505790962248703385 := by
  unfold tailWord_8131616
  simp only [CollatzResearch.WordTrace]
  refine ⟨148292200454275738146163351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197722933939034317528217801 148292200454275738146163351)
  ·
    refine ⟨222438300681413607219245027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148292200454275738146163351 222438300681413607219245027)
    ·
      refine ⟨333657451022120410828867541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222438300681413607219245027 333657451022120410828867541)
      ·
        refine ⟨7820096508330947128801583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 333657451022120410828867541 7820096508330947128801583)
        ·
          refine ⟨11730144762496420693202375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7820096508330947128801583 11730144762496420693202375)
          ·
            refine ⟨17595217143744631039803563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11730144762496420693202375 17595217143744631039803563)
            ·
              refine ⟨26392825715616946559705345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17595217143744631039803563 26392825715616946559705345)
              ·
                refine ⟨19794619286712709919779009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26392825715616946559705345 19794619286712709919779009)
                ·
                  refine ⟨14845964465034532439834257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19794619286712709919779009 14845964465034532439834257)
                  ·
                    refine ⟨11134473348775899329875693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14845964465034532439834257 11134473348775899329875693)
                    ·
                      refine ⟨4175427505790962248703385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11134473348775899329875693 4175427505790962248703385)
                      ·
                        rfl

theorem cell23_8131616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_8131616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8131616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8131616 prefixEnd_8131616 := by exact prefixLift 8131616
  have htrace : WordTrace (prefixWord ++ tailWord_8131616) baseStart_8131616 baseEnd_8131616 := by
    simpa [prefixWord, tailWord_8131616, baseEnd_8131616] using wordTrace_append hprefix tailTrace_8131616
  have hstable : (prefixWord ++ tailWord_8131616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8131616).length < 2 ^ (prefixWord ++ tailWord_8131616).sum := by decide
  have hdescent : baseEnd_8131616 < baseStart_8131616 := by decide
  rcases family_descends (prefixWord ++ tailWord_8131616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8131635 : List Nat := [1, 1, 1, 2, 4, 1, 1, 1, 2, 5, 4]
def baseStart_8131635 : Nat := 118140960795 + 8131635 * 2 ^ 59
def prefixEnd_8131635 : Nat := 4983230072969 + 3 ^ 40 * 8131635 * 2
def baseEnd_8131635 : Nat := 4175437261923397674365797

theorem tailTrace_8131635 : CollatzResearch.WordTrace tailWord_8131635 prefixEnd_8131635 4175437261923397674365797 := by
  unfold tailWord_8131635
  simp only [CollatzResearch.WordTrace]
  refine ⟨296585093895482642537268359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197723395930321761691512239 296585093895482642537268359)
  ·
    refine ⟨444877640843223963805902539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296585093895482642537268359 444877640843223963805902539)
    ·
      refine ⟨667316461264835945708853809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 444877640843223963805902539 667316461264835945708853809)
      ·
        refine ⟨500487345948626959281640357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 667316461264835945708853809 500487345948626959281640357)
        ·
          refine ⟨93841377365367554865307567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 500487345948626959281640357 93841377365367554865307567)
          ·
            refine ⟨140762066048051332297961351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93841377365367554865307567 140762066048051332297961351)
            ·
              refine ⟨211143099072076998446942027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140762066048051332297961351 211143099072076998446942027)
              ·
                refine ⟨316714648608115497670413041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 211143099072076998446942027 316714648608115497670413041)
                ·
                  refine ⟨237535986456086623252809781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 316714648608115497670413041 237535986456086623252809781)
                  ·
                    refine ⟨22268998730258120929950917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 237535986456086623252809781 22268998730258120929950917)
                    ·
                      refine ⟨4175437261923397674365797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22268998730258120929950917 4175437261923397674365797)
                      ·
                        rfl

theorem cell23_8131635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 1, 2, 5, 4].length) (baseStart_8131635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8131635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8131635 prefixEnd_8131635 := by exact prefixLift 8131635
  have htrace : WordTrace (prefixWord ++ tailWord_8131635) baseStart_8131635 baseEnd_8131635 := by
    simpa [prefixWord, tailWord_8131635, baseEnd_8131635] using wordTrace_append hprefix tailTrace_8131635
  have hstable : (prefixWord ++ tailWord_8131635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8131635).length < 2 ^ (prefixWord ++ tailWord_8131635).sum := by decide
  have hdescent : baseEnd_8131635 < baseStart_8131635 := by decide
  rcases family_descends (prefixWord ++ tailWord_8131635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8131636 : List Nat := [2, 5, 1, 2, 1, 1, 4, 1, 6]
def baseStart_8131636 : Nat := 118140960795 + 8131636 * 2 ^ 59
def prefixEnd_8131636 : Nat := 4983230072969 + 3 ^ 40 * 8131636 * 2
def baseEnd_8131636 : Nat := 463937530600450241161477

theorem tailTrace_8131636 : CollatzResearch.WordTrace tailWord_8131636 prefixEnd_8131636 463937530600450241161477 := by
  unfold tailWord_8131636
  simp only [CollatzResearch.WordTrace]
  refine ⟨148292565184239509854027381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197723420245652679805369841 148292565184239509854027381)
  ·
    refine ⟨13902427986022454048815067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 148292565184239509854027381 13902427986022454048815067)
    ·
      refine ⟨20853641979033681073222601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13902427986022454048815067 20853641979033681073222601)
      ·
        refine ⟨15640231484275260804916951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20853641979033681073222601 15640231484275260804916951)
        ·
          refine ⟨23460347226412891207375427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15640231484275260804916951 23460347226412891207375427)
          ·
            refine ⟨35190520839619336811063141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23460347226412891207375427 35190520839619336811063141)
            ·
              refine ⟨6598222657428625652074339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35190520839619336811063141 6598222657428625652074339)
              ·
                refine ⟨9897333986142938478111509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6598222657428625652074339 9897333986142938478111509)
                ·
                  refine ⟨463937530600450241161477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9897333986142938478111509 463937530600450241161477)
                  ·
                    rfl

theorem cell23_8131636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 4, 1, 6].length) (baseStart_8131636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8131636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8131636 prefixEnd_8131636 := by exact prefixLift 8131636
  have htrace : WordTrace (prefixWord ++ tailWord_8131636) baseStart_8131636 baseEnd_8131636 := by
    simpa [prefixWord, tailWord_8131636, baseEnd_8131636] using wordTrace_append hprefix tailTrace_8131636
  have hstable : (prefixWord ++ tailWord_8131636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8131636).length < 2 ^ (prefixWord ++ tailWord_8131636).sum := by decide
  have hdescent : baseEnd_8131636 < baseStart_8131636 := by decide
  rcases family_descends (prefixWord ++ tailWord_8131636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8131649 : List Nat := [1, 2, 5, 1, 3, 1, 1, 1, 3, 5]
def baseStart_8131649 : Nat := 118140960795 + 8131649 * 2 ^ 59
def prefixEnd_8131649 : Nat := 4983230072969 + 3 ^ 40 * 8131649 * 2
def baseEnd_8131649 : Nat := 1391814816884186873196911

theorem tailTrace_8131649 : CollatzResearch.WordTrace tailWord_8131649 prefixEnd_8131649 1391814816884186873196911 := by
  unfold tailWord_8131649
  simp only [CollatzResearch.WordTrace]
  refine ⟨296585604517431922928278001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197723736344954615285518667 296585604517431922928278001)
  ·
    refine ⟨222439203388073942196208501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296585604517431922928278001 222439203388073942196208501)
    ·
      refine ⟨20853675317631932080894547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 222439203388073942196208501 20853675317631932080894547)
      ·
        refine ⟨31280512976447898121341821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20853675317631932080894547 31280512976447898121341821)
        ·
          refine ⟨11730192366167961795503183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31280512976447898121341821 11730192366167961795503183)
          ·
            refine ⟨17595288549251942693254775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11730192366167961795503183 17595288549251942693254775)
            ·
              refine ⟨26392932823877914039882163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17595288549251942693254775 26392932823877914039882163)
              ·
                refine ⟨39589399235816871059823245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26392932823877914039882163 39589399235816871059823245)
                ·
                  refine ⟨14846024713431326647433717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39589399235816871059823245 14846024713431326647433717)
                  ·
                    refine ⟨1391814816884186873196911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14846024713431326647433717 1391814816884186873196911)
                    ·
                      rfl

theorem cell23_8131649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 1, 3, 5].length) (baseStart_8131649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8131649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8131649 prefixEnd_8131649 := by exact prefixLift 8131649
  have htrace : WordTrace (prefixWord ++ tailWord_8131649) baseStart_8131649 baseEnd_8131649 := by
    simpa [prefixWord, tailWord_8131649, baseEnd_8131649] using wordTrace_append hprefix tailTrace_8131649
  have hstable : (prefixWord ++ tailWord_8131649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8131649).length < 2 ^ (prefixWord ++ tailWord_8131649).sum := by decide
  have hdescent : baseEnd_8131649 < baseStart_8131649 := by decide
  rcases family_descends (prefixWord ++ tailWord_8131649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8131662 : List Nat := [4, 1, 1, 1, 1, 3, 3, 2, 1, 6]
def baseStart_8131662 : Nat := 118140960795 + 8131662 * 2 ^ 59
def prefixEnd_8131662 : Nat := 4983230072969 + 3 ^ 40 * 8131662 * 2
def baseEnd_8131662 : Nat := 1391817041967023022909391

theorem tailTrace_8131662 : CollatzResearch.WordTrace tailWord_8131662 prefixEnd_8131662 1391817041967023022909391 := by
  unfold tailWord_8131662
  simp only [CollatzResearch.WordTrace]
  refine ⟨37073259833298103268562655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 197724052444256550765667493 37073259833298103268562655)
  ·
    refine ⟨55609889749947154902843983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37073259833298103268562655 55609889749947154902843983)
    ·
      refine ⟨83414834624920732354265975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55609889749947154902843983 83414834624920732354265975)
      ·
        refine ⟨125122251937381098531398963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83414834624920732354265975 125122251937381098531398963)
        ·
          refine ⟨187683377906071647797098445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125122251937381098531398963 187683377906071647797098445)
          ·
            refine ⟨70381266714776867923911917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 187683377906071647797098445 70381266714776867923911917)
            ·
              refine ⟨26392975018041325471466969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70381266714776867923911917 26392975018041325471466969)
              ·
                refine ⟨19794731263530994103600227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26392975018041325471466969 19794731263530994103600227)
                ·
                  refine ⟨29692096895296491155400341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19794731263530994103600227 29692096895296491155400341)
                  ·
                    refine ⟨1391817041967023022909391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29692096895296491155400341 1391817041967023022909391)
                    ·
                      rfl

theorem cell23_8131662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 2, 1, 6].length) (baseStart_8131662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8131662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8131662 prefixEnd_8131662 := by exact prefixLift 8131662
  have htrace : WordTrace (prefixWord ++ tailWord_8131662) baseStart_8131662 baseEnd_8131662 := by
    simpa [prefixWord, tailWord_8131662, baseEnd_8131662] using wordTrace_append hprefix tailTrace_8131662
  have hstable : (prefixWord ++ tailWord_8131662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8131662).length < 2 ^ (prefixWord ++ tailWord_8131662).sum := by decide
  have hdescent : baseEnd_8131662 < baseStart_8131662 := by decide
  rcases family_descends (prefixWord ++ tailWord_8131662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8131666 : List Nat := [3, 2, 2, 1, 3, 2, 3, 1, 1, 5]
def baseStart_8131666 : Nat := 118140960795 + 8131666 * 2 ^ 59
def prefixEnd_8131666 : Nat := 4983230072969 + 3 ^ 40 * 8131666 * 2
def baseEnd_8131666 : Nat := 1391817726607895684359385

theorem tailTrace_8131666 : CollatzResearch.WordTrace tailWord_8131666 prefixEnd_8131666 1391817726607895684359385 := by
  unfold tailWord_8131666
  simp only [CollatzResearch.WordTrace]
  refine ⟨74146556139592583707911713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197724149705580223221097901 74146556139592583707911713)
  ·
    refine ⟨55609917104694437780933785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74146556139592583707911713 55609917104694437780933785)
    ·
      refine ⟨41707437828520828335700339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55609917104694437780933785 41707437828520828335700339)
      ·
        refine ⟨62561156742781242503550509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41707437828520828335700339 62561156742781242503550509)
        ·
          refine ⟨23460433778542965938831441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62561156742781242503550509 23460433778542965938831441)
          ·
            refine ⟨17595325333907224454123581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23460433778542965938831441 17595325333907224454123581)
            ·
              refine ⟨6598247000215209170296343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17595325333907224454123581 6598247000215209170296343)
              ·
                refine ⟨9897370500322813755444515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6598247000215209170296343 9897370500322813755444515)
                ·
                  refine ⟨14846055750484220633166773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9897370500322813755444515 14846055750484220633166773)
                  ·
                    refine ⟨1391817726607895684359385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14846055750484220633166773 1391817726607895684359385)
                    ·
                      rfl

theorem cell23_8131666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 3, 1, 1, 5].length) (baseStart_8131666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8131666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8131666 prefixEnd_8131666 := by exact prefixLift 8131666
  have htrace : WordTrace (prefixWord ++ tailWord_8131666) baseStart_8131666 baseEnd_8131666 := by
    simpa [prefixWord, tailWord_8131666, baseEnd_8131666] using wordTrace_append hprefix tailTrace_8131666
  have hstable : (prefixWord ++ tailWord_8131666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8131666).length < 2 ^ (prefixWord ++ tailWord_8131666).sum := by decide
  have hdescent : baseEnd_8131666 < baseStart_8131666 := by decide
  rcases family_descends (prefixWord ++ tailWord_8131666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8131679 : List Nat := [1, 1, 2, 3, 1, 1, 6, 2, 2, 4]
def baseStart_8131679 : Nat := 118140960795 + 8131679 * 2 ^ 59
def prefixEnd_8131679 : Nat := 4983230072969 + 3 ^ 40 * 8131679 * 2
def baseEnd_8131679 : Nat := 1391819951690731834071865

theorem tailTrace_8131679 : CollatzResearch.WordTrace tailWord_8131679 prefixEnd_8131679 1391819951690731834071865 := by
  unfold tailWord_8131679
  simp only [CollatzResearch.WordTrace]
  refine ⟨296586698707323238051870091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197724465804882158701246727 296586698707323238051870091)
  ·
    refine ⟨444880048060984857077805137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296586698707323238051870091 444880048060984857077805137)
    ·
      refine ⟨333660036045738642808353853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 444880048060984857077805137 333660036045738642808353853)
      ·
        refine ⟨125122513517151991053132695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 333660036045738642808353853 125122513517151991053132695)
        ·
          refine ⟨187683770275727986579699043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125122513517151991053132695 187683770275727986579699043)
          ·
            refine ⟨281525655413591979869548565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187683770275727986579699043 281525655413591979869548565)
            ·
              refine ⟨13196515097512124056385089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 281525655413591979869548565 13196515097512124056385089)
              ·
                refine ⟨9897386323134093042288817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13196515097512124056385089 9897386323134093042288817)
                ·
                  refine ⟨7423039742350569781716613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9897386323134093042288817 7423039742350569781716613)
                  ·
                    refine ⟨1391819951690731834071865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7423039742350569781716613 1391819951690731834071865)
                    ·
                      rfl

theorem cell23_8131679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 6, 2, 2, 4].length) (baseStart_8131679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8131679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8131679 prefixEnd_8131679 := by exact prefixLift 8131679
  have htrace : WordTrace (prefixWord ++ tailWord_8131679) baseStart_8131679 baseEnd_8131679 := by
    simpa [prefixWord, tailWord_8131679, baseEnd_8131679] using wordTrace_append hprefix tailTrace_8131679
  have hstable : (prefixWord ++ tailWord_8131679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8131679).length < 2 ^ (prefixWord ++ tailWord_8131679).sum := by decide
  have hdescent : baseEnd_8131679 < baseStart_8131679 := by decide
  rcases family_descends (prefixWord ++ tailWord_8131679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8131719 : List Nat := [1, 1, 4, 2, 1, 1, 1, 4, 4, 1, 3]
def baseStart_8131719 : Nat := 118140960795 + 8131719 * 2 ^ 59
def prefixEnd_8131719 : Nat := 4983230072969 + 3 ^ 40 * 8131719 * 2
def baseEnd_8131719 : Nat := 4175480394298375345715411

theorem tailTrace_8131719 : CollatzResearch.WordTrace tailWord_8131719 prefixEnd_8131719 4175480394298375345715411 := by
  unfold tailWord_8131719
  simp only [CollatzResearch.WordTrace]
  refine ⟨296588157627178324883326211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197725438418118883255550807 296588157627178324883326211)
  ·
    refine ⟨444882236440767487324989317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296588157627178324883326211 444882236440767487324989317)
    ·
      refine ⟨83415419332643903873435497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 444882236440767487324989317 83415419332643903873435497)
      ·
        refine ⟨62561564499482927905076623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83415419332643903873435497 62561564499482927905076623)
        ·
          refine ⟨93842346749224391857614935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62561564499482927905076623 93842346749224391857614935)
          ·
            refine ⟨140763520123836587786422403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93842346749224391857614935 140763520123836587786422403)
            ·
              refine ⟨211145280185754881679633605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140763520123836587786422403 211145280185754881679633605)
              ·
                refine ⟨39589740034829040314931301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 211145280185754881679633605 39589740034829040314931301)
                ·
                  refine ⟨7423076256530445059049619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39589740034829040314931301 7423076256530445059049619)
                  ·
                    refine ⟨11134614384795667588574429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7423076256530445059049619 11134614384795667588574429)
                    ·
                      refine ⟨4175480394298375345715411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11134614384795667588574429 4175480394298375345715411)
                      ·
                        rfl

theorem cell23_8131719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 4, 4, 1, 3].length) (baseStart_8131719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8131719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8131719 prefixEnd_8131719 := by exact prefixLift 8131719
  have htrace : WordTrace (prefixWord ++ tailWord_8131719) baseStart_8131719 baseEnd_8131719 := by
    simpa [prefixWord, tailWord_8131719, baseEnd_8131719] using wordTrace_append hprefix tailTrace_8131719
  have hstable : (prefixWord ++ tailWord_8131719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8131719).length < 2 ^ (prefixWord ++ tailWord_8131719).sum := by decide
  have hdescent : baseEnd_8131719 < baseStart_8131719 := by decide
  rcases family_descends (prefixWord ++ tailWord_8131719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8131720 : List Nat := [2, 1, 3, 4, 3, 1, 2, 1, 1, 1, 4]
def baseStart_8131720 : Nat := 118140960795 + 8131720 * 2 ^ 59
def prefixEnd_8131720 : Nat := 4983230072969 + 3 ^ 40 * 8131720 * 2
def baseEnd_8131720 : Nat := 4175480907779029841802907

theorem tailTrace_8131720 : CollatzResearch.WordTrace tailWord_8131720 prefixEnd_8131720 4175480907779029841802907 := by
  unfold tailWord_8131720
  simp only [CollatzResearch.WordTrace]
  refine ⟨148294097050087351027056307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197725462733449801369408409 148294097050087351027056307)
  ·
    refine ⟨222441145575131026540584461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148294097050087351027056307 222441145575131026540584461)
    ·
      refine ⟨83415429590674134952719173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 222441145575131026540584461 83415429590674134952719173)
      ·
        refine ⟨15640393048251400303634845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83415429590674134952719173 15640393048251400303634845)
        ·
          refine ⟨5865147393094275113863067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15640393048251400303634845 5865147393094275113863067)
          ·
            refine ⟨8797721089641412670794601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5865147393094275113863067 8797721089641412670794601)
            ·
              refine ⟨6598290817231059503095951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8797721089641412670794601 6598290817231059503095951)
              ·
                refine ⟨9897436225846589254643927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6598290817231059503095951 9897436225846589254643927)
                ·
                  refine ⟨14846154338769883881965891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9897436225846589254643927 14846154338769883881965891)
                  ·
                    refine ⟨22269231508154825822948837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14846154338769883881965891 22269231508154825822948837)
                    ·
                      refine ⟨4175480907779029841802907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22269231508154825822948837 4175480907779029841802907)
                      ·
                        rfl

theorem cell23_8131720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 2, 1, 1, 1, 4].length) (baseStart_8131720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8131720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8131720 prefixEnd_8131720 := by exact prefixLift 8131720
  have htrace : WordTrace (prefixWord ++ tailWord_8131720) baseStart_8131720 baseEnd_8131720 := by
    simpa [prefixWord, tailWord_8131720, baseEnd_8131720] using wordTrace_append hprefix tailTrace_8131720
  have hstable : (prefixWord ++ tailWord_8131720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8131720).length < 2 ^ (prefixWord ++ tailWord_8131720).sum := by decide
  have hdescent : baseEnd_8131720 < baseStart_8131720 := by decide
  rcases family_descends (prefixWord ++ tailWord_8131720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8131736 : List Nat := [2, 1, 2, 4, 2, 2, 1, 1, 4, 1, 3]
def baseStart_8131736 : Nat := 118140960795 + 8131736 * 2 ^ 59
def prefixEnd_8131736 : Nat := 4983230072969 + 3 ^ 40 * 8131736 * 2
def baseEnd_8131736 : Nat := 4175489123469501779202833

theorem tailTrace_8131736 : CollatzResearch.WordTrace tailWord_8131736 prefixEnd_8131736 4175489123469501779202833 := by
  unfold tailWord_8131736
  simp only [CollatzResearch.WordTrace]
  refine ⟨148294388834058368393347531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197725851778744491191130041 148294388834058368393347531)
  ·
    refine ⟨222441583251087552590021297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148294388834058368393347531 222441583251087552590021297)
    ·
      refine ⟨166831187438315664442515973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222441583251087552590021297 166831187438315664442515973)
      ·
        refine ⟨31280847644684187082971745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 166831187438315664442515973 31280847644684187082971745)
        ·
          refine ⟨23460635733513140312228809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31280847644684187082971745 23460635733513140312228809)
          ·
            refine ⟨17595476800134855234171607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23460635733513140312228809 17595476800134855234171607)
            ·
              refine ⟨26393215200202282851257411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17595476800134855234171607 26393215200202282851257411)
              ·
                refine ⟨39589822800303424276886117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26393215200202282851257411 39589822800303424276886117)
                ·
                  refine ⟨7423091775056892051916147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39589822800303424276886117 7423091775056892051916147)
                  ·
                    refine ⟨11134637662585338077874221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7423091775056892051916147 11134637662585338077874221)
                    ·
                      refine ⟨4175489123469501779202833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11134637662585338077874221 4175489123469501779202833)
                      ·
                        rfl

theorem cell23_8131736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 1, 4, 1, 3].length) (baseStart_8131736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8131736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8131736 prefixEnd_8131736 := by exact prefixLift 8131736
  have htrace : WordTrace (prefixWord ++ tailWord_8131736) baseStart_8131736 baseEnd_8131736 := by
    simpa [prefixWord, tailWord_8131736, baseEnd_8131736] using wordTrace_append hprefix tailTrace_8131736
  have hstable : (prefixWord ++ tailWord_8131736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8131736).length < 2 ^ (prefixWord ++ tailWord_8131736).sum := by decide
  have hdescent : baseEnd_8131736 < baseStart_8131736 := by decide
  rcases family_descends (prefixWord ++ tailWord_8131736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8131799 : List Nat := [1, 1, 3, 2, 1, 2, 2, 6, 5]
def baseStart_8131799 : Nat := 118140960795 + 8131799 * 2 ^ 59
def prefixEnd_8131799 : Nat := 4983230072969 + 3 ^ 40 * 8131799 * 2
def baseEnd_8131799 : Nat := 463946830305637225857227

theorem tailTrace_8131799 : CollatzResearch.WordTrace tailWord_8131799 prefixEnd_8131799 463946830305637225857227 := by
  unfold tailWord_8131799
  simp only [CollatzResearch.WordTrace]
  refine ⟨296591075466888498546238451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197727383644592332364158967 296591075466888498546238451)
  ·
    refine ⟨444886613200332747819357677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296591075466888498546238451 444886613200332747819357677)
    ·
      refine ⟨166832479950124780432259129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 444886613200332747819357677 166832479950124780432259129)
      ·
        refine ⟨125124359962593585324194347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166832479950124780432259129 125124359962593585324194347)
        ·
          refine ⟨187686539943890377986291521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125124359962593585324194347 187686539943890377986291521)
          ·
            refine ⟨140764904957917783489718641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 187686539943890377986291521 140764904957917783489718641)
            ·
              refine ⟨105573678718438337617288981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140764904957917783489718641 105573678718438337617288981)
              ·
                refine ⟨4948766189926797075810421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 105573678718438337617288981 4948766189926797075810421)
                ·
                  refine ⟨463946830305637225857227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4948766189926797075810421 463946830305637225857227)
                  ·
                    rfl

theorem cell23_8131799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 6, 5].length) (baseStart_8131799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8131799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8131799 prefixEnd_8131799 := by exact prefixLift 8131799
  have htrace : WordTrace (prefixWord ++ tailWord_8131799) baseStart_8131799 baseEnd_8131799 := by
    simpa [prefixWord, tailWord_8131799, baseEnd_8131799] using wordTrace_append hprefix tailTrace_8131799
  have hstable : (prefixWord ++ tailWord_8131799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8131799).length < 2 ^ (prefixWord ++ tailWord_8131799).sum := by decide
  have hdescent : baseEnd_8131799 < baseStart_8131799 := by decide
  rcases family_descends (prefixWord ++ tailWord_8131799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8131812 : List Nat := [2, 3, 1, 1, 1, 2, 2, 1, 3, 7]
def baseStart_8131812 : Nat := 118140960795 + 8131812 * 2 ^ 59
def prefixEnd_8131812 : Nat := 4983230072969 + 3 ^ 40 * 8131812 * 2
def baseEnd_8131812 : Nat := 1391842715999747827284161

theorem tailTrace_8131812 : CollatzResearch.WordTrace tailWord_8131812 prefixEnd_8131812 1391842715999747827284161 := by
  unfold tailWord_8131812
  simp only [CollatzResearch.WordTrace]
  refine ⟨148295774807920700883230845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197727699743894267844307793 148295774807920700883230845)
  ·
    refine ⟨55610915552970262831211567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148295774807920700883230845 55610915552970262831211567)
    ·
      refine ⟨83416373329455394246817351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55610915552970262831211567 83416373329455394246817351)
      ·
        refine ⟨125124559994183091370226027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83416373329455394246817351 125124559994183091370226027)
        ·
          refine ⟨187686839991274637055339041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125124559994183091370226027 187686839991274637055339041)
          ·
            refine ⟨140765129993455977791504281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 187686839991274637055339041 140765129993455977791504281)
            ·
              refine ⟨105573847495091983343628211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140765129993455977791504281 105573847495091983343628211)
              ·
                refine ⟨158360771242637975015442317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105573847495091983343628211 158360771242637975015442317)
                ·
                  refine ⟨59385289215989240630790869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 158360771242637975015442317 59385289215989240630790869)
                  ·
                    refine ⟨1391842715999747827284161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59385289215989240630790869 1391842715999747827284161)
                    ·
                      rfl

theorem cell23_8131812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 1, 3, 7].length) (baseStart_8131812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8131812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8131812 prefixEnd_8131812 := by exact prefixLift 8131812
  have htrace : WordTrace (prefixWord ++ tailWord_8131812) baseStart_8131812 baseEnd_8131812 := by
    simpa [prefixWord, tailWord_8131812, baseEnd_8131812] using wordTrace_append hprefix tailTrace_8131812
  have hstable : (prefixWord ++ tailWord_8131812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8131812).length < 2 ^ (prefixWord ++ tailWord_8131812).sum := by decide
  have hdescent : baseEnd_8131812 < baseStart_8131812 := by decide
  rcases family_descends (prefixWord ++ tailWord_8131812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8131849 : List Nat := [1, 2, 1, 1, 3, 3, 1, 4, 2, 1, 4]
def baseStart_8131849 : Nat := 118140960795 + 8131849 * 2 ^ 59
def prefixEnd_8131849 : Nat := 4983230072969 + 3 ^ 40 * 8131849 * 2
def baseEnd_8131849 : Nat := 4175547146783459837089813

theorem tailTrace_8131849 : CollatzResearch.WordTrace tailWord_8131849 prefixEnd_8131849 4175547146783459837089813 := by
  unfold tailWord_8131849
  simp only [CollatzResearch.WordTrace]
  refine ⟨296592899116707357085558601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197728599411138238057039067 296592899116707357085558601)
  ·
    refine ⟨222444674337530517814168951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296592899116707357085558601 222444674337530517814168951)
    ·
      refine ⟨333667011506295776721253427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222444674337530517814168951 333667011506295776721253427)
      ·
        refine ⟨500500517259443665081880141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 333667011506295776721253427 500500517259443665081880141)
        ·
          refine ⟨187687693972291374405705053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 500500517259443665081880141 187687693972291374405705053)
          ·
            refine ⟨70382885239609265402139395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 187687693972291374405705053 70382885239609265402139395)
            ·
              refine ⟨105574327859413898103209093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70382885239609265402139395 105574327859413898103209093)
              ·
                refine ⟨19795186473640105894351705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 105574327859413898103209093 19795186473640105894351705)
                ·
                  refine ⟨14846389855230079420763779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19795186473640105894351705 14846389855230079420763779)
                  ·
                    refine ⟨22269584782845119131145669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14846389855230079420763779 22269584782845119131145669)
                    ·
                      refine ⟨4175547146783459837089813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22269584782845119131145669 4175547146783459837089813)
                      ·
                        rfl

theorem cell23_8131849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 4, 2, 1, 4].length) (baseStart_8131849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8131849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8131849 prefixEnd_8131849 := by exact prefixLift 8131849
  have htrace : WordTrace (prefixWord ++ tailWord_8131849) baseStart_8131849 baseEnd_8131849 := by
    simpa [prefixWord, tailWord_8131849, baseEnd_8131849] using wordTrace_append hprefix tailTrace_8131849
  have hstable : (prefixWord ++ tailWord_8131849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8131849).length < 2 ^ (prefixWord ++ tailWord_8131849).sum := by decide
  have hdescent : baseEnd_8131849 < baseStart_8131849 := by decide
  rcases family_descends (prefixWord ++ tailWord_8131849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8131866 : List Nat := [3, 1, 1, 3, 3, 1, 1, 1, 1, 6, 2]
def baseStart_8131866 : Nat := 118140960795 + 8131866 * 2 ^ 59
def prefixEnd_8131866 : Nat := 4983230072969 + 3 ^ 40 * 8131866 * 2
def baseEnd_8131866 : Nat := 4175555875954586270577235

theorem tailTrace_8131866 : CollatzResearch.WordTrace tailWord_8131866 prefixEnd_8131866 4175555875954586270577235 := by
  unfold tailWord_8131866
  simp only [CollatzResearch.WordTrace]
  refine ⟨74148379789411442247231863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197729012771763845992618301 74148379789411442247231863)
  ·
    refine ⟨111222569684117163370847795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74148379789411442247231863 111222569684117163370847795)
    ·
      refine ⟨166833854526175745056271693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111222569684117163370847795 166833854526175745056271693)
      ·
        refine ⟨62562695447315904396101885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166833854526175745056271693 62562695447315904396101885)
        ·
          refine ⟨23461010792743464148538207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62562695447315904396101885 23461010792743464148538207)
          ·
            refine ⟨35191516189115196222807311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23461010792743464148538207 35191516189115196222807311)
            ·
              refine ⟨52787274283672794334210967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35191516189115196222807311 52787274283672794334210967)
              ·
                refine ⟨79180911425509191501316451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52787274283672794334210967 79180911425509191501316451)
                ·
                  refine ⟨118771367138263787251974677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79180911425509191501316451 118771367138263787251974677)
                  ·
                    refine ⟨5567407834606115027436313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 118771367138263787251974677 5567407834606115027436313)
                    ·
                      refine ⟨4175555875954586270577235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5567407834606115027436313 4175555875954586270577235)
                      ·
                        rfl

theorem cell23_8131866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 1, 1, 6, 2].length) (baseStart_8131866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8131866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8131866 prefixEnd_8131866 := by exact prefixLift 8131866
  have htrace : WordTrace (prefixWord ++ tailWord_8131866) baseStart_8131866 baseEnd_8131866 := by
    simpa [prefixWord, tailWord_8131866, baseEnd_8131866] using wordTrace_append hprefix tailTrace_8131866
  have hstable : (prefixWord ++ tailWord_8131866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8131866).length < 2 ^ (prefixWord ++ tailWord_8131866).sum := by decide
  have hdescent : baseEnd_8131866 < baseStart_8131866 := by decide
  rcases family_descends (prefixWord ++ tailWord_8131866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8131876 : List Nat := [2, 3, 1, 3, 1, 1, 3, 2, 3, 4]
def baseStart_8131876 : Nat := 118140960795 + 8131876 * 2 ^ 59
def prefixEnd_8131876 : Nat := 4983230072969 + 3 ^ 40 * 8131876 * 2
def baseEnd_8131876 : Nat := 1391853670253710410484063

theorem tailTrace_8131876 : CollatzResearch.WordTrace tailWord_8131876 prefixEnd_8131876 1391853670253710410484063 := by
  unfold tailWord_8131876
  simp only [CollatzResearch.WordTrace]
  refine ⟨148296941943804770348395741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197729255925073027131194321 148296941943804770348395741)
  ·
    refine ⟨55611353228926788880648403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148296941943804770348395741 55611353228926788880648403)
    ·
      refine ⟨83417029843390183320972605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55611353228926788880648403 83417029843390183320972605)
      ·
        refine ⟨31281386191271318745364727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83417029843390183320972605 31281386191271318745364727)
        ·
          refine ⟨46922079286906978118047091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31281386191271318745364727 46922079286906978118047091)
          ·
            refine ⟨70383118930360467177070637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46922079286906978118047091 70383118930360467177070637)
            ·
              refine ⟨26393669598885175191401489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70383118930360467177070637 26393669598885175191401489)
              ·
                refine ⟨19795252199163881393551117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26393669598885175191401489 19795252199163881393551117)
                ·
                  refine ⟨7423219574686455522581669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19795252199163881393551117 7423219574686455522581669)
                  ·
                    refine ⟨1391853670253710410484063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7423219574686455522581669 1391853670253710410484063)
                    ·
                      rfl

theorem cell23_8131876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 2, 3, 4].length) (baseStart_8131876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8131876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8131876 prefixEnd_8131876 := by exact prefixLift 8131876
  have htrace : WordTrace (prefixWord ++ tailWord_8131876) baseStart_8131876 baseEnd_8131876 := by
    simpa [prefixWord, tailWord_8131876, baseEnd_8131876] using wordTrace_append hprefix tailTrace_8131876
  have hstable : (prefixWord ++ tailWord_8131876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8131876).length < 2 ^ (prefixWord ++ tailWord_8131876).sum := by decide
  have hdescent : baseEnd_8131876 < baseStart_8131876 := by decide
  rcases family_descends (prefixWord ++ tailWord_8131876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8131893 : List Nat := [1, 3, 3, 1, 2, 2, 1, 5, 1, 4]
def baseStart_8131893 : Nat := 118140960795 + 8131893 * 2 ^ 59
def prefixEnd_8131893 : Nat := 4983230072969 + 3 ^ 40 * 8131893 * 2
def baseEnd_8131893 : Nat := 1391856579977419221646537

theorem tailTrace_8131893 : CollatzResearch.WordTrace tailWord_8131893 prefixEnd_8131893 1391856579977419221646537 := by
  unfold tailWord_8131893
  simp only [CollatzResearch.WordTrace]
  refine ⟨296594503928547952600160333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197729669285698635066773555 296594503928547952600160333)
  ·
    refine ⟨111222938973205482225060125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 296594503928547952600160333 111222938973205482225060125)
    ·
      refine ⟨41708602114952055834397547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111222938973205482225060125 41708602114952055834397547)
      ·
        refine ⟨62562903172428083751596321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41708602114952055834397547 62562903172428083751596321)
        ·
          refine ⟨46922177379321062813697241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62562903172428083751596321 46922177379321062813697241)
          ·
            refine ⟨35191633034490797110272931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46922177379321062813697241 35191633034490797110272931)
            ·
              refine ⟨52787449551736195665409397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35191633034490797110272931 52787449551736195665409397)
              ·
                refine ⟨4948823395475268343632131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52787449551736195665409397 4948823395475268343632131)
                ·
                  refine ⟨7423235093212902515448197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4948823395475268343632131 7423235093212902515448197)
                  ·
                    refine ⟨1391856579977419221646537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7423235093212902515448197 1391856579977419221646537)
                    ·
                      rfl

theorem cell23_8131893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 5, 1, 4].length) (baseStart_8131893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8131893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8131893 prefixEnd_8131893 := by exact prefixLift 8131893
  have htrace : WordTrace (prefixWord ++ tailWord_8131893) baseStart_8131893 baseEnd_8131893 := by
    simpa [prefixWord, tailWord_8131893, baseEnd_8131893] using wordTrace_append hprefix tailTrace_8131893
  have hstable : (prefixWord ++ tailWord_8131893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8131893).length < 2 ^ (prefixWord ++ tailWord_8131893).sum := by decide
  have hdescent : baseEnd_8131893 < baseStart_8131893 := by decide
  rcases family_descends (prefixWord ++ tailWord_8131893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8131936 : List Nat := [2, 1, 1, 3, 4, 1, 1, 4, 1, 5]
def baseStart_8131936 : Nat := 118140960795 + 8131936 * 2 ^ 59
def prefixEnd_8131936 : Nat := 4983230072969 + 3 ^ 40 * 8131936 * 2
def baseEnd_8131936 : Nat := 1391863939866800332233971

theorem tailTrace_8131936 : CollatzResearch.WordTrace tailWord_8131936 prefixEnd_8131936 1391863939866800332233971 := by
  unfold tailWord_8131936
  simp only [CollatzResearch.WordTrace]
  refine ⟨148298036133696085471987831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197730714844928113962650441 148298036133696085471987831)
  ·
    refine ⟨222447054200544128207981747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148298036133696085471987831 222447054200544128207981747)
    ·
      refine ⟨333670581300816192311972621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222447054200544128207981747 333670581300816192311972621)
      ·
        refine ⟨125126467987806072116989733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 333670581300816192311972621 125126467987806072116989733)
        ·
          refine ⟨23461212747713638521935575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 125126467987806072116989733 23461212747713638521935575)
          ·
            refine ⟨35191819121570457782903363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23461212747713638521935575 35191819121570457782903363)
            ·
              refine ⟨52787728682355686674355045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35191819121570457782903363 52787728682355686674355045)
              ·
                refine ⟨9897699127941691251441571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52787728682355686674355045 9897699127941691251441571)
                ·
                  refine ⟨14846548691912536877162357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9897699127941691251441571 14846548691912536877162357)
                  ·
                    refine ⟨1391863939866800332233971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14846548691912536877162357 1391863939866800332233971)
                    ·
                      rfl

theorem cell23_8131936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 4, 1, 5].length) (baseStart_8131936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8131936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8131936 prefixEnd_8131936 := by exact prefixLift 8131936
  have htrace : WordTrace (prefixWord ++ tailWord_8131936) baseStart_8131936 baseEnd_8131936 := by
    simpa [prefixWord, tailWord_8131936, baseEnd_8131936] using wordTrace_append hprefix tailTrace_8131936
  have hstable : (prefixWord ++ tailWord_8131936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8131936).length < 2 ^ (prefixWord ++ tailWord_8131936).sum := by decide
  have hdescent : baseEnd_8131936 < baseStart_8131936 := by decide
  rcases family_descends (prefixWord ++ tailWord_8131936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8131976 : List Nat := [2, 1, 3, 3, 1, 2, 2, 2, 1, 1, 5]
def baseStart_8131976 : Nat := 118140960795 + 8131976 * 2 ^ 59
def prefixEnd_8131976 : Nat := 4983230072969 + 3 ^ 40 * 8131976 * 2
def baseEnd_8131976 : Nat := 4175612358826580840201729

theorem tailTrace_8131976 : CollatzResearch.WordTrace tailWord_8131976 prefixEnd_8131976 4175612358826580840201729 := by
  unfold tailWord_8131976
  simp only [CollatzResearch.WordTrace]
  refine ⟨148298765593623628887715891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197731687458164838516954521 148298765593623628887715891)
  ·
    refine ⟨222448148390435443331573837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148298765593623628887715891 222448148390435443331573837)
    ·
      refine ⟨83418055646413291249340189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 222448148390435443331573837 83418055646413291249340189)
      ·
        refine ⟨31281770867404984218502571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83418055646413291249340189 31281770867404984218502571)
        ·
          refine ⟨46922656301107476327753857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31281770867404984218502571 46922656301107476327753857)
          ·
            refine ⟨35191992225830607245815393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46922656301107476327753857 35191992225830607245815393)
            ·
              refine ⟨26393994169372955434361545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35191992225830607245815393 26393994169372955434361545)
              ·
                refine ⟨19795495627029716575771159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26393994169372955434361545 19795495627029716575771159)
                ·
                  refine ⟨29693243440544574863656739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19795495627029716575771159 29693243440544574863656739)
                  ·
                    refine ⟨44539865160816862295485109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29693243440544574863656739 44539865160816862295485109)
                    ·
                      refine ⟨4175612358826580840201729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44539865160816862295485109 4175612358826580840201729)
                      ·
                        rfl

theorem cell23_8131976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 2, 1, 1, 5].length) (baseStart_8131976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8131976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8131976 prefixEnd_8131976 := by exact prefixLift 8131976
  have htrace : WordTrace (prefixWord ++ tailWord_8131976) baseStart_8131976 baseEnd_8131976 := by
    simpa [prefixWord, tailWord_8131976, baseEnd_8131976] using wordTrace_append hprefix tailTrace_8131976
  have hstable : (prefixWord ++ tailWord_8131976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8131976).length < 2 ^ (prefixWord ++ tailWord_8131976).sum := by decide
  have hdescent : baseEnd_8131976 < baseStart_8131976 := by decide
  rcases family_descends (prefixWord ++ tailWord_8131976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8131979 : List Nat := [1, 1, 1, 1, 4, 3, 4, 8]
def baseStart_8131979 : Nat := 118140960795 + 8131979 * 2 ^ 59
def prefixEnd_8131979 : Nat := 4983230072969 + 3 ^ 40 * 8131979 * 2
def baseEnd_8131979 : Nat := 154652366639575715869045

theorem tailTrace_8131979 : CollatzResearch.WordTrace tailWord_8131979 prefixEnd_8131979 154652366639575715869045 := by
  unfold tailWord_8131979
  simp only [CollatzResearch.WordTrace]
  refine ⟨296597640606236389287790991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197731760404157592858527327 296597640606236389287790991)
  ·
    refine ⟨444896460909354583931686487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296597640606236389287790991 444896460909354583931686487)
    ·
      refine ⟨667344691364031875897529731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 444896460909354583931686487 667344691364031875897529731)
      ·
        refine ⟨1001017037046047813846294597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 667344691364031875897529731 1001017037046047813846294597)
        ·
          refine ⟨187690694446133965096180237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1001017037046047813846294597 187690694446133965096180237)
          ·
            refine ⟨70384010417300236911067589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 187690694446133965096180237 70384010417300236911067589)
            ·
              refine ⟨13197001953243794420825173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70384010417300236911067589 13197001953243794420825173)
              ·
                refine ⟨154652366639575715869045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13197001953243794420825173 154652366639575715869045)
                ·
                  rfl

theorem cell23_8131979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 4, 8].length) (baseStart_8131979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8131979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8131979 prefixEnd_8131979 := by exact prefixLift 8131979
  have htrace : WordTrace (prefixWord ++ tailWord_8131979) baseStart_8131979 baseEnd_8131979 := by
    simpa [prefixWord, tailWord_8131979, baseEnd_8131979] using wordTrace_append hprefix tailTrace_8131979
  have hstable : (prefixWord ++ tailWord_8131979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8131979).length < 2 ^ (prefixWord ++ tailWord_8131979).sum := by decide
  have hdescent : baseEnd_8131979 < baseStart_8131979 := by decide
  rcases family_descends (prefixWord ++ tailWord_8131979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8131993 : List Nat := [1, 2, 1, 2, 1, 5, 3, 2, 1, 2, 3]
def baseStart_8131993 : Nat := 118140960795 + 8131993 * 2 ^ 59
def prefixEnd_8131993 : Nat := 4983230072969 + 3 ^ 40 * 8131993 * 2
def baseEnd_8131993 : Nat := 4175621087997707273689151

theorem tailTrace_8131993 : CollatzResearch.WordTrace tailWord_8131993 prefixEnd_8131993 4175621087997707273689151 := by
  unfold tailWord_8131993
  simp only [CollatzResearch.WordTrace]
  refine ⟨296598151228185669678800633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197732100818790446452533755 296598151228185669678800633)
  ·
    refine ⟨222448613421139252259100475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296598151228185669678800633 222448613421139252259100475)
    ·
      refine ⟨333672920131708878388650713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222448613421139252259100475 333672920131708878388650713)
      ·
        refine ⟨250254690098781658791488035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 333672920131708878388650713 250254690098781658791488035)
        ·
          refine ⟨375382035148172488187232053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250254690098781658791488035 375382035148172488187232053)
          ·
            refine ⟨35192065795141170767553005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 375382035148172488187232053 35192065795141170767553005)
            ·
              refine ⟨13197024673177939037832377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35192065795141170767553005 13197024673177939037832377)
              ·
                refine ⟨9897768504883454278374283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13197024673177939037832377 9897768504883454278374283)
                ·
                  refine ⟨14846652757325181417561425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9897768504883454278374283 14846652757325181417561425)
                  ·
                    refine ⟨11134989567993886063171069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14846652757325181417561425 11134989567993886063171069)
                    ·
                      refine ⟨4175621087997707273689151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11134989567993886063171069 4175621087997707273689151)
                      ·
                        rfl

theorem cell23_8131993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 3, 2, 1, 2, 3].length) (baseStart_8131993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8131993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8131993 prefixEnd_8131993 := by exact prefixLift 8131993
  have htrace : WordTrace (prefixWord ++ tailWord_8131993) baseStart_8131993 baseEnd_8131993 := by
    simpa [prefixWord, tailWord_8131993, baseEnd_8131993] using wordTrace_append hprefix tailTrace_8131993
  have hstable : (prefixWord ++ tailWord_8131993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8131993).length < 2 ^ (prefixWord ++ tailWord_8131993).sum := by decide
  have hdescent : baseEnd_8131993 < baseStart_8131993 := by decide
  rcases family_descends (prefixWord ++ tailWord_8131993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8132007 : List Nat := [1, 1, 6, 1, 1, 1, 2, 5, 1, 2, 2]
def baseStart_8132007 : Nat := 118140960795 + 8132007 * 2 ^ 59
def prefixEnd_8132007 : Nat := 4983230072969 + 3 ^ 40 * 8132007 * 2
def baseEnd_8132007 : Nat := 4175628276726870218914087

theorem tailTrace_8132007 : CollatzResearch.WordTrace tailWord_8132007 prefixEnd_8132007 4175628276726870218914087 := by
  unfold tailWord_8132007
  simp only [CollatzResearch.WordTrace]
  refine ⟨296598661850134950069810275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197732441233423300046540183 296598661850134950069810275)
  ·
    refine ⟨444897992775202425104715413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296598661850134950069810275 444897992775202425104715413)
    ·
      refine ⟨20854593411337613676783535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 444897992775202425104715413 20854593411337613676783535)
      ·
        refine ⟨31281890117006420515175303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20854593411337613676783535 31281890117006420515175303)
        ·
          refine ⟨46922835175509630772762955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31281890117006420515175303 46922835175509630772762955)
          ·
            refine ⟨70384252763264446159144433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46922835175509630772762955 70384252763264446159144433)
            ·
              refine ⟨52788189572448334619358325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70384252763264446159144433 52788189572448334619358325)
              ·
                refine ⟨4948892772417031370564843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52788189572448334619358325 4948892772417031370564843)
                ·
                  refine ⟨7423339158625547055847265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4948892772417031370564843 7423339158625547055847265)
                  ·
                    refine ⟨5567504368969160291885449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7423339158625547055847265 5567504368969160291885449)
                    ·
                      refine ⟨4175628276726870218914087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5567504368969160291885449 4175628276726870218914087)
                      ·
                        rfl

theorem cell23_8132007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 5, 1, 2, 2].length) (baseStart_8132007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8132007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8132007 prefixEnd_8132007 := by exact prefixLift 8132007
  have htrace : WordTrace (prefixWord ++ tailWord_8132007) baseStart_8132007 baseEnd_8132007 := by
    simpa [prefixWord, tailWord_8132007, baseEnd_8132007] using wordTrace_append hprefix tailTrace_8132007
  have hstable : (prefixWord ++ tailWord_8132007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8132007).length < 2 ^ (prefixWord ++ tailWord_8132007).sum := by decide
  have hdescent : baseEnd_8132007 < baseStart_8132007 := by decide
  rcases family_descends (prefixWord ++ tailWord_8132007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8132019 : List Nat := [1, 1, 1, 2, 3, 1, 1, 4, 2, 2, 5]
def baseStart_8132019 : Nat := 118140960795 + 8132019 * 2 ^ 59
def prefixEnd_8132019 : Nat := 4983230072969 + 3 ^ 40 * 8132019 * 2
def baseEnd_8132019 : Nat := 4175634438494724171964031

theorem tailTrace_8132019 : CollatzResearch.WordTrace tailWord_8132019 prefixEnd_8132019 4175634438494724171964031 := by
  unfold tailWord_8132019
  simp only [CollatzResearch.WordTrace]
  refine ⟨296599099526091476119247111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197732733017394317412831407 296599099526091476119247111)
  ·
    refine ⟨444898649289137214178870667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296599099526091476119247111 444898649289137214178870667)
    ·
      refine ⟨667347973933705821268306001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 444898649289137214178870667 667347973933705821268306001)
      ·
        refine ⟨500510980450279365951229501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 667347973933705821268306001 500510980450279365951229501)
        ·
          refine ⟨187691617668854762231711063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 500510980450279365951229501 187691617668854762231711063)
          ·
            refine ⟨281537426503282143347566595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187691617668854762231711063 281537426503282143347566595)
            ·
              refine ⟨422306139754923215021349893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 281537426503282143347566595 422306139754923215021349893)
              ·
                refine ⟨79182401204048102816503105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 422306139754923215021349893 79182401204048102816503105)
                ·
                  refine ⟨59386800903036077112377329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79182401204048102816503105 59386800903036077112377329)
                  ·
                    refine ⟨44540100677277057834282997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59386800903036077112377329 44540100677277057834282997)
                    ·
                      refine ⟨4175634438494724171964031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44540100677277057834282997 4175634438494724171964031)
                      ·
                        rfl

theorem cell23_8132019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 4, 2, 2, 5].length) (baseStart_8132019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8132019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8132019 prefixEnd_8132019 := by exact prefixLift 8132019
  have htrace : WordTrace (prefixWord ++ tailWord_8132019) baseStart_8132019 baseEnd_8132019 := by
    simpa [prefixWord, tailWord_8132019, baseEnd_8132019] using wordTrace_append hprefix tailTrace_8132019
  have hstable : (prefixWord ++ tailWord_8132019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8132019).length < 2 ^ (prefixWord ++ tailWord_8132019).sum := by decide
  have hdescent : baseEnd_8132019 < baseStart_8132019 := by decide
  rcases family_descends (prefixWord ++ tailWord_8132019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8132034 : List Nat := [3, 5, 2, 1, 1, 1, 2, 1, 1, 6]
def baseStart_8132034 : Nat := 118140960795 + 8132034 * 2 ^ 59
def prefixEnd_8132034 : Nat := 4983230072969 + 3 ^ 40 * 8132034 * 2
def baseEnd_8132034 : Nat := 1391880713568180537758821

theorem tailTrace_8132034 : CollatzResearch.WordTrace tailWord_8132034 prefixEnd_8132034 1391880713568180537758821 := by
  unfold tailWord_8132034
  simp only [CollatzResearch.WordTrace]
  refine ⟨74149911655259283420260789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197733097747358089120695437 74149911655259283420260789)
  ·
    refine ⟨6951554217680557820649449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 74149911655259283420260789 6951554217680557820649449)
    ·
      refine ⟨5213665663260418365487087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6951554217680557820649449 5213665663260418365487087)
      ·
        refine ⟨7820498494890627548230631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5213665663260418365487087 7820498494890627548230631)
        ·
          refine ⟨11730747742335941322345947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7820498494890627548230631 11730747742335941322345947)
          ·
            refine ⟨17596121613503911983518921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11730747742335941322345947 17596121613503911983518921)
            ·
              refine ⟨13197091210127933987639191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17596121613503911983518921 13197091210127933987639191)
              ·
                refine ⟨19795636815191900981458787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13197091210127933987639191 19795636815191900981458787)
                ·
                  refine ⟨29693455222787851472188181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19795636815191900981458787 29693455222787851472188181)
                  ·
                    refine ⟨1391880713568180537758821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29693455222787851472188181 1391880713568180537758821)
                    ·
                      rfl

theorem cell23_8132034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_8132034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8132034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8132034 prefixEnd_8132034 := by exact prefixLift 8132034
  have htrace : WordTrace (prefixWord ++ tailWord_8132034) baseStart_8132034 baseEnd_8132034 := by
    simpa [prefixWord, tailWord_8132034, baseEnd_8132034] using wordTrace_append hprefix tailTrace_8132034
  have hstable : (prefixWord ++ tailWord_8132034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8132034).length < 2 ^ (prefixWord ++ tailWord_8132034).sum := by decide
  have hdescent : baseEnd_8132034 < baseStart_8132034 := by decide
  rcases family_descends (prefixWord ++ tailWord_8132034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8132063 : List Nat := [1, 1, 2, 3, 3, 1, 1, 4, 1, 4, 2]
def baseStart_8132063 : Nat := 118140960795 + 8132063 * 2 ^ 59
def prefixEnd_8132063 : Nat := 4983230072969 + 3 ^ 40 * 8132063 * 2
def baseEnd_8132063 : Nat := 4175657031643521999813829

theorem tailTrace_8132063 : CollatzResearch.WordTrace tailWord_8132063 prefixEnd_8132063 4175657031643521999813829 := by
  unfold tailWord_8132063
  simp only [CollatzResearch.WordTrace]
  refine ⟨296600704337932071633848843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197733802891954714422565895 296600704337932071633848843)
  ·
    refine ⟨444901056506898107450773265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296600704337932071633848843 444901056506898107450773265)
    ·
      refine ⟨333675792380173580588079949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 444901056506898107450773265 333675792380173580588079949)
      ·
        refine ⟨125128422142565092720529981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 333675792380173580588079949 125128422142565092720529981)
        ·
          refine ⟨46923158303461909770198743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125128422142565092720529981 46923158303461909770198743)
          ·
            refine ⟨70384737455192864655298115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46923158303461909770198743 70384737455192864655298115)
            ·
              refine ⟨105577106182789296982947173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70384737455192864655298115 105577106182789296982947173)
              ·
                refine ⟨19795707409272993184302595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 105577106182789296982947173 19795707409272993184302595)
                ·
                  refine ⟨29693561113909489776453893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19795707409272993184302595 29693561113909489776453893)
                  ·
                    refine ⟨5567542708858029333085105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29693561113909489776453893 5567542708858029333085105)
                    ·
                      refine ⟨4175657031643521999813829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5567542708858029333085105 4175657031643521999813829)
                      ·
                        rfl

theorem cell23_8132063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 4, 1, 4, 2].length) (baseStart_8132063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8132063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8132063 prefixEnd_8132063 := by exact prefixLift 8132063
  have htrace : WordTrace (prefixWord ++ tailWord_8132063) baseStart_8132063 baseEnd_8132063 := by
    simpa [prefixWord, tailWord_8132063, baseEnd_8132063] using wordTrace_append hprefix tailTrace_8132063
  have hstable : (prefixWord ++ tailWord_8132063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8132063).length < 2 ^ (prefixWord ++ tailWord_8132063).sum := by decide
  have hdescent : baseEnd_8132063 < baseStart_8132063 := by decide
  rcases family_descends (prefixWord ++ tailWord_8132063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8132067 : List Nat := [1, 1, 1, 6, 2, 1, 4, 1, 1, 3, 2]
def baseStart_8132067 : Nat := 118140960795 + 8132067 * 2 ^ 59
def prefixEnd_8132067 : Nat := 4983230072969 + 3 ^ 40 * 8132067 * 2
def baseEnd_8132067 : Nat := 4175659085566139984163811

theorem tailTrace_8132067 : CollatzResearch.WordTrace tailWord_8132067 prefixEnd_8132067 4175659085566139984163811 := by
  unfold tailWord_8132067
  simp only [CollatzResearch.WordTrace]
  refine ⟨296600850229917580316994455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197733900153278386877996303 296600850229917580316994455)
  ·
    refine ⟨444901275344876370475491683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296600850229917580316994455 444901275344876370475491683)
    ·
      refine ⟨667351913017314555713237525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 444901275344876370475491683 667351913017314555713237525)
      ·
        refine ⟨31282120922686619799058009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 667351913017314555713237525 31282120922686619799058009)
        ·
          refine ⟨23461590692014964849293507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31282120922686619799058009 23461590692014964849293507)
          ·
            refine ⟨35192386038022447273940261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23461590692014964849293507 35192386038022447273940261)
            ·
              refine ⟨6598572382129208863863799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35192386038022447273940261 6598572382129208863863799)
              ·
                refine ⟨9897858573193813295795699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6598572382129208863863799 9897858573193813295795699)
                ·
                  refine ⟨14846787859790719943693549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9897858573193813295795699 14846787859790719943693549)
                  ·
                    refine ⟨5567545447421519978885081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14846787859790719943693549 5567545447421519978885081)
                    ·
                      refine ⟨4175659085566139984163811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5567545447421519978885081 4175659085566139984163811)
                      ·
                        rfl

theorem cell23_8132067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 4, 1, 1, 3, 2].length) (baseStart_8132067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8132067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8132067 prefixEnd_8132067 := by exact prefixLift 8132067
  have htrace : WordTrace (prefixWord ++ tailWord_8132067) baseStart_8132067 baseEnd_8132067 := by
    simpa [prefixWord, tailWord_8132067, baseEnd_8132067] using wordTrace_append hprefix tailTrace_8132067
  have hstable : (prefixWord ++ tailWord_8132067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8132067).length < 2 ^ (prefixWord ++ tailWord_8132067).sum := by decide
  have hdescent : baseEnd_8132067 < baseStart_8132067 := by decide
  rcases family_descends (prefixWord ++ tailWord_8132067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8132074 : List Nat := [3, 1, 3, 1, 5, 1, 1, 2, 2, 1, 3]
def baseStart_8132074 : Nat := 118140960795 + 8132074 * 2 ^ 59
def prefixEnd_8132074 : Nat := 4983230072969 + 3 ^ 40 * 8132074 * 2
def baseEnd_8132074 : Nat := 4175662679930721456776279

theorem tailTrace_8132074 : CollatzResearch.WordTrace tailWord_8132074 prefixEnd_8132074 4175662679930721456776279 := by
  unfold tailWord_8132074
  simp only [CollatzResearch.WordTrace]
  refine ⟨74150276385223055128124819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197734070360594813674999517 74150276385223055128124819)
  ·
    refine ⟨111225414577834582692187229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74150276385223055128124819 111225414577834582692187229)
    ·
      refine ⟨41709530466687968509570211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111225414577834582692187229 41709530466687968509570211)
      ·
        refine ⟨62564295700031952764355317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41709530466687968509570211 62564295700031952764355317)
        ·
          refine ⟨5865402721877995571658311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 62564295700031952764355317 5865402721877995571658311)
          ·
            refine ⟨8798104082816993357487467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5865402721877995571658311 8798104082816993357487467)
            ·
              refine ⟨13197156124225490036231201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8798104082816993357487467 13197156124225490036231201)
              ·
                refine ⟨9897867093169117527173401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13197156124225490036231201 9897867093169117527173401)
                ·
                  refine ⟨7423400319876838145380051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9897867093169117527173401 7423400319876838145380051)
                  ·
                    refine ⟨11135100479815257218070077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7423400319876838145380051 11135100479815257218070077)
                    ·
                      refine ⟨4175662679930721456776279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11135100479815257218070077 4175662679930721456776279)
                      ·
                        rfl

theorem cell23_8132074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 1, 2, 2, 1, 3].length) (baseStart_8132074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8132074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8132074 prefixEnd_8132074 := by exact prefixLift 8132074
  have htrace : WordTrace (prefixWord ++ tailWord_8132074) baseStart_8132074 baseEnd_8132074 := by
    simpa [prefixWord, tailWord_8132074, baseEnd_8132074] using wordTrace_append hprefix tailTrace_8132074
  have hstable : (prefixWord ++ tailWord_8132074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8132074).length < 2 ^ (prefixWord ++ tailWord_8132074).sum := by decide
  have hdescent : baseEnd_8132074 < baseStart_8132074 := by decide
  rcases family_descends (prefixWord ++ tailWord_8132074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
