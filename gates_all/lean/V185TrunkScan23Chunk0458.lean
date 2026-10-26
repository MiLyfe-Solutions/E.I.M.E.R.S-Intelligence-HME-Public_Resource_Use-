import V185TrunkScan23Chunk0457

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2709746 : List Nat := [3, 2, 1, 3, 2, 2, 1, 2, 2, 5]
def baseStart_2709746 : Nat := 118140960795 + 2709746 * 2 ^ 59
def prefixEnd_2709746 : Nat := 4983230072969 + 3 ^ 40 * 2709746 * 2
def baseEnd_2709746 : Nat := 463800716532753446671037

theorem tailTrace_2709746 : CollatzResearch.WordTrace tailWord_2709746 prefixEnd_2709746 463800716532753446671037 := by
  unfold tailWord_2709746
  simp only [CollatzResearch.WordTrace]
  refine ⟨24708139010265126154373273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65888370694040336411662061 24708139010265126154373273)
  ·
    refine ⟨18531104257698844615779955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24708139010265126154373273 18531104257698844615779955)
    ·
      refine ⟨27796656386548266923669933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18531104257698844615779955 27796656386548266923669933)
      ·
        refine ⟨10423746144955600096376225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27796656386548266923669933 10423746144955600096376225)
        ·
          refine ⟨7817809608716700072282169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10423746144955600096376225 7817809608716700072282169)
          ·
            refine ⟨5863357206537525054211627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7817809608716700072282169 5863357206537525054211627)
            ·
              refine ⟨8795035809806287581317441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5863357206537525054211627 8795035809806287581317441)
              ·
                refine ⟨6596276857354715685988081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8795035809806287581317441 6596276857354715685988081)
                ·
                  refine ⟨4947207643016036764491061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6596276857354715685988081 4947207643016036764491061)
                  ·
                    refine ⟨463800716532753446671037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4947207643016036764491061 463800716532753446671037)
                    ·
                      rfl

theorem cell23_2709746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 2, 2, 5].length) (baseStart_2709746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2709746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2709746 prefixEnd_2709746 := by exact prefixLift 2709746
  have htrace : WordTrace (prefixWord ++ tailWord_2709746) baseStart_2709746 baseEnd_2709746 := by
    simpa [prefixWord, tailWord_2709746, baseEnd_2709746] using wordTrace_append hprefix tailTrace_2709746
  have hstable : (prefixWord ++ tailWord_2709746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2709746).length < 2 ^ (prefixWord ++ tailWord_2709746).sum := by decide
  have hdescent : baseEnd_2709746 < baseStart_2709746 := by decide
  rcases family_descends (prefixWord ++ tailWord_2709746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2709810 : List Nat := [3, 2, 1, 1, 5, 1, 1, 4, 1, 4]
def baseStart_2709810 : Nat := 118140960795 + 2709810 * 2 ^ 59
def prefixEnd_2709810 : Nat := 4983230072969 + 3 ^ 40 * 2709810 * 2
def baseEnd_2709810 : Nat := 463811670786716029870939

theorem tailTrace_2709810 : CollatzResearch.WordTrace tailWord_2709810 prefixEnd_2709810 463811670786716029870939 := by
  unfold tailWord_2709810
  simp only [CollatzResearch.WordTrace]
  refine ⟨24708722578207160886955721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65889926875219095698548589 24708722578207160886955721)
  ·
    refine ⟨18531541933655370665216791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24708722578207160886955721 18531541933655370665216791)
    ·
      refine ⟨27797312900483055997825187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18531541933655370665216791 27797312900483055997825187)
      ·
        refine ⟨41695969350724583996737781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27797312900483055997825187 41695969350724583996737781)
        ·
          refine ⟨3908997126630429749694167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 41695969350724583996737781 3908997126630429749694167)
          ·
            refine ⟨5863495689945644624541251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3908997126630429749694167 5863495689945644624541251)
            ·
              refine ⟨8795243534918466936811877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5863495689945644624541251 8795243534918466936811877)
              ·
                refine ⟨1649108162797212550652227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8795243534918466936811877 1649108162797212550652227)
                ·
                  refine ⟨2473662244195818825978341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1649108162797212550652227 2473662244195818825978341)
                  ·
                    refine ⟨463811670786716029870939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2473662244195818825978341 463811670786716029870939)
                    ·
                      rfl

theorem cell23_2709810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 4, 1, 4].length) (baseStart_2709810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2709810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2709810 prefixEnd_2709810 := by exact prefixLift 2709810
  have htrace : WordTrace (prefixWord ++ tailWord_2709810) baseStart_2709810 baseEnd_2709810 := by
    simpa [prefixWord, tailWord_2709810, baseEnd_2709810] using wordTrace_append hprefix tailTrace_2709810
  have hstable : (prefixWord ++ tailWord_2709810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2709810).length < 2 ^ (prefixWord ++ tailWord_2709810).sum := by decide
  have hdescent : baseEnd_2709810 < baseStart_2709810 := by decide
  rcases family_descends (prefixWord ++ tailWord_2709810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2709836 : List Nat := [2, 2, 1, 3, 2, 1, 2, 4, 1, 5]
def baseStart_2709836 : Nat := 118140960795 + 2709836 * 2 ^ 59
def prefixEnd_2709836 : Nat := 4983230072969 + 3 ^ 40 * 2709836 * 2
def baseEnd_2709836 : Nat := 463816120952388329295899

theorem tailTrace_2709836 : CollatzResearch.WordTrace tailWord_2709836 prefixEnd_2709836 463816120952388329295899 := by
  unfold tailWord_2709836
  simp only [CollatzResearch.WordTrace]
  refine ⟨49417919305367224994134681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65890559073822966658846241 49417919305367224994134681)
  ·
    refine ⟨37063439479025418745601011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49417919305367224994134681 37063439479025418745601011)
    ·
      refine ⟨55595159218538128118401517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37063439479025418745601011 55595159218538128118401517)
      ·
        refine ⟨20848184706951798044400569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55595159218538128118401517 20848184706951798044400569)
        ·
          refine ⟨15636138530213848533300427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20848184706951798044400569 15636138530213848533300427)
          ·
            refine ⟨23454207795320772799950641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15636138530213848533300427 23454207795320772799950641)
            ·
              refine ⟨17590655846490579599962981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23454207795320772799950641 17590655846490579599962981)
              ·
                refine ⟨3298247971216983674993059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17590655846490579599962981 3298247971216983674993059)
                ·
                  refine ⟨4947371956825475512489589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3298247971216983674993059 4947371956825475512489589)
                  ·
                    refine ⟨463816120952388329295899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4947371956825475512489589 463816120952388329295899)
                    ·
                      rfl

theorem cell23_2709836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 4, 1, 5].length) (baseStart_2709836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2709836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2709836 prefixEnd_2709836 := by exact prefixLift 2709836
  have htrace : WordTrace (prefixWord ++ tailWord_2709836) baseStart_2709836 baseEnd_2709836 := by
    simpa [prefixWord, tailWord_2709836, baseEnd_2709836] using wordTrace_append hprefix tailTrace_2709836
  have hstable : (prefixWord ++ tailWord_2709836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2709836).length < 2 ^ (prefixWord ++ tailWord_2709836).sum := by decide
  have hdescent : baseEnd_2709836 < baseStart_2709836 := by decide
  rcases family_descends (prefixWord ++ tailWord_2709836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2709909 : List Nat := [1, 3, 2, 1, 1, 2, 1, 2, 1, 9]
def baseStart_2709909 : Nat := 118140960795 + 2709909 * 2 ^ 59
def prefixEnd_2709909 : Nat := 4983230072969 + 3 ^ 40 * 2709909 * 2
def baseEnd_2709909 : Nat := 463828615648314400758287

theorem tailTrace_2709909 : CollatzResearch.WordTrace tailWord_2709909 prefixEnd_2709909 463828615648314400758287 := by
  unfold tailWord_2709909
  simp only [CollatzResearch.WordTrace]
  refine ⟨98838501139469983455676781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65892334092979988970451187 98838501139469983455676781)
  ·
    refine ⟨37064437927301243795878793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98838501139469983455676781 37064437927301243795878793)
    ·
      refine ⟨27798328445475932846909095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37064437927301243795878793 27798328445475932846909095)
      ·
        refine ⟨41697492668213899270363643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27798328445475932846909095 41697492668213899270363643)
        ·
          refine ⟨62546239002320848905545465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41697492668213899270363643 62546239002320848905545465)
          ·
            refine ⟨46909679251740636679159099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62546239002320848905545465 46909679251740636679159099)
            ·
              refine ⟨70364518877610955018738649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46909679251740636679159099 70364518877610955018738649)
              ·
                refine ⟨52773389158208216264053987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70364518877610955018738649 52773389158208216264053987)
                ·
                  refine ⟨79160083737312324396080981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52773389158208216264053987 79160083737312324396080981)
                  ·
                    refine ⟨463828615648314400758287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 79160083737312324396080981 463828615648314400758287)
                    ·
                      rfl

theorem cell23_2709909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 2, 1, 9].length) (baseStart_2709909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2709909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2709909 prefixEnd_2709909 := by exact prefixLift 2709909
  have htrace : WordTrace (prefixWord ++ tailWord_2709909) baseStart_2709909 baseEnd_2709909 := by
    simpa [prefixWord, tailWord_2709909, baseEnd_2709909] using wordTrace_append hprefix tailTrace_2709909
  have hstable : (prefixWord ++ tailWord_2709909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2709909).length < 2 ^ (prefixWord ++ tailWord_2709909).sum := by decide
  have hdescent : baseEnd_2709909 < baseStart_2709909 := by decide
  rcases family_descends (prefixWord ++ tailWord_2709909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2709923 : List Nat := [1, 1, 1, 4, 1, 4, 2, 1, 4, 1, 3]
def baseStart_2709923 : Nat := 118140960795 + 2709923 * 2 ^ 59
def prefixEnd_2709923 : Nat := 4983230072969 + 3 ^ 40 * 2709923 * 2
def baseEnd_2709923 : Nat := 1391493035674106147499797

theorem tailTrace_2709923 : CollatzResearch.WordTrace tailWord_2709923 prefixEnd_2709923 1391493035674106147499797 := by
  unfold tailWord_2709923
  simp only [CollatzResearch.WordTrace]
  refine ⟨98839011761419263846686423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65892674507612842564457615 98839011761419263846686423)
  ·
    refine ⟨148258517642128895770029635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98839011761419263846686423 148258517642128895770029635)
    ·
      refine ⟨222387776463193343655044453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148258517642128895770029635 222387776463193343655044453)
      ·
        refine ⟨41697708086848751935320835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 222387776463193343655044453 41697708086848751935320835)
        ·
          refine ⟨62546562130273127902981253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41697708086848751935320835 62546562130273127902981253)
          ·
            refine ⟨11727480399426211481808985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62546562130273127902981253 11727480399426211481808985)
            ·
              refine ⟨8795610299569658611356739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11727480399426211481808985 8795610299569658611356739)
              ·
                refine ⟨13193415449354487917035109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8795610299569658611356739 13193415449354487917035109)
                ·
                  refine ⟨2473765396753966484444083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13193415449354487917035109 2473765396753966484444083)
                  ·
                    refine ⟨3710648095130949726666125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2473765396753966484444083 3710648095130949726666125)
                    ·
                      refine ⟨1391493035674106147499797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3710648095130949726666125 1391493035674106147499797)
                      ·
                        rfl

theorem cell23_2709923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 1, 4, 1, 3].length) (baseStart_2709923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2709923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2709923 prefixEnd_2709923 := by exact prefixLift 2709923
  have htrace : WordTrace (prefixWord ++ tailWord_2709923) baseStart_2709923 baseEnd_2709923 := by
    simpa [prefixWord, tailWord_2709923, baseEnd_2709923] using wordTrace_append hprefix tailTrace_2709923
  have hstable : (prefixWord ++ tailWord_2709923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2709923).length < 2 ^ (prefixWord ++ tailWord_2709923).sum := by decide
  have hdescent : baseEnd_2709923 < baseStart_2709923 := by decide
  rcases family_descends (prefixWord ++ tailWord_2709923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2709976 : List Nat := [2, 1, 2, 2, 2, 1, 1, 4, 2, 2, 4]
def baseStart_2709976 : Nat := 118140960795 + 2709976 * 2 ^ 59
def prefixEnd_2709976 : Nat := 4983230072969 + 3 ^ 40 * 2709976 * 2
def baseEnd_2709976 : Nat := 1391520250148794440137053

theorem tailTrace_2709976 : CollatzResearch.WordTrace tailWord_2709976 prefixEnd_2709976 1391520250148794440137053 := by
  unfold tailWord_2709976
  simp only [CollatzResearch.WordTrace]
  refine ⟨49420472415113626949182891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65893963220151502598910521 49420472415113626949182891)
  ·
    refine ⟨74130708622670440423774337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49420472415113626949182891 74130708622670440423774337)
    ·
      refine ⟨55598031467002830317830753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74130708622670440423774337 55598031467002830317830753)
      ·
        refine ⟨41698523600252122738373065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55598031467002830317830753 41698523600252122738373065)
        ·
          refine ⟨31273892700189092053779799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41698523600252122738373065 31273892700189092053779799)
          ·
            refine ⟨46910839050283638080669699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31273892700189092053779799 46910839050283638080669699)
            ·
              refine ⟨70366258575425457121004549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46910839050283638080669699 70366258575425457121004549)
              ·
                refine ⟨13193673482892273210188353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 70366258575425457121004549 13193673482892273210188353)
                ·
                  refine ⟨9895255112169204907641265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13193673482892273210188353 9895255112169204907641265)
                  ·
                    refine ⟨7421441334126903680730949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9895255112169204907641265 7421441334126903680730949)
                    ·
                      refine ⟨1391520250148794440137053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7421441334126903680730949 1391520250148794440137053)
                      ·
                        rfl

theorem cell23_2709976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 4, 2, 2, 4].length) (baseStart_2709976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2709976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2709976 prefixEnd_2709976 := by exact prefixLift 2709976
  have htrace : WordTrace (prefixWord ++ tailWord_2709976) baseStart_2709976 baseEnd_2709976 := by
    simpa [prefixWord, tailWord_2709976, baseEnd_2709976] using wordTrace_append hprefix tailTrace_2709976
  have hstable : (prefixWord ++ tailWord_2709976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2709976).length < 2 ^ (prefixWord ++ tailWord_2709976).sum := by decide
  have hdescent : baseEnd_2709976 < baseStart_2709976 := by decide
  rcases family_descends (prefixWord ++ tailWord_2709976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2709997 : List Nat := [1, 5, 1, 3, 1, 2, 2, 1, 1, 4, 2]
def baseStart_2709997 : Nat := 118140960795 + 2709997 * 2 ^ 59
def prefixEnd_2709997 : Nat := 4983230072969 + 3 ^ 40 * 2709997 * 2
def baseEnd_2709997 : Nat := 1391531033242538857974457

theorem tailTrace_2709997 : CollatzResearch.WordTrace tailWord_2709997 prefixEnd_2709997 1391531033242538857974457 := by
  unfold tailWord_2709997
  simp only [CollatzResearch.WordTrace]
  refine ⟨98841710763151174484880245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65894473842100782989920163 98841710763151174484880245)
  ·
    refine ⟨9266410384045422607957523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 98841710763151174484880245 9266410384045422607957523)
    ·
      refine ⟨13899615576068133911936285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9266410384045422607957523 13899615576068133911936285)
      ·
        refine ⟨5212355841025550216976107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13899615576068133911936285 5212355841025550216976107)
        ·
          refine ⟨7818533761538325325464161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5212355841025550216976107 7818533761538325325464161)
          ·
            refine ⟨5863900321153743994098121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7818533761538325325464161 5863900321153743994098121)
            ·
              refine ⟨4397925240865307995573591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5863900321153743994098121 4397925240865307995573591)
              ·
                refine ⟨6596887861297961993360387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4397925240865307995573591 6596887861297961993360387)
                ·
                  refine ⟨9895331791946942990040581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6596887861297961993360387 9895331791946942990040581)
                  ·
                    refine ⟨1855374710990051810632609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9895331791946942990040581 1855374710990051810632609)
                    ·
                      refine ⟨1391531033242538857974457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1855374710990051810632609 1391531033242538857974457)
                      ·
                        rfl

theorem cell23_2709997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 2, 1, 1, 4, 2].length) (baseStart_2709997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2709997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2709997 prefixEnd_2709997 := by exact prefixLift 2709997
  have htrace : WordTrace (prefixWord ++ tailWord_2709997) baseStart_2709997 baseEnd_2709997 := by
    simpa [prefixWord, tailWord_2709997, baseEnd_2709997] using wordTrace_append hprefix tailTrace_2709997
  have hstable : (prefixWord ++ tailWord_2709997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2709997).length < 2 ^ (prefixWord ++ tailWord_2709997).sum := by decide
  have hdescent : baseEnd_2709997 < baseStart_2709997 := by decide
  rcases family_descends (prefixWord ++ tailWord_2709997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2710018 : List Nat := [3, 4, 1, 2, 3, 1, 2, 1, 1, 3, 2]
def baseStart_2710018 : Nat := 118140960795 + 2710018 * 2 ^ 59
def prefixEnd_2710018 : Nat := 4983230072969 + 3 ^ 40 * 2710018 * 2
def baseEnd_2710018 : Nat := 1391541816336283275811861

theorem tailTrace_2710018 : CollatzResearch.WordTrace tailWord_2710018 prefixEnd_2710018 1391541816336283275811861 := by
  unfold tailWord_2710018
  simp only [CollatzResearch.WordTrace]
  refine ⟨24710619174018773767848677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65894984464050063380929805 24710619174018773767848677)
  ·
    refine ⟨4633241095128520081471627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24710619174018773767848677 4633241095128520081471627)
    ·
      refine ⟨6949861642692780122207441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4633241095128520081471627 6949861642692780122207441)
      ·
        refine ⟨5212396232019585091655581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6949861642692780122207441 5212396232019585091655581)
        ·
          refine ⟨1954648587007344409370843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5212396232019585091655581 1954648587007344409370843)
          ·
            refine ⟨2931972880511016614056265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1954648587007344409370843 2931972880511016614056265)
            ·
              refine ⟨2198979660383262460542199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2931972880511016614056265 2198979660383262460542199)
              ·
                refine ⟨3298469490574893690813299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2198979660383262460542199 3298469490574893690813299)
                ·
                  refine ⟨4947704235862340536219949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3298469490574893690813299 4947704235862340536219949)
                  ·
                    refine ⟨1855389088448377701082481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4947704235862340536219949 1855389088448377701082481)
                    ·
                      refine ⟨1391541816336283275811861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1855389088448377701082481 1391541816336283275811861)
                      ·
                        rfl

theorem cell23_2710018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 2, 1, 1, 3, 2].length) (baseStart_2710018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2710018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2710018 prefixEnd_2710018 := by exact prefixLift 2710018
  have htrace : WordTrace (prefixWord ++ tailWord_2710018) baseStart_2710018 baseEnd_2710018 := by
    simpa [prefixWord, tailWord_2710018, baseEnd_2710018] using wordTrace_append hprefix tailTrace_2710018
  have hstable : (prefixWord ++ tailWord_2710018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2710018).length < 2 ^ (prefixWord ++ tailWord_2710018).sum := by decide
  have hdescent : baseEnd_2710018 < baseStart_2710018 := by decide
  rcases family_descends (prefixWord ++ tailWord_2710018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2710020 : List Nat := [2, 3, 2, 3, 1, 1, 1, 5, 5]
def baseStart_2710020 : Nat := 118140960795 + 2710020 * 2 ^ 59
def prefixEnd_2710020 : Nat := 4983230072969 + 3 ^ 40 * 2710020 * 2
def baseEnd_2710020 : Nat := 154615871477510251998539

theorem tailTrace_2710020 : CollatzResearch.WordTrace tailWord_2710020 prefixEnd_2710020 154615871477510251998539 := by
  unfold tailWord_2710020
  simp only [CollatzResearch.WordTrace]
  refine ⟨49421274821033924706483757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65895033094711899608645009 49421274821033924706483757)
  ·
    refine ⟨18532978057887721764931409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49421274821033924706483757 18532978057887721764931409)
    ·
      refine ⟨13899733543415791323698557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18532978057887721764931409 13899733543415791323698557)
      ·
        refine ⟨5212400078780921746386959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13899733543415791323698557 5212400078780921746386959)
        ·
          refine ⟨7818600118171382619580439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5212400078780921746386959 7818600118171382619580439)
          ·
            refine ⟨11727900177257073929370659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7818600118171382619580439 11727900177257073929370659)
            ·
              refine ⟨17591850265885610894055989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11727900177257073929370659 17591850265885610894055989)
              ·
                refine ⟨1649235962426776021317749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17591850265885610894055989 1649235962426776021317749)
                ·
                  refine ⟨154615871477510251998539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1649235962426776021317749 154615871477510251998539)
                  ·
                    rfl

theorem cell23_2710020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 5, 5].length) (baseStart_2710020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2710020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2710020 prefixEnd_2710020 := by exact prefixLift 2710020
  have htrace : WordTrace (prefixWord ++ tailWord_2710020) baseStart_2710020 baseEnd_2710020 := by
    simpa [prefixWord, tailWord_2710020, baseEnd_2710020] using wordTrace_append hprefix tailTrace_2710020
  have hstable : (prefixWord ++ tailWord_2710020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2710020).length < 2 ^ (prefixWord ++ tailWord_2710020).sum := by decide
  have hdescent : baseEnd_2710020 < baseStart_2710020 := by decide
  rcases family_descends (prefixWord ++ tailWord_2710020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2710070 : List Nat := [5, 1, 2, 1, 2, 1, 2, 1, 1, 3, 4]
def baseStart_2710070 : Nat := 118140960795 + 2710070 * 2 ^ 59
def prefixEnd_2710070 : Nat := 4983230072969 + 3 ^ 40 * 2710070 * 2
def baseEnd_2710070 : Nat := 1391568517330317072361621

theorem tailTrace_2710070 : CollatzResearch.WordTrace tailWord_2710070 prefixEnd_2710070 1391568517330317072361621 := by
  unfold tailWord_2710070
  simp only [CollatzResearch.WordTrace]
  refine ⟨6177773330742919247017979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 65896248861257805301525109 6177773330742919247017979)
  ·
    refine ⟨9266659996114378870526969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6177773330742919247017979 9266659996114378870526969)
    ·
      refine ⟨6949994997085784152895227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9266659996114378870526969 6949994997085784152895227)
      ·
        refine ⟨10424992495628676229342841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6949994997085784152895227 10424992495628676229342841)
        ·
          refine ⟨7818744371721507172007131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10424992495628676229342841 7818744371721507172007131)
          ·
            refine ⟨11728116557582260758010697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7818744371721507172007131 11728116557582260758010697)
            ·
              refine ⟨8796087418186695568508023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11728116557582260758010697 8796087418186695568508023)
              ·
                refine ⟨13194131127280043352762035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8796087418186695568508023 13194131127280043352762035)
                ·
                  refine ⟨19791196690920065029143053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13194131127280043352762035 19791196690920065029143053)
                  ·
                    refine ⟨7421698759095024385928645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19791196690920065029143053 7421698759095024385928645)
                    ·
                      refine ⟨1391568517330317072361621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7421698759095024385928645 1391568517330317072361621)
                      ·
                        rfl

theorem cell23_2710070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 1, 1, 3, 4].length) (baseStart_2710070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2710070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2710070 prefixEnd_2710070 := by exact prefixLift 2710070
  have htrace : WordTrace (prefixWord ++ tailWord_2710070) baseStart_2710070 baseEnd_2710070 := by
    simpa [prefixWord, tailWord_2710070, baseEnd_2710070] using wordTrace_append hprefix tailTrace_2710070
  have hstable : (prefixWord ++ tailWord_2710070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2710070).length < 2 ^ (prefixWord ++ tailWord_2710070).sum := by decide
  have hdescent : baseEnd_2710070 < baseStart_2710070 := by decide
  rcases family_descends (prefixWord ++ tailWord_2710070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2710073 : List Nat := [1, 2, 1, 5, 1, 1, 1, 3, 1, 4, 3]
def baseStart_2710073 : Nat := 118140960795 + 2710073 * 2 ^ 59
def prefixEnd_2710073 : Nat := 4983230072969 + 3 ^ 40 * 2710073 * 2
def baseEnd_2710073 : Nat := 1391570057772280560624107

theorem tailTrace_2710073 : CollatzResearch.WordTrace tailWord_2710073 prefixEnd_2710073 1391570057772280560624107 := by
  unfold tailWord_2710073
  simp only [CollatzResearch.WordTrace]
  refine ⟨98844482710875839464646873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65896321807250559643097915 98844482710875839464646873)
  ·
    refine ⟨74133362033156879598485155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98844482710875839464646873 74133362033156879598485155)
    ·
      refine ⟨111200043049735319397727733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74133362033156879598485155 111200043049735319397727733)
      ·
        refine ⟨10425004035912686193536975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 111200043049735319397727733 10425004035912686193536975)
        ·
          refine ⟨15637506053869029290305463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10425004035912686193536975 15637506053869029290305463)
          ·
            refine ⟨23456259080803543935458195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15637506053869029290305463 23456259080803543935458195)
            ·
              refine ⟨35184388621205315903187293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23456259080803543935458195 35184388621205315903187293)
              ·
                refine ⟨13194145732951993463695235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35184388621205315903187293 13194145732951993463695235)
                ·
                  refine ⟨19791218599427990195542853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13194145732951993463695235 19791218599427990195542853)
                  ·
                    refine ⟨3710853487392748161664285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19791218599427990195542853 3710853487392748161664285)
                    ·
                      refine ⟨1391570057772280560624107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3710853487392748161664285 1391570057772280560624107)
                      ·
                        rfl

theorem cell23_2710073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 3, 1, 4, 3].length) (baseStart_2710073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2710073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2710073 prefixEnd_2710073 := by exact prefixLift 2710073
  have htrace : WordTrace (prefixWord ++ tailWord_2710073) baseStart_2710073 baseEnd_2710073 := by
    simpa [prefixWord, tailWord_2710073, baseEnd_2710073] using wordTrace_append hprefix tailTrace_2710073
  have hstable : (prefixWord ++ tailWord_2710073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2710073).length < 2 ^ (prefixWord ++ tailWord_2710073).sum := by decide
  have hdescent : baseEnd_2710073 < baseStart_2710073 := by decide
  rcases family_descends (prefixWord ++ tailWord_2710073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2710084 : List Nat := [2, 3, 5, 1, 1, 1, 1, 2, 2, 5]
def baseStart_2710084 : Nat := 118140960795 + 2710084 * 2 ^ 59
def prefixEnd_2710084 : Nat := 4983230072969 + 3 ^ 40 * 2710084 * 2
def baseEnd_2710084 : Nat := 463858568686493339195519

theorem tailTrace_2710084 : CollatzResearch.WordTrace tailWord_2710084 prefixEnd_2710084 463858568686493339195519 := by
  unfold tailWord_2710084
  simp only [CollatzResearch.WordTrace]
  refine ⟨49422441956917994171648653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65896589275890658895531537 49422441956917994171648653)
  ·
    refine ⟨18533415733844247814368245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49422441956917994171648653 18533415733844247814368245)
    ·
      refine ⟨1737507725047898232597023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18533415733844247814368245 1737507725047898232597023)
      ·
        refine ⟨2606261587571847348895535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1737507725047898232597023 2606261587571847348895535)
        ·
          refine ⟨3909392381357771023343303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2606261587571847348895535 3909392381357771023343303)
          ·
            refine ⟨5864088572036656535014955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3909392381357771023343303 5864088572036656535014955)
            ·
              refine ⟨8796132858054984802522433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5864088572036656535014955 8796132858054984802522433)
              ·
                refine ⟨6597099643541238601891825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8796132858054984802522433 6597099643541238601891825)
                ·
                  refine ⟨4947824732655928951418869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6597099643541238601891825 4947824732655928951418869)
                  ·
                    refine ⟨463858568686493339195519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4947824732655928951418869 463858568686493339195519)
                    ·
                      rfl

theorem cell23_2710084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_2710084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2710084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2710084 prefixEnd_2710084 := by exact prefixLift 2710084
  have htrace : WordTrace (prefixWord ++ tailWord_2710084) baseStart_2710084 baseEnd_2710084 := by
    simpa [prefixWord, tailWord_2710084, baseEnd_2710084] using wordTrace_append hprefix tailTrace_2710084
  have hstable : (prefixWord ++ tailWord_2710084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2710084).length < 2 ^ (prefixWord ++ tailWord_2710084).sum := by decide
  have hdescent : baseEnd_2710084 < baseStart_2710084 := by decide
  rcases family_descends (prefixWord ++ tailWord_2710084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2710090 : List Nat := [3, 1, 2, 1, 1, 5, 1, 2, 2, 2, 3]
def baseStart_2710090 : Nat := 118140960795 + 2710090 * 2 ^ 59
def prefixEnd_2710090 : Nat := 4983230072969 + 3 ^ 40 * 2710090 * 2
def baseEnd_2710090 : Nat := 1391578786943406994111529

theorem tailTrace_2710090 : CollatzResearch.WordTrace tailWord_2710090 prefixEnd_2710090 1391578786943406994111529 := by
  unfold tailWord_2710090
  simp only [CollatzResearch.WordTrace]
  refine ⟨24711275687953562842003931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65896735167876167578677149 24711275687953562842003931)
  ·
    refine ⟨37066913531930344263005897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24711275687953562842003931 37066913531930344263005897)
    ·
      refine ⟨27800185148947758197254423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37066913531930344263005897 27800185148947758197254423)
      ·
        refine ⟨41700277723421637295881635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27800185148947758197254423 41700277723421637295881635)
        ·
          refine ⟨62550416585132455943822453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41700277723421637295881635 62550416585132455943822453)
          ·
            refine ⟨5864101554856167744733355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 62550416585132455943822453 5864101554856167744733355)
            ·
              refine ⟨8796152332284251617100033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5864101554856167744733355 8796152332284251617100033)
              ·
                refine ⟨6597114249213188712825025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8796152332284251617100033 6597114249213188712825025)
                ·
                  refine ⟨4947835686909891534618769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6597114249213188712825025 4947835686909891534618769)
                  ·
                    refine ⟨3710876765182418650964077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4947835686909891534618769 3710876765182418650964077)
                    ·
                      refine ⟨1391578786943406994111529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3710876765182418650964077 1391578786943406994111529)
                      ·
                        rfl

theorem cell23_2710090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 2, 2, 2, 3].length) (baseStart_2710090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2710090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2710090 prefixEnd_2710090 := by exact prefixLift 2710090
  have htrace : WordTrace (prefixWord ++ tailWord_2710090) baseStart_2710090 baseEnd_2710090 := by
    simpa [prefixWord, tailWord_2710090, baseEnd_2710090] using wordTrace_append hprefix tailTrace_2710090
  have hstable : (prefixWord ++ tailWord_2710090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2710090).length < 2 ^ (prefixWord ++ tailWord_2710090).sum := by decide
  have hdescent : baseEnd_2710090 < baseStart_2710090 := by decide
  rcases family_descends (prefixWord ++ tailWord_2710090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2710096 : List Nat := [2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 6]
def baseStart_2710096 : Nat := 118140960795 + 2710096 * 2 ^ 59
def prefixEnd_2710096 : Nat := 4983230072969 + 3 ^ 40 * 2710096 * 2
def baseEnd_2710096 : Nat := 1391581867827333970636501

theorem tailTrace_2710096 : CollatzResearch.WordTrace tailWord_2710096 prefixEnd_2710096 1391581867827333970636501 := by
  unfold tailWord_2710096
  simp only [CollatzResearch.WordTrace]
  refine ⟨49422660794896257196367071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65896881059861676261822761 49422660794896257196367071)
  ·
    refine ⟨74133991192344385794550607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49422660794896257196367071 74133991192344385794550607)
    ·
      refine ⟨111200986788516578691825911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74133991192344385794550607 111200986788516578691825911)
      ·
        refine ⟨166801480182774868037738867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111200986788516578691825911 166801480182774868037738867)
        ·
          refine ⟨250202220274162302056608301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166801480182774868037738867 250202220274162302056608301)
          ·
            refine ⟨93825832602810863271228113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 250202220274162302056608301 93825832602810863271228113)
            ·
              refine ⟨70369374452108147453421085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93825832602810863271228113 70369374452108147453421085)
              ·
                refine ⟨26388515419540555295032907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 70369374452108147453421085 26388515419540555295032907)
                ·
                  refine ⟨39582773129310832942549361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26388515419540555295032907 39582773129310832942549361)
                  ·
                    refine ⟨29687079846983124706912021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39582773129310832942549361 29687079846983124706912021)
                    ·
                      refine ⟨1391581867827333970636501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 29687079846983124706912021 1391581867827333970636501)
                      ·
                        rfl

theorem cell23_2710096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 6].length) (baseStart_2710096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2710096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2710096 prefixEnd_2710096 := by exact prefixLift 2710096
  have htrace : WordTrace (prefixWord ++ tailWord_2710096) baseStart_2710096 baseEnd_2710096 := by
    simpa [prefixWord, tailWord_2710096, baseEnd_2710096] using wordTrace_append hprefix tailTrace_2710096
  have hstable : (prefixWord ++ tailWord_2710096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2710096).length < 2 ^ (prefixWord ++ tailWord_2710096).sum := by decide
  have hdescent : baseEnd_2710096 < baseStart_2710096 := by decide
  rcases family_descends (prefixWord ++ tailWord_2710096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2710106 : List Nat := [3, 1, 1, 2, 1, 1, 1, 1, 1, 11]
def baseStart_2710106 : Nat := 118140960795 + 2710106 * 2 ^ 59
def prefixEnd_2710106 : Nat := 4983230072969 + 3 ^ 40 * 2710106 * 2
def baseEnd_2710106 : Nat := 463862334211292977170485

theorem tailTrace_2710106 : CollatzResearch.WordTrace tailWord_2710106 prefixEnd_2710106 463862334211292977170485 := by
  unfold tailWord_2710106
  simp only [CollatzResearch.WordTrace]
  refine ⟨24711421579939071525149543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65897124213170857400398781 24711421579939071525149543)
  ·
    refine ⟨37067132369908607287724315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24711421579939071525149543 37067132369908607287724315)
    ·
      refine ⟨55600698554862910931586473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37067132369908607287724315 55600698554862910931586473)
      ·
        refine ⟨41700523916147183198689855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55600698554862910931586473 41700523916147183198689855)
        ·
          refine ⟨62550785874220774798034783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41700523916147183198689855 62550785874220774798034783)
          ·
            refine ⟨93826178811331162197052175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62550785874220774798034783 93826178811331162197052175)
            ·
              refine ⟨140739268216996743295578263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93826178811331162197052175 140739268216996743295578263)
              ·
                refine ⟨211108902325495114943367395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 140739268216996743295578263 211108902325495114943367395)
                ·
                  refine ⟨316663353488242672415051093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 211108902325495114943367395 316663353488242672415051093)
                  ·
                    refine ⟨463862334211292977170485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 316663353488242672415051093 463862334211292977170485)
                    ·
                      rfl

theorem cell23_2710106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 1, 11].length) (baseStart_2710106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2710106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2710106 prefixEnd_2710106 := by exact prefixLift 2710106
  have htrace : WordTrace (prefixWord ++ tailWord_2710106) baseStart_2710106 baseEnd_2710106 := by
    simpa [prefixWord, tailWord_2710106, baseEnd_2710106] using wordTrace_append hprefix tailTrace_2710106
  have hstable : (prefixWord ++ tailWord_2710106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2710106).length < 2 ^ (prefixWord ++ tailWord_2710106).sum := by decide
  have hdescent : baseEnd_2710106 < baseStart_2710106 := by decide
  rcases family_descends (prefixWord ++ tailWord_2710106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2710123 : List Nat := [1, 1, 1, 1, 2, 2, 1, 8, 1, 5]
def baseStart_2710123 : Nat := 118140960795 + 2710123 * 2 ^ 59
def prefixEnd_2710123 : Nat := 4983230072969 + 3 ^ 40 * 2710123 * 2
def baseEnd_2710123 : Nat := 463865243935001788332959

theorem tailTrace_2710123 : CollatzResearch.WordTrace tailWord_2710123 prefixEnd_2710123 463865243935001788332959 := by
  unfold tailWord_2710123
  simp only [CollatzResearch.WordTrace]
  refine ⟨98846306360694698003967023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65897537573796465335978015 98846306360694698003967023)
  ·
    refine ⟨148269459541042047005950535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98846306360694698003967023 148269459541042047005950535)
    ·
      refine ⟨222404189311563070508925803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148269459541042047005950535 222404189311563070508925803)
      ·
        refine ⟨333606283967344605763388705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222404189311563070508925803 333606283967344605763388705)
        ·
          refine ⟨250204712975508454322541529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 333606283967344605763388705 250204712975508454322541529)
          ·
            refine ⟨187653534731631340741906147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 250204712975508454322541529 187653534731631340741906147)
            ·
              refine ⟨281480302097447011112859221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 187653534731631340741906147 281480302097447011112859221)
              ·
                refine ⟨3298597290204457161478819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 281480302097447011112859221 3298597290204457161478819)
                ·
                  refine ⟨4947895935306685742218229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3298597290204457161478819 4947895935306685742218229)
                  ·
                    refine ⟨463865243935001788332959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4947895935306685742218229 463865243935001788332959)
                    ·
                      rfl

theorem cell23_2710123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 8, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 8, 1, 5].length) (baseStart_2710123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2710123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2710123 prefixEnd_2710123 := by exact prefixLift 2710123
  have htrace : WordTrace (prefixWord ++ tailWord_2710123) baseStart_2710123 baseEnd_2710123 := by
    simpa [prefixWord, tailWord_2710123, baseEnd_2710123] using wordTrace_append hprefix tailTrace_2710123
  have hstable : (prefixWord ++ tailWord_2710123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2710123).length < 2 ^ (prefixWord ++ tailWord_2710123).sum := by decide
  have hdescent : baseEnd_2710123 < baseStart_2710123 := by decide
  rcases family_descends (prefixWord ++ tailWord_2710123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2710173 : List Nat := [1, 4, 2, 1, 1, 1, 2, 3, 1, 1, 6]
def baseStart_2710173 : Nat := 118140960795 + 2710173 * 2 ^ 59
def prefixEnd_2710173 : Nat := 4983230072969 + 3 ^ 40 * 2710173 * 2
def baseEnd_2710173 : Nat := 1391621405837730169373647

theorem tailTrace_2710173 : CollatzResearch.WordTrace tailWord_2710173 prefixEnd_2710173 1391621405837730169373647 := by
  unfold tailWord_2710173
  simp only [CollatzResearch.WordTrace]
  refine ⟨98848130010513556543287173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65898753340342371028858115 98848130010513556543287173)
  ·
    refine ⟨18534024376971291851866345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 98848130010513556543287173 18534024376971291851866345)
    ·
      refine ⟨13900518282728468888899759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18534024376971291851866345 13900518282728468888899759)
      ·
        refine ⟨20850777424092703333349639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13900518282728468888899759 20850777424092703333349639)
        ·
          refine ⟨31276166136139055000024459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20850777424092703333349639 31276166136139055000024459)
          ·
            refine ⟨46914249204208582500036689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31276166136139055000024459 46914249204208582500036689)
            ·
              refine ⟨35185686903156436875027517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46914249204208582500036689 35185686903156436875027517)
              ·
                refine ⟨13194632588683663828135319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35185686903156436875027517 13194632588683663828135319)
                ·
                  refine ⟨19791948883025495742202979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13194632588683663828135319 19791948883025495742202979)
                  ·
                    refine ⟨29687923324538243613304469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19791948883025495742202979 29687923324538243613304469)
                    ·
                      refine ⟨1391621405837730169373647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 29687923324538243613304469 1391621405837730169373647)
                      ·
                        rfl

theorem cell23_2710173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 3, 1, 1, 6].length) (baseStart_2710173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2710173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2710173 prefixEnd_2710173 := by exact prefixLift 2710173
  have htrace : WordTrace (prefixWord ++ tailWord_2710173) baseStart_2710173 baseEnd_2710173 := by
    simpa [prefixWord, tailWord_2710173, baseEnd_2710173] using wordTrace_append hprefix tailTrace_2710173
  have hstable : (prefixWord ++ tailWord_2710173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2710173).length < 2 ^ (prefixWord ++ tailWord_2710173).sum := by decide
  have hdescent : baseEnd_2710173 < baseStart_2710173 := by decide
  rcases family_descends (prefixWord ++ tailWord_2710173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2710180 : List Nat := [2, 3, 1, 2, 2, 1, 1, 3, 3, 2, 3]
def baseStart_2710180 : Nat := 118140960795 + 2710180 * 2 ^ 59
def prefixEnd_2710180 : Nat := 4983230072969 + 3 ^ 40 * 2710180 * 2
def baseEnd_2710180 : Nat := 1391625000202311641986115

theorem tailTrace_2710180 : CollatzResearch.WordTrace tailWord_2710180 prefixEnd_2710180 1391625000202311641986115 := by
  unfold tailWord_2710180
  simp only [CollatzResearch.WordTrace]
  refine ⟨49424192660744098369395997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65898923547658797825861329 49424192660744098369395997)
  ·
    refine ⟨18534072247779036888523499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49424192660744098369395997 18534072247779036888523499)
    ·
      refine ⟨27801108371668555332785249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18534072247779036888523499 27801108371668555332785249)
      ·
        refine ⟨20850831278751416499588937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27801108371668555332785249 20850831278751416499588937)
        ·
          refine ⟨15638123459063562374691703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20850831278751416499588937 15638123459063562374691703)
          ·
            refine ⟨23457185188595343562037555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15638123459063562374691703 23457185188595343562037555)
            ·
              refine ⟨35185777782893015343056333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23457185188595343562037555 35185777782893015343056333)
              ·
                refine ⟨13194666668584880753646125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35185777782893015343056333 13194666668584880753646125)
                ·
                  refine ⟨4948000000719330282617297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13194666668584880753646125 4948000000719330282617297)
                  ·
                    refine ⟨3711000000539497711962973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4948000000719330282617297 3711000000539497711962973)
                    ·
                      refine ⟨1391625000202311641986115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3711000000539497711962973 1391625000202311641986115)
                      ·
                        rfl

theorem cell23_2710180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 3, 3, 2, 3].length) (baseStart_2710180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2710180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2710180 prefixEnd_2710180 := by exact prefixLift 2710180
  have htrace : WordTrace (prefixWord ++ tailWord_2710180) baseStart_2710180 baseEnd_2710180 := by
    simpa [prefixWord, tailWord_2710180, baseEnd_2710180] using wordTrace_append hprefix tailTrace_2710180
  have hstable : (prefixWord ++ tailWord_2710180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2710180).length < 2 ^ (prefixWord ++ tailWord_2710180).sum := by decide
  have hdescent : baseEnd_2710180 < baseStart_2710180 := by decide
  rcases family_descends (prefixWord ++ tailWord_2710180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2710221 : List Nat := [1, 6, 2, 1, 3, 1, 1, 1, 1, 6]
def baseStart_2710221 : Nat := 118140960795 + 2710221 * 2 ^ 59
def prefixEnd_2710221 : Nat := 4983230072969 + 3 ^ 40 * 2710221 * 2
def baseEnd_2710221 : Nat := 463882017636381993857809

theorem tailTrace_2710221 : CollatzResearch.WordTrace tailWord_2710221 prefixEnd_2710221 463882017636381993857809 := by
  unfold tailWord_2710221
  simp only [CollatzResearch.WordTrace]
  refine ⟨98849880714339660741034517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65899920476226440494023011 98849880714339660741034517)
  ·
    refine ⟨4633588158484671597235993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 98849880714339660741034517 4633588158484671597235993)
    ·
      refine ⟨3475191118863503697926995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4633588158484671597235993 3475191118863503697926995)
      ·
        refine ⟨5212786678295255546890493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3475191118863503697926995 5212786678295255546890493)
        ·
          refine ⟨1954795004360720830083935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5212786678295255546890493 1954795004360720830083935)
          ·
            refine ⟨2932192506541081245125903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1954795004360720830083935 2932192506541081245125903)
            ·
              refine ⟨4398288759811621867688855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2932192506541081245125903 4398288759811621867688855)
              ·
                refine ⟨6597433139717432801533283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4398288759811621867688855 6597433139717432801533283)
                ·
                  refine ⟨9896149709576149202299925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6597433139717432801533283 9896149709576149202299925)
                  ·
                    refine ⟨463882017636381993857809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9896149709576149202299925 463882017636381993857809)
                    ·
                      rfl

theorem cell23_2710221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 1, 1, 1, 6].length) (baseStart_2710221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2710221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2710221 prefixEnd_2710221 := by exact prefixLift 2710221
  have htrace : WordTrace (prefixWord ++ tailWord_2710221) baseStart_2710221 baseEnd_2710221 := by
    simpa [prefixWord, tailWord_2710221, baseEnd_2710221] using wordTrace_append hprefix tailTrace_2710221
  have hstable : (prefixWord ++ tailWord_2710221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2710221).length < 2 ^ (prefixWord ++ tailWord_2710221).sum := by decide
  have hdescent : baseEnd_2710221 < baseStart_2710221 := by decide
  rcases family_descends (prefixWord ++ tailWord_2710221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2710254 : List Nat := [4, 1, 2, 1, 1, 3, 2, 3, 1, 3, 2]
def baseStart_2710254 : Nat := 118140960795 + 2710254 * 2 ^ 59
def prefixEnd_2710254 : Nat := 4983230072969 + 3 ^ 40 * 2710254 * 2
def baseEnd_2710254 : Nat := 1391662997770744352460775

theorem tailTrace_2710254 : CollatzResearch.WordTrace tailWord_2710254 prefixEnd_2710254 1391662997770744352460775 := by
  unfold tailWord_2710254
  simp only [CollatzResearch.WordTrace]
  refine ⟨12356385540402513422123227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65900722882146738251323877 12356385540402513422123227)
  ·
    refine ⟨18534578310603770133184841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12356385540402513422123227 18534578310603770133184841)
    ·
      refine ⟨13900933732952827599888631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18534578310603770133184841 13900933732952827599888631)
      ·
        refine ⟨20851400599429241399832947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13900933732952827599888631 20851400599429241399832947)
        ·
          refine ⟨31277100899143862099749421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20851400599429241399832947 31277100899143862099749421)
          ·
            refine ⟨11728912837178948287406033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31277100899143862099749421 11728912837178948287406033)
            ·
              refine ⟨8796684627884211215554525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11728912837178948287406033 8796684627884211215554525)
              ·
                refine ⟨3298756735456579205832947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8796684627884211215554525 3298756735456579205832947)
                ·
                  refine ⟨4948135103184868808749421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3298756735456579205832947 4948135103184868808749421)
                  ·
                    refine ⟨1855550663694325803281033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4948135103184868808749421 1855550663694325803281033)
                    ·
                      refine ⟨1391662997770744352460775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1855550663694325803281033 1391662997770744352460775)
                      ·
                        rfl

theorem cell23_2710254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 3, 1, 3, 2].length) (baseStart_2710254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2710254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2710254 prefixEnd_2710254 := by exact prefixLift 2710254
  have htrace : WordTrace (prefixWord ++ tailWord_2710254) baseStart_2710254 baseEnd_2710254 := by
    simpa [prefixWord, tailWord_2710254, baseEnd_2710254] using wordTrace_append hprefix tailTrace_2710254
  have hstable : (prefixWord ++ tailWord_2710254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2710254).length < 2 ^ (prefixWord ++ tailWord_2710254).sum := by decide
  have hdescent : baseEnd_2710254 < baseStart_2710254 := by decide
  rcases family_descends (prefixWord ++ tailWord_2710254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2710301 : List Nat := [1, 4, 2, 4, 1, 1, 1, 2, 1, 4, 2]
def baseStart_2710301 : Nat := 118140960795 + 2710301 * 2 ^ 59
def prefixEnd_2710301 : Nat := 4983230072969 + 3 ^ 40 * 2710301 * 2
def baseEnd_2710301 : Nat := 1391687131361505668573059

theorem tailTrace_2710301 : CollatzResearch.WordTrace tailWord_2710301 prefixEnd_2710301 1391687131361505668573059 := by
  unfold tailWord_2710301
  simp only [CollatzResearch.WordTrace]
  refine ⟨98852798554049834403946757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65901865702699889602631171 98852798554049834403946757)
  ·
    refine ⟨18534899728884343950740017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 98852798554049834403946757 18534899728884343950740017)
    ·
      refine ⟨13901174796663257963055013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18534899728884343950740017 13901174796663257963055013)
      ·
        refine ⟨2606470274374360868072815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13901174796663257963055013 2606470274374360868072815)
        ·
          refine ⟨3909705411561541302109223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2606470274374360868072815 3909705411561541302109223)
          ·
            refine ⟨5864558117342311953163835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3909705411561541302109223 5864558117342311953163835)
            ·
              refine ⟨8796837176013467929745753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5864558117342311953163835 8796837176013467929745753)
              ·
                refine ⟨6597627882010100947309315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8796837176013467929745753 6597627882010100947309315)
                ·
                  refine ⟨9896441823015151420963973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6597627882010100947309315 9896441823015151420963973)
                  ·
                    refine ⟨1855582841815340891430745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9896441823015151420963973 1855582841815340891430745)
                    ·
                      refine ⟨1391687131361505668573059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1855582841815340891430745 1391687131361505668573059)
                      ·
                        rfl

theorem cell23_2710301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 2, 1, 4, 2].length) (baseStart_2710301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2710301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2710301 prefixEnd_2710301 := by exact prefixLift 2710301
  have htrace : WordTrace (prefixWord ++ tailWord_2710301) baseStart_2710301 baseEnd_2710301 := by
    simpa [prefixWord, tailWord_2710301, baseEnd_2710301] using wordTrace_append hprefix tailTrace_2710301
  have hstable : (prefixWord ++ tailWord_2710301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2710301).length < 2 ^ (prefixWord ++ tailWord_2710301).sum := by decide
  have hdescent : baseEnd_2710301 < baseStart_2710301 := by decide
  rcases family_descends (prefixWord ++ tailWord_2710301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2710313 : List Nat := [1, 2, 1, 1, 1, 1, 1, 4, 3, 1, 7]
def baseStart_2710313 : Nat := 118140960795 + 2710313 * 2 ^ 59
def prefixEnd_2710313 : Nat := 4983230072969 + 3 ^ 40 * 2710313 * 2
def baseEnd_2710313 : Nat := 1391693293129359621623003

theorem tailTrace_2710313 : CollatzResearch.WordTrace tailWord_2710313 prefixEnd_2710313 1391693293129359621623003 := by
  unfold tailWord_2710313
  simp only [CollatzResearch.WordTrace]
  refine ⟨98853236230006360453383593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65902157486670906968922395 98853236230006360453383593)
  ·
    refine ⟨74139927172504770340037695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98853236230006360453383593 74139927172504770340037695)
    ·
      refine ⟨111209890758757155510056543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74139927172504770340037695 111209890758757155510056543)
      ·
        refine ⟨166814836138135733265084815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111209890758757155510056543 166814836138135733265084815)
        ·
          refine ⟨250222254207203599897627223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166814836138135733265084815 250222254207203599897627223)
          ·
            refine ⟨375333381310805399846440835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 250222254207203599897627223 375333381310805399846440835)
            ·
              refine ⟨563000071966208099769661253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 375333381310805399846440835 563000071966208099769661253)
              ·
                refine ⟨105562513493664018706811485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 563000071966208099769661253 105562513493664018706811485)
                ·
                  refine ⟨39585942560124007015054307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 105562513493664018706811485 39585942560124007015054307)
                  ·
                    refine ⟨59378913840186010522581461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39585942560124007015054307 59378913840186010522581461)
                    ·
                      refine ⟨1391693293129359621623003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 59378913840186010522581461 1391693293129359621623003)
                      ·
                        rfl

theorem cell23_2710313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 4, 3, 1, 7].length) (baseStart_2710313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2710313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2710313 prefixEnd_2710313 := by exact prefixLift 2710313
  have htrace : WordTrace (prefixWord ++ tailWord_2710313) baseStart_2710313 baseEnd_2710313 := by
    simpa [prefixWord, tailWord_2710313, baseEnd_2710313] using wordTrace_append hprefix tailTrace_2710313
  have hstable : (prefixWord ++ tailWord_2710313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2710313).length < 2 ^ (prefixWord ++ tailWord_2710313).sum := by decide
  have hdescent : baseEnd_2710313 < baseStart_2710313 := by decide
  rcases family_descends (prefixWord ++ tailWord_2710313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2710318 : List Nat := [4, 1, 3, 2, 1, 2, 2, 2, 2, 2, 2]
def baseStart_2710318 : Nat := 118140960795 + 2710318 * 2 ^ 59
def prefixEnd_2710318 : Nat := 4983230072969 + 3 ^ 40 * 2710318 * 2
def baseEnd_2710318 : Nat := 1391695860532632102060481

theorem tailTrace_2710318 : CollatzResearch.WordTrace tailWord_2710318 prefixEnd_2710318 1391695860532632102060481 := by
  unfold tailWord_2710318
  simp only [CollatzResearch.WordTrace]
  refine ⟨12356677324373530788414451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65902279063325497538210405 12356677324373530788414451)
  ·
    refine ⟨18535015986560296182621677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12356677324373530788414451 18535015986560296182621677)
    ·
      refine ⟨6950630994960111068483129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18535015986560296182621677 6950630994960111068483129)
      ·
        refine ⟨5212973246220083301362347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6950630994960111068483129 5212973246220083301362347)
        ·
          refine ⟨7819459869330124952043521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5212973246220083301362347 7819459869330124952043521)
          ·
            refine ⟨5864594901997593714032641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7819459869330124952043521 5864594901997593714032641)
            ·
              refine ⟨4398446176498195285524481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5864594901997593714032641 4398446176498195285524481)
              ·
                refine ⟨3298834632373646464143361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4398446176498195285524481 3298834632373646464143361)
                ·
                  refine ⟨2474125974280234848107521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3298834632373646464143361 2474125974280234848107521)
                  ·
                    refine ⟨1855594480710176136080641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2474125974280234848107521 1855594480710176136080641)
                    ·
                      refine ⟨1391695860532632102060481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1855594480710176136080641 1391695860532632102060481)
                      ·
                        rfl

theorem cell23_2710318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 2, 2, 2, 2, 2].length) (baseStart_2710318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2710318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2710318 prefixEnd_2710318 := by exact prefixLift 2710318
  have htrace : WordTrace (prefixWord ++ tailWord_2710318) baseStart_2710318 baseEnd_2710318 := by
    simpa [prefixWord, tailWord_2710318, baseEnd_2710318] using wordTrace_append hprefix tailTrace_2710318
  have hstable : (prefixWord ++ tailWord_2710318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2710318).length < 2 ^ (prefixWord ++ tailWord_2710318).sum := by decide
  have hdescent : baseEnd_2710318 < baseStart_2710318 := by decide
  rcases family_descends (prefixWord ++ tailWord_2710318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2710334 : List Nat := [4, 2, 1, 2, 3, 1, 1, 1, 2, 3, 3]
def baseStart_2710334 : Nat := 118140960795 + 2710334 * 2 ^ 59
def prefixEnd_2710334 : Nat := 4983230072969 + 3 ^ 40 * 2710334 * 2
def baseEnd_2710334 : Nat := 1391704076223104039460407

theorem tailTrace_2710334 : CollatzResearch.WordTrace tailWord_2710334 prefixEnd_2710334 1391704076223104039460407 := by
  unfold tailWord_2710334
  simp only [CollatzResearch.WordTrace]
  refine ⟨12356750270366285129987257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65902668108620187359932037 12356750270366285129987257)
  ·
    refine ⟨9267562702774713847490443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12356750270366285129987257 9267562702774713847490443)
    ·
      refine ⟨13901344054162070771235665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9267562702774713847490443 13901344054162070771235665)
      ·
        refine ⟨10426008040621553078426749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13901344054162070771235665 10426008040621553078426749)
        ·
          refine ⟨3909753015233082404410031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10426008040621553078426749 3909753015233082404410031)
          ·
            refine ⟨5864629522849623606615047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3909753015233082404410031 5864629522849623606615047)
            ·
              refine ⟨8796944284274435409922571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5864629522849623606615047 8796944284274435409922571)
              ·
                refine ⟨13195416426411653114883857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8796944284274435409922571 13195416426411653114883857)
                ·
                  refine ⟨9896562319808739836162893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13195416426411653114883857 9896562319808739836162893)
                  ·
                    refine ⟨3711210869928277438561085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9896562319808739836162893 3711210869928277438561085)
                    ·
                      refine ⟨1391704076223104039460407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3711210869928277438561085 1391704076223104039460407)
                      ·
                        rfl

theorem cell23_2710334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 1, 2, 3, 3].length) (baseStart_2710334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2710334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2710334 prefixEnd_2710334 := by exact prefixLift 2710334
  have htrace : WordTrace (prefixWord ++ tailWord_2710334) baseStart_2710334 baseEnd_2710334 := by
    simpa [prefixWord, tailWord_2710334, baseEnd_2710334] using wordTrace_append hprefix tailTrace_2710334
  have hstable : (prefixWord ++ tailWord_2710334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2710334).length < 2 ^ (prefixWord ++ tailWord_2710334).sum := by decide
  have hdescent : baseEnd_2710334 < baseStart_2710334 := by decide
  rcases family_descends (prefixWord ++ tailWord_2710334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2710357 : List Nat := [1, 3, 2, 2, 2, 1, 1, 2, 1, 6, 2]
def baseStart_2710357 : Nat := 118140960795 + 2710357 * 2 ^ 59
def prefixEnd_2710357 : Nat := 4983230072969 + 3 ^ 40 * 2710357 * 2
def baseEnd_2710357 : Nat := 1391715886278157449472801

theorem tailTrace_2710357 : CollatzResearch.WordTrace tailWord_2710357 prefixEnd_2710357 1391715886278157449472801 := by
  unfold tailWord_2710357
  simp only [CollatzResearch.WordTrace]
  refine ⟨98854841041846955967985325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65903227361231303978656883 98854841041846955967985325)
  ·
    refine ⟨37070565390692608487994497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98854841041846955967985325 37070565390692608487994497)
    ·
      refine ⟨27802924043019456365995873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37070565390692608487994497 27802924043019456365995873)
      ·
        refine ⟨20852193032264592274496905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27802924043019456365995873 20852193032264592274496905)
        ·
          refine ⟨15639144774198444205872679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20852193032264592274496905 15639144774198444205872679)
          ·
            refine ⟨23458717161297666308809019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15639144774198444205872679 23458717161297666308809019)
            ·
              refine ⟨35188075741946499463213529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23458717161297666308809019 35188075741946499463213529)
              ·
                refine ⟨26391056806459874597410147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35188075741946499463213529 26391056806459874597410147)
                ·
                  refine ⟨39586585209689811896115221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26391056806459874597410147 39586585209689811896115221)
                  ·
                    refine ⟨1855621181704209932630401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 39586585209689811896115221 1855621181704209932630401)
                    ·
                      refine ⟨1391715886278157449472801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1855621181704209932630401 1391715886278157449472801)
                      ·
                        rfl

theorem cell23_2710357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 2, 1, 6, 2].length) (baseStart_2710357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2710357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2710357 prefixEnd_2710357 := by exact prefixLift 2710357
  have htrace : WordTrace (prefixWord ++ tailWord_2710357) baseStart_2710357 baseEnd_2710357 := by
    simpa [prefixWord, tailWord_2710357, baseEnd_2710357] using wordTrace_append hprefix tailTrace_2710357
  have hstable : (prefixWord ++ tailWord_2710357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2710357).length < 2 ^ (prefixWord ++ tailWord_2710357).sum := by decide
  have hdescent : baseEnd_2710357 < baseStart_2710357 := by decide
  rcases family_descends (prefixWord ++ tailWord_2710357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2710380 : List Nat := [2, 2, 1, 1, 4, 1, 3, 1, 8]
def baseStart_2710380 : Nat := 118140960795 + 2710380 * 2 ^ 59
def prefixEnd_2710380 : Nat := 4983230072969 + 3 ^ 40 * 2710380 * 2
def baseEnd_2710380 : Nat := 154636410703690095498355

theorem tailTrace_2710380 : CollatzResearch.WordTrace tailWord_2710380 prefixEnd_2710380 154636410703690095498355 := by
  unfold tailWord_2710380
  simp only [CollatzResearch.WordTrace]
  refine ⟨49427839960381815448036297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65903786613842420597381729 49427839960381815448036297)
  ·
    refine ⟨37070879970286361586027223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49427839960381815448036297 37070879970286361586027223)
    ·
      refine ⟨55606319955429542379040835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37070879970286361586027223 55606319955429542379040835)
      ·
        refine ⟨83409479933144313568561253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55606319955429542379040835 83409479933144313568561253)
        ·
          refine ⟨15639277487464558794105235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 83409479933144313568561253 15639277487464558794105235)
          ·
            refine ⟨23458916231196838191157853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15639277487464558794105235 23458916231196838191157853)
            ·
              refine ⟨8797093586698814321684195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23458916231196838191157853 8797093586698814321684195)
              ·
                refine ⟨13195640380048221482526293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8797093586698814321684195 13195640380048221482526293)
                ·
                  refine ⟨154636410703690095498355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13195640380048221482526293 154636410703690095498355)
                  ·
                    rfl

theorem cell23_2710380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 8].length) (baseStart_2710380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2710380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2710380 prefixEnd_2710380 := by exact prefixLift 2710380
  have htrace : WordTrace (prefixWord ++ tailWord_2710380) baseStart_2710380 baseEnd_2710380 := by
    simpa [prefixWord, tailWord_2710380, baseEnd_2710380] using wordTrace_append hprefix tailTrace_2710380
  have hstable : (prefixWord ++ tailWord_2710380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2710380).length < 2 ^ (prefixWord ++ tailWord_2710380).sum := by decide
  have hdescent : baseEnd_2710380 < baseStart_2710380 := by decide
  rcases family_descends (prefixWord ++ tailWord_2710380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2710384 : List Nat := [2, 1, 1, 1, 4, 1, 4, 4, 1, 4]
def baseStart_2710384 : Nat := 118140960795 + 2710384 * 2 ^ 59
def prefixEnd_2710384 : Nat := 4983230072969 + 3 ^ 40 * 2710384 * 2
def baseEnd_2710384 : Nat := 463909916751942947945059

theorem tailTrace_2710384 : CollatzResearch.WordTrace tailWord_2710384 prefixEnd_2710384 463909916751942947945059 := by
  unfold tailWord_2710384
  simp only [CollatzResearch.WordTrace]
  refine ⟨49427912906374569789609103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65903883875166093052812137 49427912906374569789609103)
  ·
    refine ⟨74141869359561854684413655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49427912906374569789609103 74141869359561854684413655)
    ·
      refine ⟨111212804039342782026620483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74141869359561854684413655 111212804039342782026620483)
      ·
        refine ⟨166819206059014173039930725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111212804039342782026620483 166819206059014173039930725)
        ·
          refine ⟨31278601136065157444987011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 166819206059014173039930725 31278601136065157444987011)
          ·
            refine ⟨46917901704097736167480517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31278601136065157444987011 46917901704097736167480517)
            ·
              refine ⟨8797106569518325531402597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46917901704097736167480517 8797106569518325531402597)
              ·
                refine ⟨1649457481784686037137987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8797106569518325531402597 1649457481784686037137987)
                ·
                  refine ⟨2474186222677029055706981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1649457481784686037137987 2474186222677029055706981)
                  ·
                    refine ⟨463909916751942947945059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2474186222677029055706981 463909916751942947945059)
                    ·
                      rfl

theorem cell23_2710384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 4, 1, 4].length) (baseStart_2710384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2710384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2710384 prefixEnd_2710384 := by exact prefixLift 2710384
  have htrace : WordTrace (prefixWord ++ tailWord_2710384) baseStart_2710384 baseEnd_2710384 := by
    simpa [prefixWord, tailWord_2710384, baseEnd_2710384] using wordTrace_append hprefix tailTrace_2710384
  have hstable : (prefixWord ++ tailWord_2710384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2710384).length < 2 ^ (prefixWord ++ tailWord_2710384).sum := by decide
  have hdescent : baseEnd_2710384 < baseStart_2710384 := by decide
  rcases family_descends (prefixWord ++ tailWord_2710384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2710447 : List Nat := [1, 1, 2, 1, 2, 2, 2, 2, 2, 6, 2]
def baseStart_2710447 : Nat := 118140960795 + 2710447 * 2 ^ 59
def prefixEnd_2710447 : Nat := 4983230072969 + 3 ^ 40 * 2710447 * 2
def baseEnd_2710447 : Nat := 1391762099537062097347387

theorem tailTrace_2710447 : CollatzResearch.WordTrace tailWord_2710447 prefixEnd_2710447 1391762099537062097347387 := by
  unfold tailWord_2710447
  simp only [CollatzResearch.WordTrace]
  refine ⟨98858123611520901338761595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65905415741013934225841063 98858123611520901338761595)
  ·
    refine ⟨148287185417281352008142393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98858123611520901338761595 148287185417281352008142393)
    ·
      refine ⟨111215389062961014006106795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148287185417281352008142393 111215389062961014006106795)
      ·
        refine ⟨166823083594441521009160193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111215389062961014006106795 166823083594441521009160193)
        ·
          refine ⟨125117312695831140756870145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 166823083594441521009160193 125117312695831140756870145)
          ·
            refine ⟨93837984521873355567652609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 125117312695831140756870145 93837984521873355567652609)
            ·
              refine ⟨70378488391405016675739457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93837984521873355567652609 70378488391405016675739457)
              ·
                refine ⟨52783866293553762506804593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70378488391405016675739457 52783866293553762506804593)
                ·
                  refine ⟨39587899720165321880103445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52783866293553762506804593 39587899720165321880103445)
                  ·
                    refine ⟨1855682799382749463129849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 39587899720165321880103445 1855682799382749463129849)
                    ·
                      refine ⟨1391762099537062097347387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1855682799382749463129849 1391762099537062097347387)
                      ·
                        rfl

theorem cell23_2710447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 2, 2, 6, 2].length) (baseStart_2710447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2710447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2710447 prefixEnd_2710447 := by exact prefixLift 2710447
  have htrace : WordTrace (prefixWord ++ tailWord_2710447) baseStart_2710447 baseEnd_2710447 := by
    simpa [prefixWord, tailWord_2710447, baseEnd_2710447] using wordTrace_append hprefix tailTrace_2710447
  have hstable : (prefixWord ++ tailWord_2710447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2710447).length < 2 ^ (prefixWord ++ tailWord_2710447).sum := by decide
  have hdescent : baseEnd_2710447 < baseStart_2710447 := by decide
  rcases family_descends (prefixWord ++ tailWord_2710447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2710461 : List Nat := [1, 4, 1, 2, 4, 2, 1, 2, 1, 5]
def baseStart_2710461 : Nat := 118140960795 + 2710461 * 2 ^ 59
def prefixEnd_2710461 : Nat := 4983230072969 + 3 ^ 40 * 2710461 * 2
def baseEnd_2710461 : Nat := 463923096088741680857441

theorem tailTrace_2710461 : CollatzResearch.WordTrace tailWord_2710461 prefixEnd_2710461 463923096088741680857441 := by
  unfold tailWord_2710461
  simp only [CollatzResearch.WordTrace]
  refine ⟨98858634233470181729771237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65905756155646787819847491 98858634233470181729771237)
  ·
    refine ⟨18535993918775659074332107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 98858634233470181729771237 18535993918775659074332107)
    ·
      refine ⟨27803990878163488611498161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18535993918775659074332107 27803990878163488611498161)
      ·
        refine ⟨20852993158622616458623621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27803990878163488611498161 20852993158622616458623621)
        ·
          refine ⟨3909936217241740585991929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20852993158622616458623621 3909936217241740585991929)
          ·
            refine ⟨2932452162931305439493947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3909936217241740585991929 2932452162931305439493947)
            ·
              refine ⟨4398678244396958159240921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2932452162931305439493947 4398678244396958159240921)
              ·
                refine ⟨3299008683297718619430691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4398678244396958159240921 3299008683297718619430691)
                ·
                  refine ⟨4948513024946577929146037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3299008683297718619430691 4948513024946577929146037)
                  ·
                    refine ⟨463923096088741680857441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4948513024946577929146037 463923096088741680857441)
                    ·
                      rfl

theorem cell23_2710461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 1, 2, 1, 5].length) (baseStart_2710461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2710461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2710461 prefixEnd_2710461 := by exact prefixLift 2710461
  have htrace : WordTrace (prefixWord ++ tailWord_2710461) baseStart_2710461 baseEnd_2710461 := by
    simpa [prefixWord, tailWord_2710461, baseEnd_2710461] using wordTrace_append hprefix tailTrace_2710461
  have hstable : (prefixWord ++ tailWord_2710461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2710461).length < 2 ^ (prefixWord ++ tailWord_2710461).sum := by decide
  have hdescent : baseEnd_2710461 < baseStart_2710461 := by decide
  rcases family_descends (prefixWord ++ tailWord_2710461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2710464 : List Nat := [2, 1, 1, 2, 3, 3, 3, 2, 1, 1, 4]
def baseStart_2710464 : Nat := 118140960795 + 2710464 * 2 ^ 59
def prefixEnd_2710464 : Nat := 4983230072969 + 3 ^ 40 * 2710464 * 2
def baseEnd_2710464 : Nat := 1391770828708188530834809

theorem tailTrace_2710464 : CollatzResearch.WordTrace tailWord_2710464 prefixEnd_2710464 1391770828708188530834809 := by
  unfold tailWord_2710464
  simp only [CollatzResearch.WordTrace]
  refine ⟨49429371826229656621065223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65905829101639542161420297 49429371826229656621065223)
  ·
    refine ⟨74144057739344484931597835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49429371826229656621065223 74144057739344484931597835)
    ·
      refine ⟨111216086609016727397396753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74144057739344484931597835 111216086609016727397396753)
      ·
        refine ⟨83412064956762545548047565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111216086609016727397396753 83412064956762545548047565)
        ·
          refine ⟨31279524358785954580517837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83412064956762545548047565 31279524358785954580517837)
          ·
            refine ⟨11729821634544732967694189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31279524358785954580517837 11729821634544732967694189)
            ·
              refine ⟨4398683112954274862885321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11729821634544732967694189 4398683112954274862885321)
              ·
                refine ⟨3299012334715706147163991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4398683112954274862885321 3299012334715706147163991)
                ·
                  refine ⟨4948518502073559220745987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3299012334715706147163991 4948518502073559220745987)
                  ·
                    refine ⟨7422777753110338831118981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4948518502073559220745987 7422777753110338831118981)
                    ·
                      refine ⟨1391770828708188530834809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7422777753110338831118981 1391770828708188530834809)
                      ·
                        rfl

theorem cell23_2710464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 3, 2, 1, 1, 4].length) (baseStart_2710464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2710464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2710464 prefixEnd_2710464 := by exact prefixLift 2710464
  have htrace : WordTrace (prefixWord ++ tailWord_2710464) baseStart_2710464 baseEnd_2710464 := by
    simpa [prefixWord, tailWord_2710464, baseEnd_2710464] using wordTrace_append hprefix tailTrace_2710464
  have hstable : (prefixWord ++ tailWord_2710464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2710464).length < 2 ^ (prefixWord ++ tailWord_2710464).sum := by decide
  have hdescent : baseEnd_2710464 < baseStart_2710464 := by decide
  rcases family_descends (prefixWord ++ tailWord_2710464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2710467 : List Nat := [1, 1, 1, 3, 1, 1, 2, 5, 3, 2, 3]
def baseStart_2710467 : Nat := 118140960795 + 2710467 * 2 ^ 59
def prefixEnd_2710467 : Nat := 4983230072969 + 3 ^ 40 * 2710467 * 2
def baseEnd_2710467 : Nat := 1391772369150152019097295

theorem tailTrace_2710467 : CollatzResearch.WordTrace tailWord_2710467 prefixEnd_2710467 1391772369150152019097295 := by
  unfold tailWord_2710467
  simp only [CollatzResearch.WordTrace]
  refine ⟨98858853071448444754489655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65905902047632296502993103 98858853071448444754489655)
  ·
    refine ⟨148288279607172667131734483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98858853071448444754489655 148288279607172667131734483)
    ·
      refine ⟨222432419410759000697601725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148288279607172667131734483 222432419410759000697601725)
      ·
        refine ⟨83412157279034625261600647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 222432419410759000697601725 83412157279034625261600647)
        ·
          refine ⟨125118235918551937892400971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83412157279034625261600647 125118235918551937892400971)
          ·
            refine ⟨187677353877827906838601457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125118235918551937892400971 187677353877827906838601457)
            ·
              refine ⟨140758015408370930128951093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 187677353877827906838601457 140758015408370930128951093)
              ·
                refine ⟨13196063944534774699589165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 140758015408370930128951093 13196063944534774699589165)
                ·
                  refine ⟨4948523979200540512345937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13196063944534774699589165 4948523979200540512345937)
                  ·
                    refine ⟨3711392984400405384259453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4948523979200540512345937 3711392984400405384259453)
                    ·
                      refine ⟨1391772369150152019097295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3711392984400405384259453 1391772369150152019097295)
                      ·
                        rfl

theorem cell23_2710467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 5, 3, 2, 3].length) (baseStart_2710467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2710467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2710467 prefixEnd_2710467 := by exact prefixLift 2710467
  have htrace : WordTrace (prefixWord ++ tailWord_2710467) baseStart_2710467 baseEnd_2710467 := by
    simpa [prefixWord, tailWord_2710467, baseEnd_2710467] using wordTrace_append hprefix tailTrace_2710467
  have hstable : (prefixWord ++ tailWord_2710467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2710467).length < 2 ^ (prefixWord ++ tailWord_2710467).sum := by decide
  have hdescent : baseEnd_2710467 < baseStart_2710467 := by decide
  rcases family_descends (prefixWord ++ tailWord_2710467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2710484 : List Nat := [2, 4, 1, 2, 1, 2, 3, 1, 1, 1, 5]
def baseStart_2710484 : Nat := 118140960795 + 2710484 * 2 ^ 59
def prefixEnd_2710484 : Nat := 4983230072969 + 3 ^ 40 * 2710484 * 2
def baseEnd_2710484 : Nat := 1391781098321278452584717

theorem tailTrace_2710484 : CollatzResearch.WordTrace tailWord_2710484 prefixEnd_2710484 1391781098321278452584717 := by
  unfold tailWord_2710484
  simp only [CollatzResearch.WordTrace]
  refine ⟨49429736556193428328929253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65906315408257904438572337 49429736556193428328929253)
  ·
    refine ⟨9268075604286267811674235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49429736556193428328929253 9268075604286267811674235)
    ·
      refine ⟨13902113406429401717511353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9268075604286267811674235 13902113406429401717511353)
      ·
        refine ⟨10426585054822051288133515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13902113406429401717511353 10426585054822051288133515)
        ·
          refine ⟨15639877582233076932200273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10426585054822051288133515 15639877582233076932200273)
          ·
            refine ⟨11729908186674807699150205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15639877582233076932200273 11729908186674807699150205)
            ·
              refine ⟨4398715570003052887181327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11729908186674807699150205 4398715570003052887181327)
              ·
                refine ⟨6598073355004579330771991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4398715570003052887181327 6598073355004579330771991)
                ·
                  refine ⟨9897110032506868996157987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6598073355004579330771991 9897110032506868996157987)
                  ·
                    refine ⟨14845665048760303494236981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9897110032506868996157987 14845665048760303494236981)
                    ·
                      refine ⟨1391781098321278452584717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14845665048760303494236981 1391781098321278452584717)
                      ·
                        rfl

theorem cell23_2710484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 3, 1, 1, 1, 5].length) (baseStart_2710484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2710484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2710484 prefixEnd_2710484 := by exact prefixLift 2710484
  have htrace : WordTrace (prefixWord ++ tailWord_2710484) baseStart_2710484 baseEnd_2710484 := by
    simpa [prefixWord, tailWord_2710484, baseEnd_2710484] using wordTrace_append hprefix tailTrace_2710484
  have hstable : (prefixWord ++ tailWord_2710484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2710484).length < 2 ^ (prefixWord ++ tailWord_2710484).sum := by decide
  have hdescent : baseEnd_2710484 < baseStart_2710484 := by decide
  rcases family_descends (prefixWord ++ tailWord_2710484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2710497 : List Nat := [1, 2, 3, 1, 2, 1, 1, 1, 5, 3, 3]
def baseStart_2710497 : Nat := 118140960795 + 2710497 * 2 ^ 59
def prefixEnd_2710497 : Nat := 4983230072969 + 3 ^ 40 * 2710497 * 2
def baseEnd_2710497 : Nat := 1391787773569786901722157

theorem tailTrace_2710497 : CollatzResearch.WordTrace tailWord_2710497 prefixEnd_2710497 1391787773569786901722157 := by
  unfold tailWord_2710497
  simp only [CollatzResearch.WordTrace]
  refine ⟨98859947261339759878081745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65906631507559839918721163 98859947261339759878081745)
  ·
    refine ⟨74144960446004819908561309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98859947261339759878081745 74144960446004819908561309)
    ·
      refine ⟨27804360167251807465710491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74144960446004819908561309 27804360167251807465710491)
      ·
        refine ⟨41706540250877711198565737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27804360167251807465710491 41706540250877711198565737)
        ·
          refine ⟨31279905188158283398924303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41706540250877711198565737 31279905188158283398924303)
          ·
            refine ⟨46919857782237425098386455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31279905188158283398924303 46919857782237425098386455)
            ·
              refine ⟨70379786673356137647579683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46919857782237425098386455 70379786673356137647579683)
              ·
                refine ⟨105569680010034206471369525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70379786673356137647579683 105569680010034206471369525)
                ·
                  refine ⟨9897157500940706856690893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 105569680010034206471369525 9897157500940706856690893)
                  ·
                    refine ⟨3711434062852765071259085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9897157500940706856690893 3711434062852765071259085)
                    ·
                      refine ⟨1391787773569786901722157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3711434062852765071259085 1391787773569786901722157)
                      ·
                        rfl

theorem cell23_2710497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 1, 5, 3, 3].length) (baseStart_2710497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2710497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2710497 prefixEnd_2710497 := by exact prefixLift 2710497
  have htrace : WordTrace (prefixWord ++ tailWord_2710497) baseStart_2710497 baseEnd_2710497 := by
    simpa [prefixWord, tailWord_2710497, baseEnd_2710497] using wordTrace_append hprefix tailTrace_2710497
  have hstable : (prefixWord ++ tailWord_2710497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2710497).length < 2 ^ (prefixWord ++ tailWord_2710497).sum := by decide
  have hdescent : baseEnd_2710497 < baseStart_2710497 := by decide
  rcases family_descends (prefixWord ++ tailWord_2710497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2710564 : List Nat := [2, 3, 1, 4, 1, 1, 2, 1, 2, 6]
def baseStart_2710564 : Nat := 118140960795 + 2710564 * 2 ^ 59
def prefixEnd_2710564 : Nat := 4983230072969 + 3 ^ 40 * 2710564 * 2
def baseEnd_2710564 : Nat := 463940725591212713194783

theorem tailTrace_2710564 : CollatzResearch.WordTrace tailWord_2710564 prefixEnd_2710564 463940725591212713194783 := by
  unfold tailWord_2710564
  simp only [CollatzResearch.WordTrace]
  refine ⟨49431195476048515160385373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65908260634731353547180497 49431195476048515160385373)
  ·
    refine ⟨18536698303518193185144515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49431195476048515160385373 18536698303518193185144515)
    ·
      refine ⟨27805047455277289777716773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18536698303518193185144515 27805047455277289777716773)
      ·
        refine ⟨5213446397864491833321895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27805047455277289777716773 5213446397864491833321895)
        ·
          refine ⟨7820169596796737749982843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5213446397864491833321895 7820169596796737749982843)
          ·
            refine ⟨11730254395195106624974265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7820169596796737749982843 11730254395195106624974265)
            ·
              refine ⟨8797690796396329968730699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11730254395195106624974265 8797690796396329968730699)
              ·
                refine ⟨13196536194594494953096049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8797690796396329968730699 13196536194594494953096049)
                ·
                  refine ⟨9897402145945871214822037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13196536194594494953096049 9897402145945871214822037)
                  ·
                    refine ⟨463940725591212713194783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9897402145945871214822037 463940725591212713194783)
                    ·
                      rfl

theorem cell23_2710564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 1, 2, 6].length) (baseStart_2710564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2710564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2710564 prefixEnd_2710564 := by exact prefixLift 2710564
  have htrace : WordTrace (prefixWord ++ tailWord_2710564) baseStart_2710564 baseEnd_2710564 := by
    simpa [prefixWord, tailWord_2710564, baseEnd_2710564] using wordTrace_append hprefix tailTrace_2710564
  have hstable : (prefixWord ++ tailWord_2710564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2710564).length < 2 ^ (prefixWord ++ tailWord_2710564).sum := by decide
  have hdescent : baseEnd_2710564 < baseStart_2710564 := by decide
  rcases family_descends (prefixWord ++ tailWord_2710564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2710574 : List Nat := [4, 1, 3, 1, 1, 1, 2, 2, 2, 1, 5]
def baseStart_2710574 : Nat := 118140960795 + 2710574 * 2 ^ 59
def prefixEnd_2710574 : Nat := 4983230072969 + 3 ^ 40 * 2710574 * 2
def baseEnd_2710574 : Nat := 1391827311580183100459303

theorem tailTrace_2710574 : CollatzResearch.WordTrace tailWord_2710574 prefixEnd_2710574 1391827311580183100459303 := by
  unfold tailWord_2710574
  simp only [CollatzResearch.WordTrace]
  refine ⟨12357844460257600253579347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65908503788040534685756517 12357844460257600253579347)
  ·
    refine ⟨18536766690386400380369021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12357844460257600253579347 18536766690386400380369021)
    ·
      refine ⟨6951287508894900142638383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18536766690386400380369021 6951287508894900142638383)
      ·
        refine ⟨10426931263342350213957575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6951287508894900142638383 10426931263342350213957575)
        ·
          refine ⟨15640396895013525320936363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10426931263342350213957575 15640396895013525320936363)
          ·
            refine ⟨23460595342520287981404545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15640396895013525320936363 23460595342520287981404545)
            ·
              refine ⟨17595446506890215986053409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23460595342520287981404545 17595446506890215986053409)
              ·
                refine ⟨13196584880167661989540057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17595446506890215986053409 13196584880167661989540057)
                ·
                  refine ⟨9897438660125746492155043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13196584880167661989540057 9897438660125746492155043)
                  ·
                    refine ⟨14846157990188619738232565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9897438660125746492155043 14846157990188619738232565)
                    ·
                      refine ⟨1391827311580183100459303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14846157990188619738232565 1391827311580183100459303)
                      ·
                        rfl

theorem cell23_2710574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 2, 2, 1, 5].length) (baseStart_2710574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2710574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2710574 prefixEnd_2710574 := by exact prefixLift 2710574
  have htrace : WordTrace (prefixWord ++ tailWord_2710574) baseStart_2710574 baseEnd_2710574 := by
    simpa [prefixWord, tailWord_2710574, baseEnd_2710574] using wordTrace_append hprefix tailTrace_2710574
  have hstable : (prefixWord ++ tailWord_2710574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2710574).length < 2 ^ (prefixWord ++ tailWord_2710574).sum := by decide
  have hdescent : baseEnd_2710574 < baseStart_2710574 := by decide
  rcases family_descends (prefixWord ++ tailWord_2710574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2710577 : List Nat := [1, 2, 2, 3, 1, 2, 1, 4, 7]
def baseStart_2710577 : Nat := 118140960795 + 2710577 * 2 ^ 59
def prefixEnd_2710577 : Nat := 4983230072969 + 3 ^ 40 * 2710577 * 2
def baseEnd_2710577 : Nat := 154647650224682954302421

theorem tailTrace_2710577 : CollatzResearch.WordTrace tailWord_2710577 prefixEnd_2710577 154647650224682954302421 := by
  unfold tailWord_2710577
  simp only [CollatzResearch.WordTrace]
  refine ⟨98862865101049933540993985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65908576734033289027329323 98862865101049933540993985)
  ·
    refine ⟨74147148825787450155745489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98862865101049933540993985 74147148825787450155745489)
    ·
      refine ⟨55610361619340587616809117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74147148825787450155745489 55610361619340587616809117)
      ·
        refine ⟨20853885607252720356303419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55610361619340587616809117 20853885607252720356303419)
        ·
          refine ⟨31280828410879080534455129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20853885607252720356303419 31280828410879080534455129)
          ·
            refine ⟨23460621308159310400841347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31280828410879080534455129 23460621308159310400841347)
            ·
              refine ⟨35190931962238965601262021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23460621308159310400841347 35190931962238965601262021)
              ·
                refine ⟨6598299742919806050236629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35190931962238965601262021 6598299742919806050236629)
                ·
                  refine ⟨154647650224682954302421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6598299742919806050236629 154647650224682954302421)
                  ·
                    rfl

theorem cell23_2710577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 4, 7].length) (baseStart_2710577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2710577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2710577 prefixEnd_2710577 := by exact prefixLift 2710577
  have htrace : WordTrace (prefixWord ++ tailWord_2710577) baseStart_2710577 baseEnd_2710577 := by
    simpa [prefixWord, tailWord_2710577, baseEnd_2710577] using wordTrace_append hprefix tailTrace_2710577
  have hstable : (prefixWord ++ tailWord_2710577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2710577).length < 2 ^ (prefixWord ++ tailWord_2710577).sum := by decide
  have hdescent : baseEnd_2710577 < baseStart_2710577 := by decide
  rcases family_descends (prefixWord ++ tailWord_2710577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2710667 : List Nat := [1, 1, 1, 1, 4, 1, 1, 5, 8]
def baseStart_2710667 : Nat := 118140960795 + 2710667 * 2 ^ 59
def prefixEnd_2710667 : Nat := 4983230072969 + 3 ^ 40 * 2710667 * 2
def baseEnd_2710667 : Nat := 154652785031227915177375

theorem tailTrace_2710667 : CollatzResearch.WordTrace tailWord_2710667 prefixEnd_2710667 154652785031227915177375 := by
  unfold tailWord_2710667
  simp only [CollatzResearch.WordTrace]
  refine ⟨98866147670723878911770255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65910765113815919274513503 98866147670723878911770255)
  ·
    refine ⟨148299221506085818367655383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98866147670723878911770255 148299221506085818367655383)
    ·
      refine ⟨222448832259128727551483075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148299221506085818367655383 222448832259128727551483075)
      ·
        refine ⟨333673248388693091327224613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222448832259128727551483075 333673248388693091327224613)
        ·
          refine ⟨62563734072879954623854615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 333673248388693091327224613 62563734072879954623854615)
          ·
            refine ⟨93845601109319931935781923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62563734072879954623854615 93845601109319931935781923)
            ·
              refine ⟨140768401663979897903672885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93845601109319931935781923 140768401663979897903672885)
              ·
                refine ⟨13197037655998115428469333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 140768401663979897903672885 13197037655998115428469333)
                ·
                  refine ⟨154652785031227915177375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13197037655998115428469333 154652785031227915177375)
                  ·
                    rfl

theorem cell23_2710667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 5, 8].length) (baseStart_2710667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2710667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2710667 prefixEnd_2710667 := by exact prefixLift 2710667
  have htrace : WordTrace (prefixWord ++ tailWord_2710667) baseStart_2710667 baseEnd_2710667 := by
    simpa [prefixWord, tailWord_2710667, baseEnd_2710667] using wordTrace_append hprefix tailTrace_2710667
  have hstable : (prefixWord ++ tailWord_2710667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2710667).length < 2 ^ (prefixWord ++ tailWord_2710667).sum := by decide
  have hdescent : baseEnd_2710667 < baseStart_2710667 := by decide
  rcases family_descends (prefixWord ++ tailWord_2710667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2710697 : List Nat := [1, 2, 1, 1, 1, 1, 2, 1, 4, 9]
def baseStart_2710697 : Nat := 118140960795 + 2710697 * 2 ^ 59
def prefixEnd_2710697 : Nat := 4983230072969 + 3 ^ 40 * 2710697 * 2
def baseEnd_2710697 : Nat := 463963489900228706407079

theorem tailTrace_2710697 : CollatzResearch.WordTrace tailWord_2710697 prefixEnd_2710697 463963489900228706407079 := by
  unfold tailWord_2710697
  simp only [CollatzResearch.WordTrace]
  refine ⟨98867241860615194035362345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65911494573743462690241563 98867241860615194035362345)
  ·
    refine ⟨74150431395461395526521759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98867241860615194035362345 74150431395461395526521759)
    ·
      refine ⟨111225647093192093289782639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74150431395461395526521759 111225647093192093289782639)
      ·
        refine ⟨166838470639788139934673959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111225647093192093289782639 166838470639788139934673959)
        ·
          refine ⟨250257705959682209902010939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166838470639788139934673959 250257705959682209902010939)
          ·
            refine ⟨375386558939523314853016409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 250257705959682209902010939 375386558939523314853016409)
            ·
              refine ⟨281539919204642486139762307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 375386558939523314853016409 281539919204642486139762307)
              ·
                refine ⟨422309878806963729209643461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 281539919204642486139762307 422309878806963729209643461)
                ·
                  refine ⟨79183102276305699226808149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 422309878806963729209643461 79183102276305699226808149)
                  ·
                    refine ⟨463963489900228706407079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 79183102276305699226808149 463963489900228706407079)
                    ·
                      rfl

theorem cell23_2710697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 4, 9].length) (baseStart_2710697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2710697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2710697 prefixEnd_2710697 := by exact prefixLift 2710697
  have htrace : WordTrace (prefixWord ++ tailWord_2710697) baseStart_2710697 baseEnd_2710697 := by
    simpa [prefixWord, tailWord_2710697, baseEnd_2710697] using wordTrace_append hprefix tailTrace_2710697
  have hstable : (prefixWord ++ tailWord_2710697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2710697).length < 2 ^ (prefixWord ++ tailWord_2710697).sum := by decide
  have hdescent : baseEnd_2710697 < baseStart_2710697 := by decide
  rcases family_descends (prefixWord ++ tailWord_2710697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2710698 : List Nat := [3, 1, 5, 1, 1, 2, 1, 1, 1, 4, 3]
def baseStart_2710698 : Nat := 118140960795 + 2710698 * 2 ^ 59
def prefixEnd_2710698 : Nat := 4983230072969 + 3 ^ 40 * 2710698 * 2
def baseEnd_2710698 : Nat := 1391890983181340615308733

theorem tailTrace_2710698 : CollatzResearch.WordTrace tailWord_2710698 prefixEnd_2710698 1391890983181340615308733 := by
  unfold tailWord_2710698
  simp only [CollatzResearch.WordTrace]
  refine ⟨24716819583402892801537187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65911518889074380804099165 24716819583402892801537187)
  ·
    refine ⟨37075229375104339202305781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24716819583402892801537187 37075229375104339202305781)
    ·
      refine ⟨3475802753916031800216167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 37075229375104339202305781 3475802753916031800216167)
      ·
        refine ⟨5213704130874047700324251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3475802753916031800216167 5213704130874047700324251)
        ·
          refine ⟨7820556196311071550486377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5213704130874047700324251 7820556196311071550486377)
          ·
            refine ⟨5865417147233303662864783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7820556196311071550486377 5865417147233303662864783)
            ·
              refine ⟨8798125720849955494297175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5865417147233303662864783 8798125720849955494297175)
              ·
                refine ⟨13197188581274933241445763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8798125720849955494297175 13197188581274933241445763)
                ·
                  refine ⟨19795782871912399862168645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13197188581274933241445763 19795782871912399862168645)
                  ·
                    refine ⟨3711709288483574974156621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19795782871912399862168645 3711709288483574974156621)
                    ·
                      refine ⟨1391890983181340615308733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3711709288483574974156621 1391890983181340615308733)
                      ·
                        rfl

theorem cell23_2710698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 1, 1, 4, 3].length) (baseStart_2710698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2710698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2710698 prefixEnd_2710698 := by exact prefixLift 2710698
  have htrace : WordTrace (prefixWord ++ tailWord_2710698) baseStart_2710698 baseEnd_2710698 := by
    simpa [prefixWord, tailWord_2710698, baseEnd_2710698] using wordTrace_append hprefix tailTrace_2710698
  have hstable : (prefixWord ++ tailWord_2710698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2710698).length < 2 ^ (prefixWord ++ tailWord_2710698).sum := by decide
  have hdescent : baseEnd_2710698 < baseStart_2710698 := by decide
  rcases family_descends (prefixWord ++ tailWord_2710698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2710705 : List Nat := [1, 2, 2, 5, 1, 2, 2, 3, 1, 4]
def baseStart_2710705 : Nat := 118140960795 + 2710705 * 2 ^ 59
def prefixEnd_2710705 : Nat := 4983230072969 + 3 ^ 40 * 2710705 * 2
def baseEnd_2710705 : Nat := 463964859181974029307067

theorem tailTrace_2710705 : CollatzResearch.WordTrace tailWord_2710705 prefixEnd_2710705 463964859181974029307067 := by
  unfold tailWord_2710705
  simp only [CollatzResearch.WordTrace]
  refine ⟨98867533644586211401653569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65911689096390807601102379 98867533644586211401653569)
  ·
    refine ⟨74150650233439658551240177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98867533644586211401653569 74150650233439658551240177)
    ·
      refine ⟨55612987675079743913430133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74150650233439658551240177 55612987675079743913430133)
      ·
        refine ⟨5213717594538725991884075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 55612987675079743913430133 5213717594538725991884075)
        ·
          refine ⟨7820576391808088987826113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5213717594538725991884075 7820576391808088987826113)
          ·
            refine ⟨5865432293856066740869585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7820576391808088987826113 5865432293856066740869585)
            ·
              refine ⟨4399074220392050055652189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5865432293856066740869585 4399074220392050055652189)
              ·
                refine ⟨1649652832647018770869571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4399074220392050055652189 1649652832647018770869571)
                ·
                  refine ⟨2474479248970528156304357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1649652832647018770869571 2474479248970528156304357)
                  ·
                    refine ⟨463964859181974029307067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2474479248970528156304357 463964859181974029307067)
                    ·
                      rfl

theorem cell23_2710705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 2, 3, 1, 4].length) (baseStart_2710705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2710705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2710705 prefixEnd_2710705 := by exact prefixLift 2710705
  have htrace : WordTrace (prefixWord ++ tailWord_2710705) baseStart_2710705 baseEnd_2710705 := by
    simpa [prefixWord, tailWord_2710705, baseEnd_2710705] using wordTrace_append hprefix tailTrace_2710705
  have hstable : (prefixWord ++ tailWord_2710705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2710705).length < 2 ^ (prefixWord ++ tailWord_2710705).sum := by decide
  have hdescent : baseEnd_2710705 < baseStart_2710705 := by decide
  rcases family_descends (prefixWord ++ tailWord_2710705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2710711 : List Nat := [1, 1, 3, 1, 4, 1, 1, 2, 5, 1, 3]
def baseStart_2710711 : Nat := 118140960795 + 2710711 * 2 ^ 59
def prefixEnd_2710711 : Nat := 4983230072969 + 3 ^ 40 * 2710711 * 2
def baseEnd_2710711 : Nat := 1391897658429849064446173

theorem tailTrace_2710711 : CollatzResearch.WordTrace tailWord_2710711 prefixEnd_2710711 1391897658429849064446173 := by
  unfold tailWord_2710711
  simp only [CollatzResearch.WordTrace]
  refine ⟨98867752482564474426371987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65911834988376316284247991 98867752482564474426371987)
  ·
    refine ⟨148301628723846711639557981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98867752482564474426371987 148301628723846711639557981)
    ·
      refine ⟨55613110771442516864834243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 148301628723846711639557981 55613110771442516864834243)
      ·
        refine ⟨83419666157163775297251365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55613110771442516864834243 83419666157163775297251365)
        ·
          refine ⟨15641187404468207868234631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 83419666157163775297251365 15641187404468207868234631)
          ·
            refine ⟨23461781106702311802351947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15641187404468207868234631 23461781106702311802351947)
            ·
              refine ⟨35192671660053467703527921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23461781106702311802351947 35192671660053467703527921)
              ·
                refine ⟨26394503745040100777645941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35192671660053467703527921 26394503745040100777645941)
                ·
                  refine ⟨2474484726097509447904307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26394503745040100777645941 2474484726097509447904307)
                  ·
                    refine ⟨3711727089146264171856461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2474484726097509447904307 3711727089146264171856461)
                    ·
                      refine ⟨1391897658429849064446173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3711727089146264171856461 1391897658429849064446173)
                      ·
                        rfl

theorem cell23_2710711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 2, 5, 1, 3].length) (baseStart_2710711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2710711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2710711 prefixEnd_2710711 := by exact prefixLift 2710711
  have htrace : WordTrace (prefixWord ++ tailWord_2710711) baseStart_2710711 baseEnd_2710711 := by
    simpa [prefixWord, tailWord_2710711, baseEnd_2710711] using wordTrace_append hprefix tailTrace_2710711
  have hstable : (prefixWord ++ tailWord_2710711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2710711).length < 2 ^ (prefixWord ++ tailWord_2710711).sum := by decide
  have hdescent : baseEnd_2710711 < baseStart_2710711 := by decide
  rcases family_descends (prefixWord ++ tailWord_2710711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2710718 : List Nat := [4, 2, 1, 1, 3, 3, 1, 2, 6]
def baseStart_2710718 : Nat := 118140960795 + 2710718 * 2 ^ 59
def prefixEnd_2710718 : Nat := 4983230072969 + 3 ^ 40 * 2710718 * 2
def baseEnd_2710718 : Nat := 154655694754936726339849

theorem tailTrace_2710718 : CollatzResearch.WordTrace tailWord_2710718 prefixEnd_2710718 154655694754936726339849 := by
  unfold tailWord_2710718
  simp only [CollatzResearch.WordTrace]
  refine ⟨12358500974192389327734601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65912005195692743081251205 12358500974192389327734601)
  ·
    refine ⟨9268875730644291995800951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12358500974192389327734601 9268875730644291995800951)
    ·
      refine ⟨13903313595966437993701427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9268875730644291995800951 13903313595966437993701427)
      ·
        refine ⟨20854970393949656990552141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13903313595966437993701427 20854970393949656990552141)
        ·
          refine ⟨7820613897731121371457053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20854970393949656990552141 7820613897731121371457053)
          ·
            refine ⟨2932730211649170514296395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7820613897731121371457053 2932730211649170514296395)
            ·
              refine ⟨4399095317473755771444593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2932730211649170514296395 4399095317473755771444593)
              ·
                refine ⟨3299321488105316828583445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4399095317473755771444593 3299321488105316828583445)
                ·
                  refine ⟨154655694754936726339849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3299321488105316828583445 154655694754936726339849)
                  ·
                    rfl

theorem cell23_2710718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 1, 2, 6].length) (baseStart_2710718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2710718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2710718 prefixEnd_2710718 := by exact prefixLift 2710718
  have htrace : WordTrace (prefixWord ++ tailWord_2710718) baseStart_2710718 baseEnd_2710718 := by
    simpa [prefixWord, tailWord_2710718, baseEnd_2710718] using wordTrace_append hprefix tailTrace_2710718
  have hstable : (prefixWord ++ tailWord_2710718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2710718).length < 2 ^ (prefixWord ++ tailWord_2710718).sum := by decide
  have hdescent : baseEnd_2710718 < baseStart_2710718 := by decide
  rcases family_descends (prefixWord ++ tailWord_2710718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2710721 : List Nat := [1, 2, 6, 1, 1, 1, 1, 1, 1, 2, 6]
def baseStart_2710721 : Nat := 118140960795 + 2710721 * 2 ^ 59
def prefixEnd_2710721 : Nat := 4983230072969 + 3 ^ 40 * 2710721 * 2
def baseEnd_2710721 : Nat := 1391902793236394025321127

theorem tailTrace_2710721 : CollatzResearch.WordTrace tailWord_2710721 prefixEnd_2710721 1391902793236394025321127 := by
  unfold tailWord_2710721
  simp only [CollatzResearch.WordTrace]
  refine ⟨98868117212528246134236017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65912078141685497422824011 98868117212528246134236017)
  ·
    refine ⟨74151087909396184600677013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98868117212528246134236017 74151087909396184600677013)
    ·
      refine ⟨3475832245752946153156735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 74151087909396184600677013 3475832245752946153156735)
      ·
        refine ⟨5213748368629419229735103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3475832245752946153156735 5213748368629419229735103)
        ·
          refine ⟨7820622552944128844602655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5213748368629419229735103 7820622552944128844602655)
          ·
            refine ⟨11730933829416193266903983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7820622552944128844602655 11730933829416193266903983)
            ·
              refine ⟨17596400744124289900355975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11730933829416193266903983 17596400744124289900355975)
              ·
                refine ⟨26394601116186434850533963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17596400744124289900355975 26394601116186434850533963)
                ·
                  refine ⟨39591901674279652275800945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26394601116186434850533963 39591901674279652275800945)
                  ·
                    refine ⟨29693926255709739206850709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39591901674279652275800945 29693926255709739206850709)
                    ·
                      refine ⟨1391902793236394025321127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 29693926255709739206850709 1391902793236394025321127)
                      ·
                        rfl

theorem cell23_2710721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_2710721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2710721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2710721 prefixEnd_2710721 := by exact prefixLift 2710721
  have htrace : WordTrace (prefixWord ++ tailWord_2710721) baseStart_2710721 baseEnd_2710721 := by
    simpa [prefixWord, tailWord_2710721, baseEnd_2710721] using wordTrace_append hprefix tailTrace_2710721
  have hstable : (prefixWord ++ tailWord_2710721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2710721).length < 2 ^ (prefixWord ++ tailWord_2710721).sum := by decide
  have hdescent : baseEnd_2710721 < baseStart_2710721 := by decide
  rcases family_descends (prefixWord ++ tailWord_2710721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2710722 : List Nat := [3, 5, 1, 1, 2, 1, 2, 1, 3, 4]
def baseStart_2710722 : Nat := 118140960795 + 2710722 * 2 ^ 59
def prefixEnd_2710722 : Nat := 4983230072969 + 3 ^ 40 * 2710722 * 2
def baseEnd_2710722 : Nat := 463967768905682840469541

theorem tailTrace_2710722 : CollatzResearch.WordTrace tailWord_2710722 prefixEnd_2710722 463967768905682840469541 := by
  unfold tailWord_2710722
  simp only [CollatzResearch.WordTrace]
  refine ⟨24717038421381155826255605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65912102457016415536681613 24717038421381155826255605)
  ·
    refine ⟨2317222352004483358711463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 24717038421381155826255605 2317222352004483358711463)
    ·
      refine ⟨3475833528006725038067195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2317222352004483358711463 3475833528006725038067195)
      ·
        refine ⟨5213750292010087557100793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3475833528006725038067195 5213750292010087557100793)
        ·
          refine ⟨3910312719007565667825595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5213750292010087557100793 3910312719007565667825595)
          ·
            refine ⟨5865469078511348501738393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3910312719007565667825595 5865469078511348501738393)
            ·
              refine ⟨4399101808883511376303795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5865469078511348501738393 4399101808883511376303795)
              ·
                refine ⟨6598652713325267064455693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4399101808883511376303795 6598652713325267064455693)
                ·
                  refine ⟨2474494767496975149170885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6598652713325267064455693 2474494767496975149170885)
                  ·
                    refine ⟨463967768905682840469541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2474494767496975149170885 463967768905682840469541)
                    ·
                      rfl

theorem cell23_2710722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 2, 1, 3, 4].length) (baseStart_2710722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2710722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2710722 prefixEnd_2710722 := by exact prefixLift 2710722
  have htrace : WordTrace (prefixWord ++ tailWord_2710722) baseStart_2710722 baseEnd_2710722 := by
    simpa [prefixWord, tailWord_2710722, baseEnd_2710722] using wordTrace_append hprefix tailTrace_2710722
  have hstable : (prefixWord ++ tailWord_2710722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2710722).length < 2 ^ (prefixWord ++ tailWord_2710722).sum := by decide
  have hdescent : baseEnd_2710722 < baseStart_2710722 := by decide
  rcases family_descends (prefixWord ++ tailWord_2710722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2710751 : List Nat := [1, 1, 2, 3, 2, 1, 3, 4, 1, 1, 4]
def baseStart_2710751 : Nat := 118140960795 + 2710751 * 2 ^ 59
def prefixEnd_2710751 : Nat := 4983230072969 + 3 ^ 40 * 2710751 * 2
def baseEnd_2710751 : Nat := 1391918197656028907945989

theorem tailTrace_2710751 : CollatzResearch.WordTrace tailWord_2710751 prefixEnd_2710751 1391918197656028907945989 := by
  unfold tailWord_2710751
  simp only [CollatzResearch.WordTrace]
  refine ⟨98869211402419561257828107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65912807601613040838552071 98869211402419561257828107)
  ·
    refine ⟨148303817103629341886742161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98869211402419561257828107 148303817103629341886742161)
    ·
      refine ⟨111227862827722006415056621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148303817103629341886742161 111227862827722006415056621)
      ·
        refine ⟨41710448560395752405646233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 111227862827722006415056621 41710448560395752405646233)
        ·
          refine ⟨31282836420296814304234675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41710448560395752405646233 31282836420296814304234675)
          ·
            refine ⟨46924254630445221456352013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31282836420296814304234675 46924254630445221456352013)
            ·
              refine ⟨17596595486416958046132005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46924254630445221456352013 17596595486416958046132005)
              ·
                refine ⟨3299361653703179633649751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17596595486416958046132005 3299361653703179633649751)
                ·
                  refine ⟨4949042480554769450474627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3299361653703179633649751 4949042480554769450474627)
                  ·
                    refine ⟨7423563720832154175711941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4949042480554769450474627 7423563720832154175711941)
                    ·
                      refine ⟨1391918197656028907945989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7423563720832154175711941 1391918197656028907945989)
                      ·
                        rfl

theorem cell23_2710751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 4, 1, 1, 4].length) (baseStart_2710751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2710751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2710751 prefixEnd_2710751 := by exact prefixLift 2710751
  have htrace : WordTrace (prefixWord ++ tailWord_2710751) baseStart_2710751 baseEnd_2710751 := by
    simpa [prefixWord, tailWord_2710751, baseEnd_2710751] using wordTrace_append hprefix tailTrace_2710751
  have hstable : (prefixWord ++ tailWord_2710751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2710751).length < 2 ^ (prefixWord ++ tailWord_2710751).sum := by decide
  have hdescent : baseEnd_2710751 < baseStart_2710751 := by decide
  rcases family_descends (prefixWord ++ tailWord_2710751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2710762 : List Nat := [3, 1, 3, 1, 1, 5, 1, 3, 1, 1, 3]
def baseStart_2710762 : Nat := 118140960795 + 2710762 * 2 ^ 59
def prefixEnd_2710762 : Nat := 4983230072969 + 3 ^ 40 * 2710762 * 2
def baseEnd_2710762 : Nat := 1391923845943228364908439

theorem tailTrace_2710762 : CollatzResearch.WordTrace tailWord_2710762 prefixEnd_2710762 1391923845943228364908439 := by
  unfold tailWord_2710762
  simp only [CollatzResearch.WordTrace]
  refine ⟨24717403151344927534119635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65913075070253140090985693 24717403151344927534119635)
  ·
    refine ⟨37076104727017391301179453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24717403151344927534119635 37076104727017391301179453)
    ·
      refine ⟨13903539272631521737942295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37076104727017391301179453 13903539272631521737942295)
      ·
        refine ⟨20855308908947282606913443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13903539272631521737942295 20855308908947282606913443)
        ·
          refine ⟨31282963363420923910370165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20855308908947282606913443 31282963363420923910370165)
          ·
            refine ⟨2932777815320711616597203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 31282963363420923910370165 2932777815320711616597203)
            ·
              refine ⟨4399166722981067424895805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2932777815320711616597203 4399166722981067424895805)
              ·
                refine ⟨1649687521117900284335927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4399166722981067424895805 1649687521117900284335927)
                ·
                  refine ⟨2474531281676850426503891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1649687521117900284335927 2474531281676850426503891)
                  ·
                    refine ⟨3711796922515275639755837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2474531281676850426503891 3711796922515275639755837)
                    ·
                      refine ⟨1391923845943228364908439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3711796922515275639755837 1391923845943228364908439)
                      ·
                        rfl

theorem cell23_2710762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 1, 3, 1, 1, 3].length) (baseStart_2710762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2710762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2710762 prefixEnd_2710762 := by exact prefixLift 2710762
  have htrace : WordTrace (prefixWord ++ tailWord_2710762) baseStart_2710762 baseEnd_2710762 := by
    simpa [prefixWord, tailWord_2710762, baseEnd_2710762] using wordTrace_append hprefix tailTrace_2710762
  have hstable : (prefixWord ++ tailWord_2710762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2710762).length < 2 ^ (prefixWord ++ tailWord_2710762).sum := by decide
  have hdescent : baseEnd_2710762 < baseStart_2710762 := by decide
  rcases family_descends (prefixWord ++ tailWord_2710762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2710771 : List Nat := [1, 1, 1, 2, 2, 6, 2, 1, 1, 1, 5]
def baseStart_2710771 : Nat := 118140960795 + 2710771 * 2 ^ 59
def prefixEnd_2710771 : Nat := 4983230072969 + 3 ^ 40 * 2710771 * 2
def baseEnd_2710771 : Nat := 1391928467269118829695897

theorem tailTrace_2710771 : CollatzResearch.WordTrace tailWord_2710771 prefixEnd_2710771 1391928467269118829695897 := by
  unfold tailWord_2710771
  simp only [CollatzResearch.WordTrace]
  refine ⟨98869940862347104673556167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65913293908231403115704111 98869940862347104673556167)
  ·
    refine ⟨148304911293520657010334251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98869940862347104673556167 148304911293520657010334251)
    ·
      refine ⟨222457366940280985515501377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148304911293520657010334251 222457366940280985515501377)
      ·
        refine ⟨166843025205210739136626033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 222457366940280985515501377 166843025205210739136626033)
        ·
          refine ⟨125132268903908054352469525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 166843025205210739136626033 125132268903908054352469525)
          ·
            refine ⟨5865575104870690047772009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 125132268903908054352469525 5865575104870690047772009)
            ·
              refine ⟨4399181328653017535829007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5865575104870690047772009 4399181328653017535829007)
              ·
                refine ⟨6598771992979526303743511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4399181328653017535829007 6598771992979526303743511)
                ·
                  refine ⟨9898157989469289455615267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6598771992979526303743511 9898157989469289455615267)
                  ·
                    refine ⟨14847236984203934183422901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9898157989469289455615267 14847236984203934183422901)
                    ·
                      refine ⟨1391928467269118829695897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14847236984203934183422901 1391928467269118829695897)
                      ·
                        rfl

theorem cell23_2710771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 2, 1, 1, 1, 5].length) (baseStart_2710771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2710771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2710771 prefixEnd_2710771 := by exact prefixLift 2710771
  have htrace : WordTrace (prefixWord ++ tailWord_2710771) baseStart_2710771 baseEnd_2710771 := by
    simpa [prefixWord, tailWord_2710771, baseEnd_2710771] using wordTrace_append hprefix tailTrace_2710771
  have hstable : (prefixWord ++ tailWord_2710771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2710771).length < 2 ^ (prefixWord ++ tailWord_2710771).sum := by decide
  have hdescent : baseEnd_2710771 < baseStart_2710771 := by decide
  rcases family_descends (prefixWord ++ tailWord_2710771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2710785 : List Nat := [1, 2, 4, 1, 1, 3, 3, 1, 3, 2, 2]
def baseStart_2710785 : Nat := 118140960795 + 2710785 * 2 ^ 59
def prefixEnd_2710785 : Nat := 4983230072969 + 3 ^ 40 * 2710785 * 2
def baseEnd_2710785 : Nat := 1391935655998281774920833

theorem tailTrace_2710785 : CollatzResearch.WordTrace tailWord_2710785 prefixEnd_2710785 1391935655998281774920833 := by
  unfold tailWord_2710785
  simp only [CollatzResearch.WordTrace]
  refine ⟨98870451484296385064565809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65913634322864256709710539 98870451484296385064565809)
  ·
    refine ⟨74152838613222288798424357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98870451484296385064565809 74152838613222288798424357)
    ·
      refine ⟨13903657239979179149704567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 74152838613222288798424357 13903657239979179149704567)
      ·
        refine ⟨20855485859968768724556851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13903657239979179149704567 20855485859968768724556851)
        ·
          refine ⟨31283228789953153086835277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20855485859968768724556851 31283228789953153086835277)
          ·
            refine ⟨11731210796232432407563229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31283228789953153086835277 11731210796232432407563229)
            ·
              refine ⟨4399204048587162152836211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11731210796232432407563229 4399204048587162152836211)
              ·
                refine ⟨6598806072880743229254317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4399204048587162152836211 6598806072880743229254317)
                ·
                  refine ⟨2474552277330278710970369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6598806072880743229254317 2474552277330278710970369)
                  ·
                    refine ⟨1855914207997709033227777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2474552277330278710970369 1855914207997709033227777)
                    ·
                      refine ⟨1391935655998281774920833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1855914207997709033227777 1391935655998281774920833)
                      ·
                        rfl

theorem cell23_2710785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 3, 1, 3, 2, 2].length) (baseStart_2710785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2710785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2710785 prefixEnd_2710785 := by exact prefixLift 2710785
  have htrace : WordTrace (prefixWord ++ tailWord_2710785) baseStart_2710785 baseEnd_2710785 := by
    simpa [prefixWord, tailWord_2710785, baseEnd_2710785] using wordTrace_append hprefix tailTrace_2710785
  have hstable : (prefixWord ++ tailWord_2710785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2710785).length < 2 ^ (prefixWord ++ tailWord_2710785).sum := by decide
  have hdescent : baseEnd_2710785 < baseStart_2710785 := by decide
  rcases family_descends (prefixWord ++ tailWord_2710785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2710794 : List Nat := [3, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6]
def baseStart_2710794 : Nat := 118140960795 + 2710794 * 2 ^ 59
def prefixEnd_2710794 : Nat := 4983230072969 + 3 ^ 40 * 2710794 * 2
def baseEnd_2710794 : Nat := 1391940277324172239708291

theorem tailTrace_2710794 : CollatzResearch.WordTrace tailWord_2710794 prefixEnd_2710794 1391940277324172239708291 := by
  unfold tailWord_2710794
  simp only [CollatzResearch.WordTrace]
  refine ⟨24717694935315944900410859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65913853160842519734428957 24717694935315944900410859)
  ·
    refine ⟨37076542402973917350616289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24717694935315944900410859 37076542402973917350616289)
    ·
      refine ⟨27807406802230438012962217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37076542402973917350616289 27807406802230438012962217)
      ·
        refine ⟨20855555101672828509721663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27807406802230438012962217 20855555101672828509721663)
        ·
          refine ⟨31283332652509242764582495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20855555101672828509721663 31283332652509242764582495)
          ·
            refine ⟨46924998978763864146873743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31283332652509242764582495 46924998978763864146873743)
            ·
              refine ⟨70387498468145796220310615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46924998978763864146873743 70387498468145796220310615)
              ·
                refine ⟨105581247702218694330465923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70387498468145796220310615 105581247702218694330465923)
                ·
                  refine ⟨158371871553328041495698885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 105581247702218694330465923 158371871553328041495698885)
                  ·
                    refine ⟨29694725916249007780443541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 158371871553328041495698885 29694725916249007780443541)
                    ·
                      refine ⟨1391940277324172239708291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 29694725916249007780443541 1391940277324172239708291)
                      ·
                        rfl

theorem cell23_2710794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6].length) (baseStart_2710794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2710794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2710794 prefixEnd_2710794 := by exact prefixLift 2710794
  have htrace : WordTrace (prefixWord ++ tailWord_2710794) baseStart_2710794 baseEnd_2710794 := by
    simpa [prefixWord, tailWord_2710794, baseEnd_2710794] using wordTrace_append hprefix tailTrace_2710794
  have hstable : (prefixWord ++ tailWord_2710794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2710794).length < 2 ^ (prefixWord ++ tailWord_2710794).sum := by decide
  have hdescent : baseEnd_2710794 < baseStart_2710794 := by decide
  rcases family_descends (prefixWord ++ tailWord_2710794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2710795 : List Nat := [1, 1, 1, 1, 5, 5, 2, 1, 2, 4]
def baseStart_2710795 : Nat := 118140960795 + 2710795 * 2 ^ 59
def prefixEnd_2710795 : Nat := 4983230072969 + 3 ^ 40 * 2710795 * 2
def baseEnd_2710795 : Nat := 463980263601608911931929

theorem tailTrace_2710795 : CollatzResearch.WordTrace tailWord_2710795 prefixEnd_2710795 463980263601608911931929 := by
  unfold tailWord_2710795
  simp only [CollatzResearch.WordTrace]
  refine ⟨98870816214260156772429839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65913877476173437848286559 98870816214260156772429839)
  ·
    refine ⟨148306224321390235158644759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98870816214260156772429839 148306224321390235158644759)
    ·
      refine ⟨222459336482085352737967139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148306224321390235158644759 222459336482085352737967139)
      ·
        refine ⟨333689004723128029106950709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222459336482085352737967139 333689004723128029106950709)
        ·
          refine ⟨31283344192793252728776629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 333689004723128029106950709 31283344192793252728776629)
          ·
            refine ⟨2932813518074367443322809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 31283344192793252728776629 2932813518074367443322809)
            ·
              refine ⟨2199610138555775582492107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2932813518074367443322809 2199610138555775582492107)
              ·
                refine ⟨3299415207833663373738161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2199610138555775582492107 3299415207833663373738161)
                ·
                  refine ⟨2474561405875247530303621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3299415207833663373738161 2474561405875247530303621)
                  ·
                    refine ⟨463980263601608911931929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2474561405875247530303621 463980263601608911931929)
                    ·
                      rfl

theorem cell23_2710795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 2, 1, 2, 4].length) (baseStart_2710795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2710795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2710795 prefixEnd_2710795 := by exact prefixLift 2710795
  have htrace : WordTrace (prefixWord ++ tailWord_2710795) baseStart_2710795 baseEnd_2710795 := by
    simpa [prefixWord, tailWord_2710795, baseEnd_2710795] using wordTrace_append hprefix tailTrace_2710795
  have hstable : (prefixWord ++ tailWord_2710795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2710795).length < 2 ^ (prefixWord ++ tailWord_2710795).sum := by decide
  have hdescent : baseEnd_2710795 < baseStart_2710795 := by decide
  rcases family_descends (prefixWord ++ tailWord_2710795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2710801 : List Nat := [1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 3]
def baseStart_2710801 : Nat := 118140960795 + 2710801 * 2 ^ 59
def prefixEnd_2710801 : Nat := 4983230072969 + 3 ^ 40 * 2710801 * 2
def baseEnd_2710801 : Nat := 1391943871688753712320759

theorem tailTrace_2710801 : CollatzResearch.WordTrace tailWord_2710801 prefixEnd_2710801 1391943871688753712320759 := by
  unfold tailWord_2710801
  simp only [CollatzResearch.WordTrace]
  refine ⟨98871035052238419797148257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65914023368158946531432171 98871035052238419797148257)
  ·
    refine ⟨74153276289178814847861193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98871035052238419797148257 74153276289178814847861193)
    ·
      refine ⟨55614957216884111135895895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74153276289178814847861193 55614957216884111135895895)
      ·
        refine ⟨83422435825326166703843843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55614957216884111135895895 83422435825326166703843843)
        ·
          refine ⟨125133653737989250055765765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83422435825326166703843843 125133653737989250055765765)
          ·
            refine ⟨23462560075872984385456081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 125133653737989250055765765 23462560075872984385456081)
            ·
              refine ⟨17596920056904738289092061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23462560075872984385456081 17596920056904738289092061)
              ·
                refine ⟨6598845021339276858409523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17596920056904738289092061 6598845021339276858409523)
                ·
                  refine ⟨9898267532008915287614285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6598845021339276858409523 9898267532008915287614285)
                  ·
                    refine ⟨3711850324503343232855357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9898267532008915287614285 3711850324503343232855357)
                    ·
                      refine ⟨1391943871688753712320759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3711850324503343232855357 1391943871688753712320759)
                      ·
                        rfl

theorem cell23_2710801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 3].length) (baseStart_2710801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2710801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2710801 prefixEnd_2710801 := by exact prefixLift 2710801
  have htrace : WordTrace (prefixWord ++ tailWord_2710801) baseStart_2710801 baseEnd_2710801 := by
    simpa [prefixWord, tailWord_2710801, baseEnd_2710801] using wordTrace_append hprefix tailTrace_2710801
  have hstable : (prefixWord ++ tailWord_2710801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2710801).length < 2 ^ (prefixWord ++ tailWord_2710801).sum := by decide
  have hdescent : baseEnd_2710801 < baseStart_2710801 := by decide
  rcases family_descends (prefixWord ++ tailWord_2710801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2710835 : List Nat := [1, 1, 1, 2, 5, 3, 2, 2, 2, 1, 3]
def baseStart_2710835 : Nat := 118140960795 + 2710835 * 2 ^ 59
def prefixEnd_2710835 : Nat := 4983230072969 + 3 ^ 40 * 2710835 * 2
def baseEnd_2710835 : Nat := 1391961330031006579295603

theorem tailTrace_2710835 : CollatzResearch.WordTrace tailWord_2710835 prefixEnd_2710835 1391961330031006579295603 := by
  unfold tailWord_2710835
  simp only [CollatzResearch.WordTrace]
  refine ⟨98872275134115243603885959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65914850089410162402590639 98872275134115243603885959)
  ·
    refine ⟨148308412701172865405828939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98872275134115243603885959 148308412701172865405828939)
    ·
      refine ⟨222462619051759298108743409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148308412701172865405828939 222462619051759298108743409)
      ·
        refine ⟨166846964288819473581557557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 222462619051759298108743409 166846964288819473581557557)
        ·
          refine ⟨15641902902076825648271021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 166846964288819473581557557 15641902902076825648271021)
          ·
            refine ⟨5865713588278809618101633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15641902902076825648271021 5865713588278809618101633)
            ·
              refine ⟨4399285191209107213576225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5865713588278809618101633 4399285191209107213576225)
              ·
                refine ⟨3299463893406830410182169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4399285191209107213576225 3299463893406830410182169)
                ·
                  refine ⟨2474597920055122807636627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3299463893406830410182169 2474597920055122807636627)
                  ·
                    refine ⟨3711896880082684211454941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2474597920055122807636627 3711896880082684211454941)
                    ·
                      refine ⟨1391961330031006579295603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3711896880082684211454941 1391961330031006579295603)
                      ·
                        rfl

theorem cell23_2710835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 2, 2, 2, 1, 3].length) (baseStart_2710835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2710835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2710835 prefixEnd_2710835 := by exact prefixLift 2710835
  have htrace : WordTrace (prefixWord ++ tailWord_2710835) baseStart_2710835 baseEnd_2710835 := by
    simpa [prefixWord, tailWord_2710835, baseEnd_2710835] using wordTrace_append hprefix tailTrace_2710835
  have hstable : (prefixWord ++ tailWord_2710835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2710835).length < 2 ^ (prefixWord ++ tailWord_2710835).sum := by decide
  have hdescent : baseEnd_2710835 < baseStart_2710835 := by decide
  rcases family_descends (prefixWord ++ tailWord_2710835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2710852 : List Nat := [2, 3, 4, 1, 1, 1, 2, 3, 2, 1, 3]
def baseStart_2710852 : Nat := 118140960795 + 2710852 * 2 ^ 59
def prefixEnd_2710852 : Nat := 4983230072969 + 3 ^ 40 * 2710852 * 2
def baseEnd_2710852 : Nat := 1391970059202133012783025

theorem tailTrace_2710852 : CollatzResearch.WordTrace tailWord_2710852 prefixEnd_2710852 1391970059202133012783025 := by
  unfold tailWord_2710852
  simp only [CollatzResearch.WordTrace]
  refine ⟨49436447587526827753627405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65915263450035770338169873 49436447587526827753627405)
  ·
    refine ⟨18538667845322560407610277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49436447587526827753627405 18538667845322560407610277)
    ·
      refine ⟨3476000220997980076426927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18538667845322560407610277 3476000220997980076426927)
      ·
        refine ⟨5214000331496970114640391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3476000220997980076426927 5214000331496970114640391)
        ·
          refine ⟨7821000497245455171960587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5214000331496970114640391 7821000497245455171960587)
          ·
            refine ⟨11731500745868182757940881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7821000497245455171960587 11731500745868182757940881)
            ·
              refine ⟨8798625559401137068455661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11731500745868182757940881 8798625559401137068455661)
              ·
                refine ⟨3299484584775426400670873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8798625559401137068455661 3299484584775426400670873)
                ·
                  refine ⟨2474613438581569800503155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3299484584775426400670873 2474613438581569800503155)
                  ·
                    refine ⟨3711920157872354700754733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2474613438581569800503155 3711920157872354700754733)
                    ·
                      refine ⟨1391970059202133012783025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3711920157872354700754733 1391970059202133012783025)
                      ·
                        rfl

theorem cell23_2710852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 3, 2, 1, 3].length) (baseStart_2710852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2710852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2710852 prefixEnd_2710852 := by exact prefixLift 2710852
  have htrace : WordTrace (prefixWord ++ tailWord_2710852) baseStart_2710852 baseEnd_2710852 := by
    simpa [prefixWord, tailWord_2710852, baseEnd_2710852] using wordTrace_append hprefix tailTrace_2710852
  have hstable : (prefixWord ++ tailWord_2710852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2710852).length < 2 ^ (prefixWord ++ tailWord_2710852).sum := by decide
  have hdescent : baseEnd_2710852 < baseStart_2710852 := by decide
  rcases family_descends (prefixWord ++ tailWord_2710852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2710870 : List Nat := [5, 2, 3, 1, 1, 1, 2, 3, 1, 2, 2]
def baseStart_2710870 : Nat := 118140960795 + 2710870 * 2 ^ 59
def prefixEnd_2710870 : Nat := 4983230072969 + 3 ^ 40 * 2710870 * 2
def baseEnd_2710870 : Nat := 1391979301853913942357943

theorem tailTrace_2710870 : CollatzResearch.WordTrace tailWord_2710870 prefixEnd_2710870 1391979301853913942357943 := by
  unfold tailWord_2710870
  simp only [CollatzResearch.WordTrace]
  refine ⟨6179596980561777786338129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 65915701125992296387606709 6179596980561777786338129)
  ·
    refine ⟨4634697735421333339753597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6179596980561777786338129 4634697735421333339753597)
    ·
      refine ⟨1738011650783000002407599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4634697735421333339753597 1738011650783000002407599)
      ·
        refine ⟨2607017476174500003611399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1738011650783000002407599 2607017476174500003611399)
        ·
          refine ⟨3910526214261750005417099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2607017476174500003611399 3910526214261750005417099)
          ·
            refine ⟨5865789321392625008125649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3910526214261750005417099 5865789321392625008125649)
            ·
              refine ⟨4399341991044468756094237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5865789321392625008125649 4399341991044468756094237)
              ·
                refine ⟨1649753246641675783535339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4399341991044468756094237 1649753246641675783535339)
                ·
                  refine ⟨2474629869962513675303009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1649753246641675783535339 2474629869962513675303009)
                  ·
                    refine ⟨1855972402471885256477257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2474629869962513675303009 1855972402471885256477257)
                    ·
                      refine ⟨1391979301853913942357943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1855972402471885256477257 1391979301853913942357943)
                      ·
                        rfl

theorem cell23_2710870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 2, 3, 1, 2, 2].length) (baseStart_2710870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2710870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2710870 prefixEnd_2710870 := by exact prefixLift 2710870
  have htrace : WordTrace (prefixWord ++ tailWord_2710870) baseStart_2710870 baseEnd_2710870 := by
    simpa [prefixWord, tailWord_2710870, baseEnd_2710870] using wordTrace_append hprefix tailTrace_2710870
  have hstable : (prefixWord ++ tailWord_2710870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2710870).length < 2 ^ (prefixWord ++ tailWord_2710870).sum := by decide
  have hdescent : baseEnd_2710870 < baseStart_2710870 := by decide
  rcases family_descends (prefixWord ++ tailWord_2710870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2710892 : List Nat := [2, 2, 1, 1, 5, 1, 3, 2, 2, 2, 2]
def baseStart_2710892 : Nat := 118140960795 + 2710892 * 2 ^ 59
def prefixEnd_2710892 : Nat := 4983230072969 + 3 ^ 40 * 2710892 * 2
def baseEnd_2710892 : Nat := 1391990598428312856282841

theorem tailTrace_2710892 : CollatzResearch.WordTrace tailWord_2710892 prefixEnd_2710892 1391990598428312856282841 := by
  unfold tailWord_2710892
  simp only [CollatzResearch.WordTrace]
  refine ⟨49437177047454371169355465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65916236063272494892473953 49437177047454371169355465)
  ·
    refine ⟨37077882785590778377016599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49437177047454371169355465 37077882785590778377016599)
    ·
      refine ⟨55616824178386167565524899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37077882785590778377016599 55616824178386167565524899)
      ·
        refine ⟨83425236267579251348287349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55616824178386167565524899 83425236267579251348287349)
        ·
          refine ⟨7821115900085554813901939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 83425236267579251348287349 7821115900085554813901939)
          ·
            refine ⟨11731673850128332220852909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7821115900085554813901939 11731673850128332220852909)
            ·
              refine ⟨4399377693798124582819841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11731673850128332220852909 4399377693798124582819841)
              ·
                refine ⟨3299533270348593437114881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4399377693798124582819841 3299533270348593437114881)
                ·
                  refine ⟨2474649952761445077836161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3299533270348593437114881 2474649952761445077836161)
                  ·
                    refine ⟨1855987464571083808377121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2474649952761445077836161 1855987464571083808377121)
                    ·
                      refine ⟨1391990598428312856282841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1855987464571083808377121 1391990598428312856282841)
                      ·
                        rfl

theorem cell23_2710892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 2, 2].length) (baseStart_2710892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2710892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2710892 prefixEnd_2710892 := by exact prefixLift 2710892
  have htrace : WordTrace (prefixWord ++ tailWord_2710892) baseStart_2710892 baseEnd_2710892 := by
    simpa [prefixWord, tailWord_2710892, baseEnd_2710892] using wordTrace_append hprefix tailTrace_2710892
  have hstable : (prefixWord ++ tailWord_2710892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2710892).length < 2 ^ (prefixWord ++ tailWord_2710892).sum := by decide
  have hdescent : baseEnd_2710892 < baseStart_2710892 := by decide
  rcases family_descends (prefixWord ++ tailWord_2710892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2710898 : List Nat := [3, 2, 1, 2, 1, 2, 1, 6, 5]
def baseStart_2710898 : Nat := 118140960795 + 2710898 * 2 ^ 59
def prefixEnd_2710898 : Nat := 4983230072969 + 3 ^ 40 * 2710898 * 2
def baseEnd_2710898 : Nat := 154665964368026648089757

theorem tailTrace_2710898 : CollatzResearch.WordTrace tailWord_2710898 prefixEnd_2710898 154665964368026648089757 := by
  unfold tailWord_2710898
  simp only [CollatzResearch.WordTrace]
  refine ⟨24718643233221751340857337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65916381955258003575619565 24718643233221751340857337)
  ·
    refine ⟨18538982424916313505643003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24718643233221751340857337 18538982424916313505643003)
    ·
      refine ⟨27808473637374470258464505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18538982424916313505643003 27808473637374470258464505)
      ·
        refine ⟨20856355228030852693848379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27808473637374470258464505 20856355228030852693848379)
        ·
          refine ⟨31284532842046279040772569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20856355228030852693848379 31284532842046279040772569)
          ·
            refine ⟨23463399631534709280579427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31284532842046279040772569 23463399631534709280579427)
            ·
              refine ⟨35195099447302063920869141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23463399631534709280579427 35195099447302063920869141)
              ·
                refine ⟨1649770286592284246290741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 35195099447302063920869141 1649770286592284246290741)
                ·
                  refine ⟨154665964368026648089757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1649770286592284246290741 154665964368026648089757)
                  ·
                    rfl

theorem cell23_2710898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 6, 5].length) (baseStart_2710898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2710898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2710898 prefixEnd_2710898 := by exact prefixLift 2710898
  have htrace : WordTrace (prefixWord ++ tailWord_2710898) baseStart_2710898 baseEnd_2710898 := by
    simpa [prefixWord, tailWord_2710898, baseEnd_2710898] using wordTrace_append hprefix tailTrace_2710898
  have hstable : (prefixWord ++ tailWord_2710898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2710898).length < 2 ^ (prefixWord ++ tailWord_2710898).sum := by decide
  have hdescent : baseEnd_2710898 < baseStart_2710898 := by decide
  rcases family_descends (prefixWord ++ tailWord_2710898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2710931 : List Nat := [1, 1, 1, 2, 1, 2, 1, 1, 8, 1, 4]
def baseStart_2710931 : Nat := 118140960795 + 2710931 * 2 ^ 59
def prefixEnd_2710931 : Nat := 4983230072969 + 3 ^ 40 * 2710931 * 2
def baseEnd_2710931 : Nat := 1392010624173838203695161

theorem tailTrace_2710931 : CollatzResearch.WordTrace tailWord_2710931 prefixEnd_2710931 1392010624173838203695161 := by
  unfold tailWord_2710931
  simp only [CollatzResearch.WordTrace]
  refine ⟨98875776541767451999380647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65917184361178301332920431 98875776541767451999380647)
  ·
    refine ⟨148313664812651177999070971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98875776541767451999380647 148313664812651177999070971)
    ·
      refine ⟨222470497218976766998606457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148313664812651177999070971 222470497218976766998606457)
      ·
        refine ⟨166852872914232575248954843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 222470497218976766998606457 166852872914232575248954843)
        ·
          refine ⟨250279309371348862873432265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166852872914232575248954843 250279309371348862873432265)
          ·
            refine ⟨187709482028511647155074199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 250279309371348862873432265 187709482028511647155074199)
            ·
              refine ⟨281564223042767470732611299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 187709482028511647155074199 281564223042767470732611299)
              ·
                refine ⟨422346334564151206098916949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 281564223042767470732611299 422346334564151206098916949)
                ·
                  refine ⟨4949371108173646946471683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 422346334564151206098916949 4949371108173646946471683)
                  ·
                    refine ⟨7424056662260470419707525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4949371108173646946471683 7424056662260470419707525)
                    ·
                      refine ⟨1392010624173838203695161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7424056662260470419707525 1392010624173838203695161)
                      ·
                        rfl

theorem cell23_2710931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 8, 1, 4].length) (baseStart_2710931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2710931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2710931 prefixEnd_2710931 := by exact prefixLift 2710931
  have htrace : WordTrace (prefixWord ++ tailWord_2710931) baseStart_2710931 baseEnd_2710931 := by
    simpa [prefixWord, tailWord_2710931, baseEnd_2710931] using wordTrace_append hprefix tailTrace_2710931
  have hstable : (prefixWord ++ tailWord_2710931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2710931).length < 2 ^ (prefixWord ++ tailWord_2710931).sum := by decide
  have hdescent : baseEnd_2710931 < baseStart_2710931 := by decide
  rcases family_descends (prefixWord ++ tailWord_2710931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2710932 : List Nat := [2, 4, 2, 1, 2, 3, 1, 3, 5]
def baseStart_2710932 : Nat := 118140960795 + 2710932 * 2 ^ 59
def prefixEnd_2710932 : Nat := 4983230072969 + 3 ^ 40 * 2710932 * 2
def baseEnd_2710932 : Nat := 154667904183832522198073

theorem tailTrace_2710932 : CollatzResearch.WordTrace tailWord_2710932 prefixEnd_2710932 154667904183832522198073 := by
  unfold tailWord_2710932
  simp only [CollatzResearch.WordTrace]
  refine ⟨49437906507381914585083525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65917208676509219446778033 49437906507381914585083525)
  ·
    refine ⟨9269607470134108984703161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49437906507381914585083525 9269607470134108984703161)
    ·
      refine ⟨6952205602600581738527371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9269607470134108984703161 6952205602600581738527371)
      ·
        refine ⟨10428308403900872607791057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6952205602600581738527371 10428308403900872607791057)
        ·
          refine ⟨7821231302925654455843293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10428308403900872607791057 7821231302925654455843293)
          ·
            refine ⟨2932961738597120420941235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7821231302925654455843293 2932961738597120420941235)
            ·
              refine ⟨4399442607895680631411853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2932961738597120420941235 4399442607895680631411853)
              ·
                refine ⟨1649790977960880236779445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4399442607895680631411853 1649790977960880236779445)
                ·
                  refine ⟨154667904183832522198073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1649790977960880236779445 154667904183832522198073)
                  ·
                    rfl

theorem cell23_2710932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 1, 3, 5].length) (baseStart_2710932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2710932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2710932 prefixEnd_2710932 := by exact prefixLift 2710932
  have htrace : WordTrace (prefixWord ++ tailWord_2710932) baseStart_2710932 baseEnd_2710932 := by
    simpa [prefixWord, tailWord_2710932, baseEnd_2710932] using wordTrace_append hprefix tailTrace_2710932
  have hstable : (prefixWord ++ tailWord_2710932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2710932).length < 2 ^ (prefixWord ++ tailWord_2710932).sum := by decide
  have hdescent : baseEnd_2710932 < baseStart_2710932 := by decide
  rcases family_descends (prefixWord ++ tailWord_2710932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2711005 : List Nat := [1, 4, 3, 1, 1, 3, 2, 2, 6]
def baseStart_2711005 : Nat := 118140960795 + 2711005 * 2 ^ 59
def prefixEnd_2711005 : Nat := 4983230072969 + 3 ^ 40 * 2711005 * 2
def baseEnd_2711005 : Nat := 154672069082474546018869

theorem tailTrace_2711005 : CollatzResearch.WordTrace tailWord_2711005 prefixEnd_2711005 154672069082474546018869 := by
  unfold tailWord_2711005
  simp only [CollatzResearch.WordTrace]
  refine ⟨98878475543499362637574469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65918983695666241758382979 98878475543499362637574469)
  ·
    refine ⟨18539714164406130494545213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 98878475543499362637574469 18539714164406130494545213)
    ·
      refine ⟨6952392811652298935454455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18539714164406130494545213 6952392811652298935454455)
      ·
        refine ⟨10428589217478448403181683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6952392811652298935454455 10428589217478448403181683)
        ·
          refine ⟨15642883826217672604772525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10428589217478448403181683 15642883826217672604772525)
          ·
            refine ⟨5866081434831627226789697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15642883826217672604772525 5866081434831627226789697)
            ·
              refine ⟨4399561076123720420092273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5866081434831627226789697 4399561076123720420092273)
              ·
                refine ⟨3299670807092790315069205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4399561076123720420092273 3299670807092790315069205)
                ·
                  refine ⟨154672069082474546018869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3299670807092790315069205 154672069082474546018869)
                  ·
                    rfl

theorem cell23_2711005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 2, 2, 6].length) (baseStart_2711005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2711005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2711005 prefixEnd_2711005 := by exact prefixLift 2711005
  have htrace : WordTrace (prefixWord ++ tailWord_2711005) baseStart_2711005 baseEnd_2711005 := by
    simpa [prefixWord, tailWord_2711005, baseEnd_2711005] using wordTrace_append hprefix tailTrace_2711005
  have hstable : (prefixWord ++ tailWord_2711005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2711005).length < 2 ^ (prefixWord ++ tailWord_2711005).sum := by decide
  have hdescent : baseEnd_2711005 < baseStart_2711005 := by decide
  rcases family_descends (prefixWord ++ tailWord_2711005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2711009 : List Nat := [1, 2, 3, 1, 2, 5, 2, 2, 1, 4]
def baseStart_2711009 : Nat := 118140960795 + 2711009 * 2 ^ 59
def prefixEnd_2711009 : Nat := 4983230072969 + 3 ^ 40 * 2711009 * 2
def baseEnd_2711009 : Nat := 464016891888296299506601

theorem tailTrace_2711009 : CollatzResearch.WordTrace tailWord_2711009 prefixEnd_2711009 464016891888296299506601 := by
  unfold tailWord_2711009
  simp only [CollatzResearch.WordTrace]
  refine ⟨98878621435484871320720081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65919080956989914213813387 98878621435484871320720081)
  ·
    refine ⟨74158966076613653490540061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98878621435484871320720081 74158966076613653490540061)
    ·
      refine ⟨27809612278730120058952523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74158966076613653490540061 27809612278730120058952523)
      ·
        refine ⟨41714418418095180088428785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27809612278730120058952523 41714418418095180088428785)
        ·
          refine ⟨31285813813571385066321589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41714418418095180088428785 31285813813571385066321589)
          ·
            refine ⟨2933045045022317349967649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 31285813813571385066321589 2933045045022317349967649)
            ·
              refine ⟨2199783783766738012475737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2933045045022317349967649 2199783783766738012475737)
              ·
                refine ⟨1649837837825053509356803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2199783783766738012475737 1649837837825053509356803)
                ·
                  refine ⟨2474756756737580264035205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1649837837825053509356803 2474756756737580264035205)
                  ·
                    refine ⟨464016891888296299506601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2474756756737580264035205 464016891888296299506601)
                    ·
                      rfl

theorem cell23_2711009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 2, 2, 1, 4].length) (baseStart_2711009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2711009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2711009 prefixEnd_2711009 := by exact prefixLift 2711009
  have htrace : WordTrace (prefixWord ++ tailWord_2711009) baseStart_2711009 baseEnd_2711009 := by
    simpa [prefixWord, tailWord_2711009, baseEnd_2711009] using wordTrace_append hprefix tailTrace_2711009
  have hstable : (prefixWord ++ tailWord_2711009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2711009).length < 2 ^ (prefixWord ++ tailWord_2711009).sum := by decide
  have hdescent : baseEnd_2711009 < baseStart_2711009 := by decide
  rcases family_descends (prefixWord ++ tailWord_2711009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2711048 : List Nat := [2, 1, 3, 2, 1, 1, 4, 2, 1, 6]
def baseStart_2711048 : Nat := 118140960795 + 2711048 * 2 ^ 59
def prefixEnd_2711048 : Nat := 4983230072969 + 3 ^ 40 * 2711048 * 2
def baseEnd_2711048 : Nat := 464023567136804748644041

theorem tailTrace_2711048 : CollatzResearch.WordTrace tailWord_2711048 prefixEnd_2711048 464023567136804748644041 := by
  unfold tailWord_2711048
  simp only [CollatzResearch.WordTrace]
  refine ⟨49440021941171790490694899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65920029254895720654259865 49440021941171790490694899)
  ·
    refine ⟨74160032911757685736042349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49440021941171790490694899 74160032911757685736042349)
    ·
      refine ⟨27810012341909132151015881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74160032911757685736042349 27810012341909132151015881)
      ·
        refine ⟨20857509256431849113261911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27810012341909132151015881 20857509256431849113261911)
        ·
          refine ⟨31286263884647773669892867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20857509256431849113261911 31286263884647773669892867)
          ·
            refine ⟨46929395826971660504839301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31286263884647773669892867 46929395826971660504839301)
            ·
              refine ⟨8799261717557186344657369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46929395826971660504839301 8799261717557186344657369)
              ·
                refine ⟨6599446288167889758493027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8799261717557186344657369 6599446288167889758493027)
                ·
                  refine ⟨9899169432251834637739541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6599446288167889758493027 9899169432251834637739541)
                  ·
                    refine ⟨464023567136804748644041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9899169432251834637739541 464023567136804748644041)
                    ·
                      rfl

theorem cell23_2711048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 2, 1, 6].length) (baseStart_2711048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2711048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2711048 prefixEnd_2711048 := by exact prefixLift 2711048
  have htrace : WordTrace (prefixWord ++ tailWord_2711048) baseStart_2711048 baseEnd_2711048 := by
    simpa [prefixWord, tailWord_2711048, baseEnd_2711048] using wordTrace_append hprefix tailTrace_2711048
  have hstable : (prefixWord ++ tailWord_2711048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2711048).length < 2 ^ (prefixWord ++ tailWord_2711048).sum := by decide
  have hdescent : baseEnd_2711048 < baseStart_2711048 := by decide
  rcases family_descends (prefixWord ++ tailWord_2711048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2711068 : List Nat := [2, 2, 3, 1, 2, 1, 2, 2, 1, 1, 6]
def baseStart_2711068 : Nat := 118140960795 + 2711068 * 2 ^ 59
def prefixEnd_2711068 : Nat := 4983230072969 + 3 ^ 40 * 2711068 * 2
def baseEnd_2711068 : Nat := 1392080971023504167682031

theorem tailTrace_2711068 : CollatzResearch.WordTrace tailWord_2711068 prefixEnd_2711068 1392080971023504167682031 := by
  unfold tailWord_2711068
  simp only [CollatzResearch.WordTrace]
  refine ⟨49440386671135562198558929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65920515561514082931411905 49440386671135562198558929)
  ·
    refine ⟨37080290003351671648919197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49440386671135562198558929 37080290003351671648919197)
    ·
      refine ⟨13905108751256876868344699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37080290003351671648919197 13905108751256876868344699)
      ·
        refine ⟨20857663126885315302517049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13905108751256876868344699 20857663126885315302517049)
        ·
          refine ⟨15643247345163986476887787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20857663126885315302517049 15643247345163986476887787)
          ·
            refine ⟨23464871017745979715331681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15643247345163986476887787 23464871017745979715331681)
            ·
              refine ⟨17598653263309484786498761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23464871017745979715331681 17598653263309484786498761)
              ·
                refine ⟨13198989947482113589874071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17598653263309484786498761 13198989947482113589874071)
                ·
                  refine ⟨19798484921223170384811107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13198989947482113589874071 19798484921223170384811107)
                  ·
                    refine ⟨29697727381834755577216661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19798484921223170384811107 29697727381834755577216661)
                    ·
                      refine ⟨1392080971023504167682031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 29697727381834755577216661 1392080971023504167682031)
                      ·
                        rfl

theorem cell23_2711068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 2, 1, 1, 6].length) (baseStart_2711068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2711068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2711068 prefixEnd_2711068 := by exact prefixLift 2711068
  have htrace : WordTrace (prefixWord ++ tailWord_2711068) baseStart_2711068 baseEnd_2711068 := by
    simpa [prefixWord, tailWord_2711068, baseEnd_2711068] using wordTrace_append hprefix tailTrace_2711068
  have hstable : (prefixWord ++ tailWord_2711068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2711068).length < 2 ^ (prefixWord ++ tailWord_2711068).sum := by decide
  have hdescent : baseEnd_2711068 < baseStart_2711068 := by decide
  rcases family_descends (prefixWord ++ tailWord_2711068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2711075 : List Nat := [1, 1, 1, 4, 5, 1, 1, 2, 1, 1, 5]
def baseStart_2711075 : Nat := 118140960795 + 2711075 * 2 ^ 59
def prefixEnd_2711075 : Nat := 4983230072969 + 3 ^ 40 * 2711075 * 2
def baseEnd_2711075 : Nat := 1392084565388085640294499

theorem tailTrace_2711075 : CollatzResearch.WordTrace tailWord_2711075 prefixEnd_2711075 1392084565388085640294499 := by
  unfold tailWord_2711075
  simp only [CollatzResearch.WordTrace]
  refine ⟨98881028653245764592622679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65920685768830509728415119 98881028653245764592622679)
  ·
    refine ⟨148321542979868646888934019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98881028653245764592622679 148321542979868646888934019)
    ·
      refine ⟨222482314469802970333401029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148321542979868646888934019 222482314469802970333401029)
      ·
        refine ⟨41715433963088056937512693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 222482314469802970333401029 41715433963088056937512693)
        ·
          refine ⟨3910821934039505337891815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 41715433963088056937512693 3910821934039505337891815)
          ·
            refine ⟨5866232901059258006837723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3910821934039505337891815 5866232901059258006837723)
            ·
              refine ⟨8799349351588887010256585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5866232901059258006837723 8799349351588887010256585)
              ·
                refine ⟨6599512013691665257692439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8799349351588887010256585 6599512013691665257692439)
                ·
                  refine ⟨9899268020537497886538659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6599512013691665257692439 9899268020537497886538659)
                  ·
                    refine ⟨14848902030806246829807989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9899268020537497886538659 14848902030806246829807989)
                    ·
                      refine ⟨1392084565388085640294499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14848902030806246829807989 1392084565388085640294499)
                      ·
                        rfl

theorem cell23_2711075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 2, 1, 1, 5].length) (baseStart_2711075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2711075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2711075 prefixEnd_2711075 := by exact prefixLift 2711075
  have htrace : WordTrace (prefixWord ++ tailWord_2711075) baseStart_2711075 baseEnd_2711075 := by
    simpa [prefixWord, tailWord_2711075, baseEnd_2711075] using wordTrace_append hprefix tailTrace_2711075
  have hstable : (prefixWord ++ tailWord_2711075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2711075).length < 2 ^ (prefixWord ++ tailWord_2711075).sum := by decide
  have hdescent : baseEnd_2711075 < baseStart_2711075 := by decide
  rcases family_descends (prefixWord ++ tailWord_2711075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2711095 : List Nat := [1, 1, 3, 1, 2, 6, 2, 7]
def baseStart_2711095 : Nat := 118140960795 + 2711095 * 2 ^ 59
def prefixEnd_2711095 : Nat := 4983230072969 + 3 ^ 40 * 2711095 * 2
def baseEnd_2711095 : Nat := 51559067963006502297941

theorem tailTrace_2711095 : CollatzResearch.WordTrace tailWord_2711095 prefixEnd_2711095 51559067963006502297941 := by
  unfold tailWord_2711095
  simp only [CollatzResearch.WordTrace]
  refine ⟨98881758113173308008350739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65921172075448872005567159 98881758113173308008350739)
  ·
    refine ⟨148322637169759962012526109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98881758113173308008350739 148322637169759962012526109)
    ·
      refine ⟨55620988938659985754697291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 148322637169759962012526109 55620988938659985754697291)
      ·
        refine ⟨83431483407989978632045937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55620988938659985754697291 83431483407989978632045937)
        ·
          refine ⟨62573612555992483974034453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83431483407989978632045937 62573612555992483974034453)
          ·
            refine ⟨2933138088562147686282865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 62573612555992483974034453 2933138088562147686282865)
            ·
              refine ⟨2199853566421610764712149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2933138088562147686282865 2199853566421610764712149)
              ·
                refine ⟨51559067963006502297941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2199853566421610764712149 51559067963006502297941)
                ·
                  rfl

theorem cell23_2711095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 2, 7].length) (baseStart_2711095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2711095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2711095 prefixEnd_2711095 := by exact prefixLift 2711095
  have htrace : WordTrace (prefixWord ++ tailWord_2711095) baseStart_2711095 baseEnd_2711095 := by
    simpa [prefixWord, tailWord_2711095, baseEnd_2711095] using wordTrace_append hprefix tailTrace_2711095
  have hstable : (prefixWord ++ tailWord_2711095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2711095).length < 2 ^ (prefixWord ++ tailWord_2711095).sum := by decide
  have hdescent : baseEnd_2711095 < baseStart_2711095 := by decide
  rcases family_descends (prefixWord ++ tailWord_2711095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2711105 : List Nat := [1, 2, 5, 1, 1, 1, 2, 1, 3, 3, 3]
def baseStart_2711105 : Nat := 118140960795 + 2711105 * 2 ^ 59
def prefixEnd_2711105 : Nat := 4983230072969 + 3 ^ 40 * 2711105 * 2
def baseEnd_2711105 : Nat := 1392099969807720522919361

theorem tailTrace_2711105 : CollatzResearch.WordTrace tailWord_2711105 prefixEnd_2711105 1392099969807720522919361 := by
  unfold tailWord_2711105
  simp only [CollatzResearch.WordTrace]
  refine ⟨98882122843137079716214769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65921415228758053144143179 98882122843137079716214769)
  ·
    refine ⟨74161592132352809787161077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98882122843137079716214769 74161592132352809787161077)
    ·
      refine ⟨6952649262408075917546351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 74161592132352809787161077 6952649262408075917546351)
      ·
        refine ⟨10428973893612113876319527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6952649262408075917546351 10428973893612113876319527)
        ·
          refine ⟨15643460840418170814479291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10428973893612113876319527 15643460840418170814479291)
          ·
            refine ⟨23465191260627256221718937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15643460840418170814479291 23465191260627256221718937)
            ·
              refine ⟨17598893445470442166289203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23465191260627256221718937 17598893445470442166289203)
              ·
                refine ⟨26398340168205663249433805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17598893445470442166289203 26398340168205663249433805)
                ·
                  refine ⟨9899377563077123718537677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26398340168205663249433805 9899377563077123718537677)
                  ·
                    refine ⟨3712266586153921394451629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9899377563077123718537677 3712266586153921394451629)
                    ·
                      refine ⟨1392099969807720522919361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3712266586153921394451629 1392099969807720522919361)
                      ·
                        rfl

theorem cell23_2711105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 1, 3, 3, 3].length) (baseStart_2711105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2711105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2711105 prefixEnd_2711105 := by exact prefixLift 2711105
  have htrace : WordTrace (prefixWord ++ tailWord_2711105) baseStart_2711105 baseEnd_2711105 := by
    simpa [prefixWord, tailWord_2711105, baseEnd_2711105] using wordTrace_append hprefix tailTrace_2711105
  have hstable : (prefixWord ++ tailWord_2711105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2711105).length < 2 ^ (prefixWord ++ tailWord_2711105).sum := by decide
  have hdescent : baseEnd_2711105 < baseStart_2711105 := by decide
  rcases family_descends (prefixWord ++ tailWord_2711105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2711115 : List Nat := [1, 1, 1, 1, 3, 1, 3, 2, 5, 3, 2]
def baseStart_2711115 : Nat := 118140960795 + 2711115 * 2 ^ 59
def prefixEnd_2711115 : Nat := 4983230072969 + 3 ^ 40 * 2711115 * 2
def baseEnd_2711115 : Nat := 1392105104614265483794315

theorem tailTrace_2711115 : CollatzResearch.WordTrace tailWord_2711115 prefixEnd_2711115 1392105104614265483794315 := by
  unfold tailWord_2711115
  simp only [CollatzResearch.WordTrace]
  refine ⟨98882487573100851424078799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65921658382067234282719199 98882487573100851424078799)
  ·
    refine ⟨148323731359651277136118199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98882487573100851424078799 148323731359651277136118199)
    ·
      refine ⟨222485597039476915704177299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148323731359651277136118199 222485597039476915704177299)
      ·
        refine ⟨333728395559215373556265949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222485597039476915704177299 333728395559215373556265949)
        ·
          refine ⟨125148148334705765083599731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 333728395559215373556265949 125148148334705765083599731)
          ·
            refine ⟨187722222502058647625399597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125148148334705765083599731 187722222502058647625399597)
            ·
              refine ⟨70395833438271992859524849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 187722222502058647625399597 70395833438271992859524849)
              ·
                refine ⟨52796875078703994644643637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70395833438271992859524849 52796875078703994644643637)
                ·
                  refine ⟨4949707038628499497935341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 52796875078703994644643637 4949707038628499497935341)
                  ·
                    refine ⟨1856140139485687311725753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4949707038628499497935341 1856140139485687311725753)
                    ·
                      refine ⟨1392105104614265483794315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1856140139485687311725753 1392105104614265483794315)
                      ·
                        rfl

theorem cell23_2711115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 5, 3, 2].length) (baseStart_2711115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2711115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2711115 prefixEnd_2711115 := by exact prefixLift 2711115
  have htrace : WordTrace (prefixWord ++ tailWord_2711115) baseStart_2711115 baseEnd_2711115 := by
    simpa [prefixWord, tailWord_2711115, baseEnd_2711115] using wordTrace_append hprefix tailTrace_2711115
  have hstable : (prefixWord ++ tailWord_2711115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2711115).length < 2 ^ (prefixWord ++ tailWord_2711115).sum := by decide
  have hdescent : baseEnd_2711115 < baseStart_2711115 := by decide
  rcases family_descends (prefixWord ++ tailWord_2711115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2711118 : List Nat := [4, 1, 1, 1, 1, 2, 1, 1, 4, 2, 5]
def baseStart_2711118 : Nat := 118140960795 + 2711118 * 2 ^ 59
def prefixEnd_2711118 : Nat := 4983230072969 + 3 ^ 40 * 2711118 * 2
def baseEnd_2711118 : Nat := 1392106645056228972056801

theorem tailTrace_2711118 : CollatzResearch.WordTrace tailWord_2711118 prefixEnd_2711118 1392106645056228972056801 := by
  unfold tailWord_2711118
  simp only [CollatzResearch.WordTrace]
  refine ⟨12360324624011247867054751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65921731328059988624292005 12360324624011247867054751)
  ·
    refine ⟨18540486936016871800582127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12360324624011247867054751 18540486936016871800582127)
    ·
      refine ⟨27810730404025307700873191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18540486936016871800582127 27810730404025307700873191)
      ·
        refine ⟨41716095606037961551309787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27810730404025307700873191 41716095606037961551309787)
        ·
          refine ⟨62574143409056942326964681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41716095606037961551309787 62574143409056942326964681)
          ·
            refine ⟨46930607556792706745223511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62574143409056942326964681 46930607556792706745223511)
            ·
              refine ⟨70395911335189060117835267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46930607556792706745223511 70395911335189060117835267)
              ·
                refine ⟨105593867002783590176752901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70395911335189060117835267 105593867002783590176752901)
                ·
                  refine ⟨19798850063021923158141169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 105593867002783590176752901 19798850063021923158141169)
                  ·
                    refine ⟨14849137547266442368605877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19798850063021923158141169 14849137547266442368605877)
                    ·
                      refine ⟨1392106645056228972056801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14849137547266442368605877 1392106645056228972056801)
                      ·
                        rfl

theorem cell23_2711118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 1, 4, 2, 5].length) (baseStart_2711118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2711118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2711118 prefixEnd_2711118 := by exact prefixLift 2711118
  have htrace : WordTrace (prefixWord ++ tailWord_2711118) baseStart_2711118 baseEnd_2711118 := by
    simpa [prefixWord, tailWord_2711118, baseEnd_2711118] using wordTrace_append hprefix tailTrace_2711118
  have hstable : (prefixWord ++ tailWord_2711118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2711118).length < 2 ^ (prefixWord ++ tailWord_2711118).sum := by decide
  have hdescent : baseEnd_2711118 < baseStart_2711118 := by decide
  rcases family_descends (prefixWord ++ tailWord_2711118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2711122 : List Nat := [3, 2, 2, 1, 2, 2, 2, 1, 4, 1, 3]
def baseStart_2711122 : Nat := 118140960795 + 2711122 * 2 ^ 59
def prefixEnd_2711122 : Nat := 4983230072969 + 3 ^ 40 * 2711122 * 2
def baseEnd_2711122 : Nat := 1392108698978846956406783

theorem tailTrace_2711122 : CollatzResearch.WordTrace tailWord_2711122 prefixEnd_2711122 1392108698978846956406783 := by
  unfold tailWord_2711122
  simp only [CollatzResearch.WordTrace]
  refine ⟨24720685721018872904895905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65921828589383661079722413 24720685721018872904895905)
  ·
    refine ⟨18540514290764154678671929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24720685721018872904895905 18540514290764154678671929)
    ·
      refine ⟨13905385718073116009003947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18540514290764154678671929 13905385718073116009003947)
      ·
        refine ⟨20858078577109674013505921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13905385718073116009003947 20858078577109674013505921)
        ·
          refine ⟨15643558932832255510129441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20858078577109674013505921 15643558932832255510129441)
          ·
            refine ⟨11732669199624191632597081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15643558932832255510129441 11732669199624191632597081)
            ·
              refine ⟨8799501899718143724447811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11732669199624191632597081 8799501899718143724447811)
              ·
                refine ⟨13199252849577215586671717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8799501899718143724447811 13199252849577215586671717)
                ·
                  refine ⟨2474859909295727922500947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13199252849577215586671717 2474859909295727922500947)
                  ·
                    refine ⟨3712289863943591883751421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2474859909295727922500947 3712289863943591883751421)
                    ·
                      refine ⟨1392108698978846956406783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3712289863943591883751421 1392108698978846956406783)
                      ·
                        rfl

theorem cell23_2711122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 1, 4, 1, 3].length) (baseStart_2711122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2711122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2711122 prefixEnd_2711122 := by exact prefixLift 2711122
  have htrace : WordTrace (prefixWord ++ tailWord_2711122) baseStart_2711122 baseEnd_2711122 := by
    simpa [prefixWord, tailWord_2711122, baseEnd_2711122] using wordTrace_append hprefix tailTrace_2711122
  have hstable : (prefixWord ++ tailWord_2711122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2711122).length < 2 ^ (prefixWord ++ tailWord_2711122).sum := by decide
  have hdescent : baseEnd_2711122 < baseStart_2711122 := by decide
  rcases family_descends (prefixWord ++ tailWord_2711122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2711128 : List Nat := [2, 1, 2, 2, 1, 2, 1, 3, 2, 3, 4]
def baseStart_2711128 : Nat := 118140960795 + 2711128 * 2 ^ 59
def prefixEnd_2711128 : Nat := 4983230072969 + 3 ^ 40 * 2711128 * 2
def baseEnd_2711128 : Nat := 1392111779862773932931755

theorem tailTrace_2711128 : CollatzResearch.WordTrace tailWord_2711128 prefixEnd_2711128 1392111779862773932931755 := by
  unfold tailWord_2711128
  simp only [CollatzResearch.WordTrace]
  refine ⟨49441480861026877322151019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65921974481369169762868025 49441480861026877322151019)
  ·
    refine ⟨74162221291540315983226529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49441480861026877322151019 74162221291540315983226529)
    ·
      refine ⟨55621665968655236987419897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74162221291540315983226529 55621665968655236987419897)
      ·
        refine ⟨41716249476491427740564923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55621665968655236987419897 41716249476491427740564923)
        ·
          refine ⟨62574374214737141610847385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41716249476491427740564923 62574374214737141610847385)
          ·
            refine ⟨46930780661052856208135539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62574374214737141610847385 46930780661052856208135539)
            ·
              refine ⟨70396170991579284312203309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46930780661052856208135539 70396170991579284312203309)
              ·
                refine ⟨26398564121842231617076241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 70396170991579284312203309 26398564121842231617076241)
                ·
                  refine ⟨19798923091381673712807181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26398564121842231617076241 19798923091381673712807181)
                  ·
                    refine ⟨7424596159268127642302693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19798923091381673712807181 7424596159268127642302693)
                    ·
                      refine ⟨1392111779862773932931755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7424596159268127642302693 1392111779862773932931755)
                      ·
                        rfl

theorem cell23_2711128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 3, 2, 3, 4].length) (baseStart_2711128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2711128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2711128 prefixEnd_2711128 := by exact prefixLift 2711128
  have htrace : WordTrace (prefixWord ++ tailWord_2711128) baseStart_2711128 baseEnd_2711128 := by
    simpa [prefixWord, tailWord_2711128, baseEnd_2711128] using wordTrace_append hprefix tailTrace_2711128
  have hstable : (prefixWord ++ tailWord_2711128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2711128).length < 2 ^ (prefixWord ++ tailWord_2711128).sum := by decide
  have hdescent : baseEnd_2711128 < baseStart_2711128 := by decide
  rcases family_descends (prefixWord ++ tailWord_2711128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2711133 : List Nat := [1, 4, 4, 2, 1, 2, 2, 1, 2, 4]
def baseStart_2711133 : Nat := 118140960795 + 2711133 * 2 ^ 59
def prefixEnd_2711133 : Nat := 4983230072969 + 3 ^ 40 * 2711133 * 2
def baseEnd_2711133 : Nat := 464038115755348804456411

theorem tailTrace_2711133 : CollatzResearch.WordTrace tailWord_2711133 prefixEnd_2711133 464038115755348804456411 := by
  unfold tailWord_2711133
  simp only [CollatzResearch.WordTrace]
  refine ⟨98883144087035640498234053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65922096058023760332156035 98883144087035640498234053)
  ·
    refine ⟨18540589516319182593418885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 98883144087035640498234053 18540589516319182593418885)
    ·
      refine ⟨3476360534309846736266041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18540589516319182593418885 3476360534309846736266041)
      ·
        refine ⟨2607270400732385052199531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3476360534309846736266041 2607270400732385052199531)
        ·
          refine ⟨3910905601098577578299297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2607270400732385052199531 3910905601098577578299297)
          ·
            refine ⟨2933179200823933183724473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3910905601098577578299297 2933179200823933183724473)
            ·
              refine ⟨2199884400617949887793355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2933179200823933183724473 2199884400617949887793355)
              ·
                refine ⟨3299826600926924831690033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2199884400617949887793355 3299826600926924831690033)
                ·
                  refine ⟨2474869950695193623767525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3299826600926924831690033 2474869950695193623767525)
                  ·
                    refine ⟨464038115755348804456411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2474869950695193623767525 464038115755348804456411)
                    ·
                      rfl

theorem cell23_2711133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 2, 1, 2, 4].length) (baseStart_2711133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2711133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2711133 prefixEnd_2711133 := by exact prefixLift 2711133
  have htrace : WordTrace (prefixWord ++ tailWord_2711133) baseStart_2711133 baseEnd_2711133 := by
    simpa [prefixWord, tailWord_2711133, baseEnd_2711133] using wordTrace_append hprefix tailTrace_2711133
  have hstable : (prefixWord ++ tailWord_2711133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2711133).length < 2 ^ (prefixWord ++ tailWord_2711133).sum := by decide
  have hdescent : baseEnd_2711133 < baseStart_2711133 := by decide
  rcases family_descends (prefixWord ++ tailWord_2711133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2711139 : List Nat := [1, 1, 1, 5, 1, 3, 4, 1, 2, 1, 3]
def baseStart_2711139 : Nat := 118140960795 + 2711139 * 2 ^ 59
def prefixEnd_2711139 : Nat := 4983230072969 + 3 ^ 40 * 2711139 * 2
def baseEnd_2711139 : Nat := 1392117428149973389894205

theorem tailTrace_2711139 : CollatzResearch.WordTrace tailWord_2711139 prefixEnd_2711139 1392117428149973389894205 := by
  unfold tailWord_2711139
  simp only [CollatzResearch.WordTrace]
  refine ⟨98883362925013903522952471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65922241950009269015301647 98883362925013903522952471)
  ·
    refine ⟨148325044387520855284428707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98883362925013903522952471 148325044387520855284428707)
    ·
      refine ⟨222487566581281282926643061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148325044387520855284428707 222487566581281282926643061)
      ·
        refine ⟨20858209366995120274372787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 222487566581281282926643061 20858209366995120274372787)
        ·
          refine ⟨31287314050492680411559181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20858209366995120274372787 31287314050492680411559181)
          ·
            refine ⟨11732742768934755154334693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31287314050492680411559181 11732742768934755154334693)
            ·
              refine ⟨2199889269175266591437755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11732742768934755154334693 2199889269175266591437755)
              ·
                refine ⟨3299833903762899887156633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2199889269175266591437755 3299833903762899887156633)
                ·
                  refine ⟨2474875427822174915367475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3299833903762899887156633 2474875427822174915367475)
                  ·
                    refine ⟨3712313141733262373051213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2474875427822174915367475 3712313141733262373051213)
                    ·
                      refine ⟨1392117428149973389894205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3712313141733262373051213 1392117428149973389894205)
                      ·
                        rfl

theorem cell23_2711139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 4, 1, 2, 1, 3].length) (baseStart_2711139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2711139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2711139 prefixEnd_2711139 := by exact prefixLift 2711139
  have htrace : WordTrace (prefixWord ++ tailWord_2711139) baseStart_2711139 baseEnd_2711139 := by
    simpa [prefixWord, tailWord_2711139, baseEnd_2711139] using wordTrace_append hprefix tailTrace_2711139
  have hstable : (prefixWord ++ tailWord_2711139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2711139).length < 2 ^ (prefixWord ++ tailWord_2711139).sum := by decide
  have hdescent : baseEnd_2711139 < baseStart_2711139 := by decide
  rcases family_descends (prefixWord ++ tailWord_2711139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2711149 : List Nat := [1, 5, 1, 1, 4, 1, 1, 1, 3, 3, 2]
def baseStart_2711149 : Nat := 118140960795 + 2711149 * 2 ^ 59
def prefixEnd_2711149 : Nat := 4983230072969 + 3 ^ 40 * 2711149 * 2
def baseEnd_2711149 : Nat := 1392122562956518350769159

theorem tailTrace_2711149 : CollatzResearch.WordTrace tailWord_2711149 prefixEnd_2711149 1392122562956518350769159 := by
  unfold tailWord_2711149
  simp only [CollatzResearch.WordTrace]
  refine ⟨98883727654977675230816501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65922485103318450153877667 98883727654977675230816501)
  ·
    refine ⟨9270349467654157052889047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 98883727654977675230816501 9270349467654157052889047)
    ·
      refine ⟨13905524201481235579333571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9270349467654157052889047 13905524201481235579333571)
      ·
        refine ⟨20858286302221853369000357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13905524201481235579333571 20858286302221853369000357)
        ·
          refine ⟨3910928681666597506687567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20858286302221853369000357 3910928681666597506687567)
          ·
            refine ⟨5866393022499896260031351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3910928681666597506687567 5866393022499896260031351)
            ·
              refine ⟨8799589533749844390047027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5866393022499896260031351 8799589533749844390047027)
              ·
                refine ⟨13199384300624766585070541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8799589533749844390047027 13199384300624766585070541)
                ·
                  refine ⟨4949769112734287469401453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13199384300624766585070541 4949769112734287469401453)
                  ·
                    refine ⟨1856163417275357801025545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4949769112734287469401453 1856163417275357801025545)
                    ·
                      refine ⟨1392122562956518350769159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1856163417275357801025545 1392122562956518350769159)
                      ·
                        rfl

theorem cell23_2711149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 1, 3, 3, 2].length) (baseStart_2711149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2711149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2711149 prefixEnd_2711149 := by exact prefixLift 2711149
  have htrace : WordTrace (prefixWord ++ tailWord_2711149) baseStart_2711149 baseEnd_2711149 := by
    simpa [prefixWord, tailWord_2711149, baseEnd_2711149] using wordTrace_append hprefix tailTrace_2711149
  have hstable : (prefixWord ++ tailWord_2711149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2711149).length < 2 ^ (prefixWord ++ tailWord_2711149).sum := by decide
  have hdescent : baseEnd_2711149 < baseStart_2711149 := by decide
  rcases family_descends (prefixWord ++ tailWord_2711149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2711162 : List Nat := [3, 1, 1, 1, 1, 1, 1, 6, 4, 2, 2]
def baseStart_2711162 : Nat := 118140960795 + 2711162 * 2 ^ 59
def prefixEnd_2711162 : Nat := 4983230072969 + 3 ^ 40 * 2711162 * 2
def baseEnd_2711162 : Nat := 1392129238205026799906599

theorem tailTrace_2711162 : CollatzResearch.WordTrace tailWord_2711162 prefixEnd_2711162 1392129238205026799906599 := by
  unfold tailWord_2711162
  simp only [CollatzResearch.WordTrace]
  refine ⟨24721050450982644612759935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65922801202620385634026493 24721050450982644612759935)
  ·
    refine ⟨37081575676473966919139903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24721050450982644612759935 37081575676473966919139903)
    ·
      refine ⟨55622363514710950378709855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37081575676473966919139903 55622363514710950378709855)
      ·
        refine ⟨83433545272066425568064783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55622363514710950378709855 83433545272066425568064783)
        ·
          refine ⟨125150317908099638352097175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83433545272066425568064783 125150317908099638352097175)
          ·
            refine ⟨187725476862149457528145763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125150317908099638352097175 187725476862149457528145763)
            ·
              refine ⟨281588215293224186292218645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 187725476862149457528145763 281588215293224186292218645)
              ·
                refine ⟨13199447591869883732447749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 281588215293224186292218645 13199447591869883732447749)
                ·
                  refine ⟨2474896423475603199833953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13199447591869883732447749 2474896423475603199833953)
                  ·
                    refine ⟨1856172317606702399875465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2474896423475603199833953 1856172317606702399875465)
                    ·
                      refine ⟨1392129238205026799906599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1856172317606702399875465 1392129238205026799906599)
                      ·
                        rfl

theorem cell23_2711162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 6, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 6, 4, 2, 2].length) (baseStart_2711162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2711162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2711162 prefixEnd_2711162 := by exact prefixLift 2711162
  have htrace : WordTrace (prefixWord ++ tailWord_2711162) baseStart_2711162 baseEnd_2711162 := by
    simpa [prefixWord, tailWord_2711162, baseEnd_2711162] using wordTrace_append hprefix tailTrace_2711162
  have hstable : (prefixWord ++ tailWord_2711162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2711162).length < 2 ^ (prefixWord ++ tailWord_2711162).sum := by decide
  have hdescent : baseEnd_2711162 < baseStart_2711162 := by decide
  rcases family_descends (prefixWord ++ tailWord_2711162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2711165 : List Nat := [1, 4, 1, 1, 4, 1, 2, 1, 2, 1, 5]
def baseStart_2711165 : Nat := 118140960795 + 2711165 * 2 ^ 59
def prefixEnd_2711165 : Nat := 4983230072969 + 3 ^ 40 * 2711165 * 2
def baseEnd_2711165 : Nat := 1392130778646990288169085

theorem tailTrace_2711165 : CollatzResearch.WordTrace tailWord_2711165 prefixEnd_2711165 1392130778646990288169085 := by
  unfold tailWord_2711165
  simp only [CollatzResearch.WordTrace]
  refine ⟨98884311222919709963398949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65922874148613139975599299 98884311222919709963398949)
  ·
    refine ⟨18540808354297445618137303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 98884311222919709963398949 18540808354297445618137303)
    ·
      refine ⟨27811212531446168427205955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18540808354297445618137303 27811212531446168427205955)
      ·
        refine ⟨41716818797169252640808933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27811212531446168427205955 41716818797169252640808933)
        ·
          refine ⟨7821903524469234870151675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41716818797169252640808933 7821903524469234870151675)
          ·
            refine ⟨11732855286703852305227513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7821903524469234870151675 11732855286703852305227513)
            ·
              refine ⟨8799641465027889228920635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11732855286703852305227513 8799641465027889228920635)
              ·
                refine ⟨13199462197541833843380953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8799641465027889228920635 13199462197541833843380953)
                ·
                  refine ⟨9899596648156375382535715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13199462197541833843380953 9899596648156375382535715)
                  ·
                    refine ⟨14849394972234563073803573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9899596648156375382535715 14849394972234563073803573)
                    ·
                      refine ⟨1392130778646990288169085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14849394972234563073803573 1392130778646990288169085)
                      ·
                        rfl

theorem cell23_2711165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 1, 2, 1, 5].length) (baseStart_2711165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2711165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2711165 prefixEnd_2711165 := by exact prefixLift 2711165
  have htrace : WordTrace (prefixWord ++ tailWord_2711165) baseStart_2711165 baseEnd_2711165 := by
    simpa [prefixWord, tailWord_2711165, baseEnd_2711165] using wordTrace_append hprefix tailTrace_2711165
  have hstable : (prefixWord ++ tailWord_2711165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2711165).length < 2 ^ (prefixWord ++ tailWord_2711165).sum := by decide
  have hdescent : baseEnd_2711165 < baseStart_2711165 := by decide
  rcases family_descends (prefixWord ++ tailWord_2711165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2711179 : List Nat := [1, 1, 1, 1, 4, 1, 6, 2, 2, 2, 2]
def baseStart_2711179 : Nat := 118140960795 + 2711179 * 2 ^ 59
def prefixEnd_2711179 : Nat := 4983230072969 + 3 ^ 40 * 2711179 * 2
def baseEnd_2711179 : Nat := 1392137967376153233394021

theorem tailTrace_2711179 : CollatzResearch.WordTrace tailWord_2711179 prefixEnd_2711179 1392137967376153233394021 := by
  unfold tailWord_2711179
  simp only [CollatzResearch.WordTrace]
  refine ⟨98884821844868990354408591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65923214563245993569605727 98884821844868990354408591)
  ·
    refine ⟨148327232767303485531612887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98884821844868990354408591 148327232767303485531612887)
    ·
      refine ⟨222490849150955228297419331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148327232767303485531612887 222490849150955228297419331)
      ·
        refine ⟨333736273726432842446128997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222490849150955228297419331 333736273726432842446128997)
        ·
          refine ⟨62575551323706157958649187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 333736273726432842446128997 62575551323706157958649187)
          ·
            refine ⟨93863326985559236937973781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62575551323706157958649187 93863326985559236937973781)
            ·
              refine ⟨4399843452448089231467521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 93863326985559236937973781 4399843452448089231467521)
              ·
                refine ⟨3299882589336066923600641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4399843452448089231467521 3299882589336066923600641)
                ·
                  refine ⟨2474911942002050192700481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3299882589336066923600641 2474911942002050192700481)
                  ·
                    refine ⟨1856183956501537644525361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2474911942002050192700481 1856183956501537644525361)
                    ·
                      refine ⟨1392137967376153233394021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1856183956501537644525361 1392137967376153233394021)
                      ·
                        rfl

theorem cell23_2711179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 6, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 6, 2, 2, 2, 2].length) (baseStart_2711179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2711179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2711179 prefixEnd_2711179 := by exact prefixLift 2711179
  have htrace : WordTrace (prefixWord ++ tailWord_2711179) baseStart_2711179 baseEnd_2711179 := by
    simpa [prefixWord, tailWord_2711179, baseEnd_2711179] using wordTrace_append hprefix tailTrace_2711179
  have hstable : (prefixWord ++ tailWord_2711179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2711179).length < 2 ^ (prefixWord ++ tailWord_2711179).sum := by decide
  have hdescent : baseEnd_2711179 < baseStart_2711179 := by decide
  rcases family_descends (prefixWord ++ tailWord_2711179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2711252 : List Nat := [2, 4, 1, 3, 1, 1, 1, 2, 1, 3, 4]
def baseStart_2711252 : Nat := 118140960795 + 2711252 * 2 ^ 59
def prefixEnd_2711252 : Nat := 4983230072969 + 3 ^ 40 * 2711252 * 2
def baseEnd_2711252 : Nat := 1392175451463931447781185

theorem tailTrace_2711252 : CollatzResearch.WordTrace tailWord_2711252 prefixEnd_2711252 1392175451463931447781185 := by
  unfold tailWord_2711252
  simp only [CollatzResearch.WordTrace]
  refine ⟨49443742186802261910908005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65924989582403015881210673 49443742186802261910908005)
  ·
    refine ⟨9270701660025424108295251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49443742186802261910908005 9270701660025424108295251)
    ·
      refine ⟨13906052490038136162442877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9270701660025424108295251 13906052490038136162442877)
      ·
        refine ⟨5214769683764301060916079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13906052490038136162442877 5214769683764301060916079)
        ·
          refine ⟨7822154525646451591374119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5214769683764301060916079 7822154525646451591374119)
          ·
            refine ⟨11733231788469677387061179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7822154525646451591374119 11733231788469677387061179)
            ·
              refine ⟨17599847682704516080591769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11733231788469677387061179 17599847682704516080591769)
              ·
                refine ⟨13199885762028387060443827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17599847682704516080591769 13199885762028387060443827)
                ·
                  refine ⟨19799828643042580590665741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13199885762028387060443827 19799828643042580590665741)
                  ·
                    refine ⟨7424935741140967721499653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19799828643042580590665741 7424935741140967721499653)
                    ·
                      refine ⟨1392175451463931447781185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7424935741140967721499653 1392175451463931447781185)
                      ·
                        rfl

theorem cell23_2711252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_2711252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2711252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2711252 prefixEnd_2711252 := by exact prefixLift 2711252
  have htrace : WordTrace (prefixWord ++ tailWord_2711252) baseStart_2711252 baseEnd_2711252 := by
    simpa [prefixWord, tailWord_2711252, baseEnd_2711252] using wordTrace_append hprefix tailTrace_2711252
  have hstable : (prefixWord ++ tailWord_2711252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2711252).length < 2 ^ (prefixWord ++ tailWord_2711252).sum := by decide
  have hdescent : baseEnd_2711252 < baseStart_2711252 := by decide
  rcases family_descends (prefixWord ++ tailWord_2711252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2711255 : List Nat := [1, 1, 3, 2, 1, 3, 1, 1, 3, 4, 3]
def baseStart_2711255 : Nat := 118140960795 + 2711255 * 2 ^ 59
def prefixEnd_2711255 : Nat := 4983230072969 + 3 ^ 40 * 2711255 * 2
def baseEnd_2711255 : Nat := 1392176991905894936043671

theorem tailTrace_2711255 : CollatzResearch.WordTrace tailWord_2711255 prefixEnd_2711255 1392176991905894936043671 := by
  unfold tailWord_2711255
  simp only [CollatzResearch.WordTrace]
  refine ⟨98887593792593655334175219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65925062528395770222783479 98887593792593655334175219)
  ·
    refine ⟨148331390688890483001262829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98887593792593655334175219 148331390688890483001262829)
    ·
      refine ⟨55624271508333931125473561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 148331390688890483001262829 55624271508333931125473561)
      ·
        refine ⟨41718203631250448344105171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55624271508333931125473561 41718203631250448344105171)
        ·
          refine ⟨62577305446875672516157757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41718203631250448344105171 62577305446875672516157757)
          ·
            refine ⟨23466489542578377193559159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62577305446875672516157757 23466489542578377193559159)
            ·
              refine ⟨35199734313867565790338739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23466489542578377193559159 35199734313867565790338739)
              ·
                refine ⟨52799601470801348685508109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35199734313867565790338739 52799601470801348685508109)
                ·
                  refine ⟨19799850551550505757065541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52799601470801348685508109 19799850551550505757065541)
                  ·
                    refine ⟨3712471978415719829449789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19799850551550505757065541 3712471978415719829449789)
                    ·
                      refine ⟨1392176991905894936043671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3712471978415719829449789 1392176991905894936043671)
                      ·
                        rfl

theorem cell23_2711255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 1, 3, 4, 3].length) (baseStart_2711255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2711255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2711255 prefixEnd_2711255 := by exact prefixLift 2711255
  have htrace : WordTrace (prefixWord ++ tailWord_2711255) baseStart_2711255 baseEnd_2711255 := by
    simpa [prefixWord, tailWord_2711255, baseEnd_2711255] using wordTrace_append hprefix tailTrace_2711255
  have hstable : (prefixWord ++ tailWord_2711255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2711255).length < 2 ^ (prefixWord ++ tailWord_2711255).sum := by decide
  have hdescent : baseEnd_2711255 < baseStart_2711255 := by decide
  rcases family_descends (prefixWord ++ tailWord_2711255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2711272 : List Nat := [2, 1, 4, 1, 3, 1, 2, 1, 1, 4, 3]
def baseStart_2711272 : Nat := 118140960795 + 2711272 * 2 ^ 59
def prefixEnd_2711272 : Nat := 4983230072969 + 3 ^ 40 * 2711272 * 2
def baseEnd_2711272 : Nat := 1392185721077021369531093

theorem tailTrace_2711272 : CollatzResearch.WordTrace tailWord_2711272 prefixEnd_2711272 1392185721077021369531093 := by
  unfold tailWord_2711272
  simp only [CollatzResearch.WordTrace]
  refine ⟨49444106916766033618772035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65925475889021378158362713 49444106916766033618772035)
  ·
    refine ⟨74166160375149050428158053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49444106916766033618772035 74166160375149050428158053)
    ·
      refine ⟨13906155070340446955279635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 74166160375149050428158053 13906155070340446955279635)
      ·
        refine ⟨20859232605510670432919453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13906155070340446955279635 20859232605510670432919453)
        ·
          refine ⟨7822212227066501412344795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20859232605510670432919453 7822212227066501412344795)
          ·
            refine ⟨11733318340599752118517193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7822212227066501412344795 11733318340599752118517193)
            ·
              refine ⟨8799988755449814088887895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11733318340599752118517193 8799988755449814088887895)
              ·
                refine ⟨13199983133174721133331843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8799988755449814088887895 13199983133174721133331843)
                ·
                  refine ⟨19799974699762081699997765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13199983133174721133331843 19799974699762081699997765)
                  ·
                    refine ⟨3712495256205390318749581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19799974699762081699997765 3712495256205390318749581)
                    ·
                      refine ⟨1392185721077021369531093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3712495256205390318749581 1392185721077021369531093)
                      ·
                        rfl

theorem cell23_2711272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 1, 1, 4, 3].length) (baseStart_2711272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2711272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2711272 prefixEnd_2711272 := by exact prefixLift 2711272
  have htrace : WordTrace (prefixWord ++ tailWord_2711272) baseStart_2711272 baseEnd_2711272 := by
    simpa [prefixWord, tailWord_2711272, baseEnd_2711272] using wordTrace_append hprefix tailTrace_2711272
  have hstable : (prefixWord ++ tailWord_2711272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2711272).length < 2 ^ (prefixWord ++ tailWord_2711272).sum := by decide
  have hdescent : baseEnd_2711272 < baseStart_2711272 := by decide
  rcases family_descends (prefixWord ++ tailWord_2711272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2711305 : List Nat := [1, 2, 1, 1, 3, 2, 1, 4, 3, 5]
def baseStart_2711305 : Nat := 118140960795 + 2711305 * 2 ^ 59
def prefixEnd_2711305 : Nat := 4983230072969 + 3 ^ 40 * 2711305 * 2
def baseEnd_2711305 : Nat := 464067555312873246806147

theorem tailTrace_2711305 : CollatzResearch.WordTrace tailWord_2711305 prefixEnd_2711305 464067555312873246806147 := by
  unfold tailWord_2711305
  simp only [CollatzResearch.WordTrace]
  refine ⟨98889417442412513873495369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65926278294941675915663579 98889417442412513873495369)
  ·
    refine ⟨74167063081809385405121527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98889417442412513873495369 74167063081809385405121527)
    ·
      refine ⟨111250594622714078107682291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74167063081809385405121527 111250594622714078107682291)
      ·
        refine ⟨166875891934071117161523437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111250594622714078107682291 166875891934071117161523437)
        ·
          refine ⟨62578459475276668935571289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 166875891934071117161523437 62578459475276668935571289)
          ·
            refine ⟨46933844606457501701678467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62578459475276668935571289 46933844606457501701678467)
            ·
              refine ⟨70400766909686252552517701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46933844606457501701678467 70400766909686252552517701)
              ·
                refine ⟨13200143795566172353597069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 70400766909686252552517701 13200143795566172353597069)
                ·
                  refine ⟨4950053923337314632598901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13200143795566172353597069 4950053923337314632598901)
                  ·
                    refine ⟨464067555312873246806147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4950053923337314632598901 464067555312873246806147)
                    ·
                      rfl

theorem cell23_2711305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 4, 3, 5].length) (baseStart_2711305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2711305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2711305 prefixEnd_2711305 := by exact prefixLift 2711305
  have htrace : WordTrace (prefixWord ++ tailWord_2711305) baseStart_2711305 baseEnd_2711305 := by
    simpa [prefixWord, tailWord_2711305, baseEnd_2711305] using wordTrace_append hprefix tailTrace_2711305
  have hstable : (prefixWord ++ tailWord_2711305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2711305).length < 2 ^ (prefixWord ++ tailWord_2711305).sum := by decide
  have hdescent : baseEnd_2711305 < baseStart_2711305 := by decide
  rcases family_descends (prefixWord ++ tailWord_2711305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2711322 : List Nat := [3, 1, 1, 3, 2, 3, 1, 1, 3, 5]
def baseStart_2711322 : Nat := 118140960795 + 2711322 * 2 ^ 59
def prefixEnd_2711322 : Nat := 4983230072969 + 3 ^ 40 * 2711322 * 2
def baseEnd_2711322 : Nat := 464070465036582057968621

theorem tailTrace_2711322 : CollatzResearch.WordTrace tailWord_2711322 prefixEnd_2711322 464070465036582057968621 := by
  unfold tailWord_2711322
  simp only [CollatzResearch.WordTrace]
  refine ⟨24722509370837731444216055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65926691655567283851242813 24722509370837731444216055)
  ·
    refine ⟨37083764056256597166324083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24722509370837731444216055 37083764056256597166324083)
    ·
      refine ⟨55625646084384895749486125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37083764056256597166324083 55625646084384895749486125)
      ·
        refine ⟨20859617281644335906057297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55625646084384895749486125 20859617281644335906057297)
        ·
          refine ⟨15644712961233251929542973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20859617281644335906057297 15644712961233251929542973)
          ·
            refine ⟨5866767360462469473578615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15644712961233251929542973 5866767360462469473578615)
            ·
              refine ⟨8800151040693704210367923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5866767360462469473578615 8800151040693704210367923)
              ·
                refine ⟨13200226561040556315551885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8800151040693704210367923 13200226561040556315551885)
                ·
                  refine ⟨4950084960390208618331957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13200226561040556315551885 4950084960390208618331957)
                  ·
                    refine ⟨464070465036582057968621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4950084960390208618331957 464070465036582057968621)
                    ·
                      rfl

theorem cell23_2711322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 1, 3, 5].length) (baseStart_2711322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2711322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2711322 prefixEnd_2711322 := by exact prefixLift 2711322
  have htrace : WordTrace (prefixWord ++ tailWord_2711322) baseStart_2711322 baseEnd_2711322 := by
    simpa [prefixWord, tailWord_2711322, baseEnd_2711322] using wordTrace_append hprefix tailTrace_2711322
  have hstable : (prefixWord ++ tailWord_2711322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2711322).length < 2 ^ (prefixWord ++ tailWord_2711322).sum := by decide
  have hdescent : baseEnd_2711322 < baseStart_2711322 := by decide
  rcases family_descends (prefixWord ++ tailWord_2711322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2711329 : List Nat := [1, 2, 3, 2, 1, 3, 1, 3, 2, 3, 2]
def baseStart_2711329 : Nat := 118140960795 + 2711329 * 2 ^ 59
def prefixEnd_2711329 : Nat := 4983230072969 + 3 ^ 40 * 2711329 * 2
def baseEnd_2711329 : Nat := 1392214989474327646518331

theorem tailTrace_2711329 : CollatzResearch.WordTrace tailWord_2711329 prefixEnd_2711329 1392214989474327646518331 := by
  unfold tailWord_2711329
  simp only [CollatzResearch.WordTrace]
  refine ⟨98890292794325565972369041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65926861862883710648246027 98890292794325565972369041)
  ·
    refine ⟨74167719595744174479276781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98890292794325565972369041 74167719595744174479276781)
    ·
      refine ⟨27812894848404065429728793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74167719595744174479276781 27812894848404065429728793)
      ·
        refine ⟨20859671136303049072296595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27812894848404065429728793 20859671136303049072296595)
        ·
          refine ⟨31289506704454573608444893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20859671136303049072296595 31289506704454573608444893)
          ·
            refine ⟨11733565014170465103166835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31289506704454573608444893 11733565014170465103166835)
            ·
              refine ⟨17600347521255697654750253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11733565014170465103166835 17600347521255697654750253)
              ·
                refine ⟨6600130320470886620531345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17600347521255697654750253 6600130320470886620531345)
                ·
                  refine ⟨4950097740353164965398509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6600130320470886620531345 4950097740353164965398509)
                  ·
                    refine ⟨1856286652632436862024441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4950097740353164965398509 1856286652632436862024441)
                    ·
                      refine ⟨1392214989474327646518331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1856286652632436862024441 1392214989474327646518331)
                      ·
                        rfl

theorem cell23_2711329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 3, 2, 3, 2].length) (baseStart_2711329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2711329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2711329 prefixEnd_2711329 := by exact prefixLift 2711329
  have htrace : WordTrace (prefixWord ++ tailWord_2711329) baseStart_2711329 baseEnd_2711329 := by
    simpa [prefixWord, tailWord_2711329, baseEnd_2711329] using wordTrace_append hprefix tailTrace_2711329
  have hstable : (prefixWord ++ tailWord_2711329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2711329).length < 2 ^ (prefixWord ++ tailWord_2711329).sum := by decide
  have hdescent : baseEnd_2711329 < baseStart_2711329 := by decide
  rcases family_descends (prefixWord ++ tailWord_2711329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2711393 : List Nat := [1, 2, 3, 1, 1, 1, 6, 3, 1, 2, 2]
def baseStart_2711393 : Nat := 118140960795 + 2711393 * 2 ^ 59
def prefixEnd_2711393 : Nat := 4983230072969 + 3 ^ 40 * 2711393 * 2
def baseEnd_2711393 : Nat := 1392247852236215396118037

theorem tailTrace_2711393 : CollatzResearch.WordTrace tailWord_2711393 prefixEnd_2711393 1392247852236215396118037 := by
  unfold tailWord_2711393
  simp only [CollatzResearch.WordTrace]
  refine ⟨98892627066093704902698833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65928418044062469935132555 98892627066093704902698833)
  ·
    refine ⟨74169470299570278677024125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98892627066093704902698833 74169470299570278677024125)
    ·
      refine ⟨27813551362338854503884047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74169470299570278677024125 27813551362338854503884047)
      ·
        refine ⟨41720327043508281755826071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27813551362338854503884047 41720327043508281755826071)
        ·
          refine ⟨62580490565262422633739107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41720327043508281755826071 62580490565262422633739107)
          ·
            refine ⟨93870735847893633950608661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62580490565262422633739107 93870735847893633950608661)
            ·
              refine ⟨4400190742870014091434781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 93870735847893633950608661 4400190742870014091434781)
              ·
                refine ⟨1650071528576255284288043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4400190742870014091434781 1650071528576255284288043)
                ·
                  refine ⟨2475107292864382926432065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1650071528576255284288043 2475107292864382926432065)
                  ·
                    refine ⟨1856330469648287194824049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2475107292864382926432065 1856330469648287194824049)
                    ·
                      refine ⟨1392247852236215396118037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1856330469648287194824049 1392247852236215396118037)
                      ·
                        rfl

theorem cell23_2711393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 6, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 6, 3, 1, 2, 2].length) (baseStart_2711393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2711393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2711393 prefixEnd_2711393 := by exact prefixLift 2711393
  have htrace : WordTrace (prefixWord ++ tailWord_2711393) baseStart_2711393 baseEnd_2711393 := by
    simpa [prefixWord, tailWord_2711393, baseEnd_2711393] using wordTrace_append hprefix tailTrace_2711393
  have hstable : (prefixWord ++ tailWord_2711393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2711393).length < 2 ^ (prefixWord ++ tailWord_2711393).sum := by decide
  have hdescent : baseEnd_2711393 < baseStart_2711393 := by decide
  rcases family_descends (prefixWord ++ tailWord_2711393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2711396 : List Nat := [2, 3, 1, 1, 5, 1, 1, 3, 1, 2, 3]
def baseStart_2711396 : Nat := 118140960795 + 2711396 * 2 ^ 59
def prefixEnd_2711396 : Nat := 4983230072969 + 3 ^ 40 * 2711396 * 2
def baseEnd_2711396 : Nat := 1392249392678178884380523

theorem tailTrace_2711396 : CollatzResearch.WordTrace tailWord_2711396 prefixEnd_2711396 1392249392678178884380523 := by
  unfold tailWord_2711396
  simp only [CollatzResearch.WordTrace]
  refine ⟨49446368242541418207529021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65928490990055224276705361 49446368242541418207529021)
  ·
    refine ⟨18542388090953031827823383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49446368242541418207529021 18542388090953031827823383)
    ·
      refine ⟨27813582136429547741735075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18542388090953031827823383 27813582136429547741735075)
      ·
        refine ⟨41720373204644321612602613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27813582136429547741735075 41720373204644321612602613)
        ·
          refine ⟨3911284987935405151181495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 41720373204644321612602613 3911284987935405151181495)
          ·
            refine ⟨5866927481903107726772243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3911284987935405151181495 5866927481903107726772243)
            ·
              refine ⟨8800391222854661590158365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5866927481903107726772243 8800391222854661590158365)
              ·
                refine ⟨3300146708570498096309387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8800391222854661590158365 3300146708570498096309387)
                ·
                  refine ⟨4950220062855747144464081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3300146708570498096309387 4950220062855747144464081)
                  ·
                    refine ⟨3712665047141810358348061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4950220062855747144464081 3712665047141810358348061)
                    ·
                      refine ⟨1392249392678178884380523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3712665047141810358348061 1392249392678178884380523)
                      ·
                        rfl

theorem cell23_2711396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 3, 1, 2, 3].length) (baseStart_2711396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2711396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2711396 prefixEnd_2711396 := by exact prefixLift 2711396
  have htrace : WordTrace (prefixWord ++ tailWord_2711396) baseStart_2711396 baseEnd_2711396 := by
    simpa [prefixWord, tailWord_2711396, baseEnd_2711396] using wordTrace_append hprefix tailTrace_2711396
  have hstable : (prefixWord ++ tailWord_2711396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2711396).length < 2 ^ (prefixWord ++ tailWord_2711396).sum := by decide
  have hdescent : baseEnd_2711396 < baseStart_2711396 := by decide
  rcases family_descends (prefixWord ++ tailWord_2711396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2711409 : List Nat := [1, 2, 2, 2, 1, 3, 3, 1, 4, 1, 3]
def baseStart_2711409 : Nat := 118140960795 + 2711409 * 2 ^ 59
def prefixEnd_2711409 : Nat := 4983230072969 + 3 ^ 40 * 2711409 * 2
def baseEnd_2711409 : Nat := 1392256067926687333517963

theorem tailTrace_2711409 : CollatzResearch.WordTrace tailWord_2711409 prefixEnd_2711409 1392256067926687333517963 := by
  unfold tailWord_2711409
  simp only [CollatzResearch.WordTrace]
  refine ⟨98893210634035739635281281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65928807089357159756854187 98893210634035739635281281)
  ·
    refine ⟨74169907975526804726460961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98893210634035739635281281 74169907975526804726460961)
    ·
      refine ⟨55627430981645103544845721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74169907975526804726460961 55627430981645103544845721)
      ·
        refine ⟨41720573236233827658634291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55627430981645103544845721 41720573236233827658634291)
        ·
          refine ⟨62580859854350741487951437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41720573236233827658634291 62580859854350741487951437)
          ·
            refine ⟨23467822445381528057981789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62580859854350741487951437 23467822445381528057981789)
            ·
              refine ⟨8800433417018073021743171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23467822445381528057981789 8800433417018073021743171)
              ·
                refine ⟨13200650125527109532614757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8800433417018073021743171 13200650125527109532614757)
                ·
                  refine ⟨2475121898536333037365267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13200650125527109532614757 2475121898536333037365267)
                  ·
                    refine ⟨3712682847804499556047901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2475121898536333037365267 3712682847804499556047901)
                    ·
                      refine ⟨1392256067926687333517963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3712682847804499556047901 1392256067926687333517963)
                      ·
                        rfl

theorem cell23_2711409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 1, 4, 1, 3].length) (baseStart_2711409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2711409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2711409 prefixEnd_2711409 := by exact prefixLift 2711409
  have htrace : WordTrace (prefixWord ++ tailWord_2711409) baseStart_2711409 baseEnd_2711409 := by
    simpa [prefixWord, tailWord_2711409, baseEnd_2711409] using wordTrace_append hprefix tailTrace_2711409
  have hstable : (prefixWord ++ tailWord_2711409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2711409).length < 2 ^ (prefixWord ++ tailWord_2711409).sum := by decide
  have hdescent : baseEnd_2711409 < baseStart_2711409 := by decide
  rcases family_descends (prefixWord ++ tailWord_2711409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2711449 : List Nat := [1, 2, 1, 2, 1, 3, 2, 4, 1, 4, 2]
def baseStart_2711449 : Nat := 118140960795 + 2711449 * 2 ^ 59
def prefixEnd_2711449 : Nat := 4983230072969 + 3 ^ 40 * 2711449 * 2
def baseEnd_2711449 : Nat := 1392276607152867177017779

theorem tailTrace_2711449 : CollatzResearch.WordTrace tailWord_2711449 prefixEnd_2711449 1392276607152867177017779 := by
  unfold tailWord_2711449
  simp only [CollatzResearch.WordTrace]
  refine ⟨98894669553890826466737401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65929779702593884311158267 98894669553890826466737401)
  ·
    refine ⟨74171002165418119850053051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98894669553890826466737401 74171002165418119850053051)
    ·
      refine ⟨111256503248127179775079577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74171002165418119850053051 111256503248127179775079577)
      ·
        refine ⟨83442377436095384831309683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111256503248127179775079577 83442377436095384831309683)
        ·
          refine ⟨125163566154143077246964525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83442377436095384831309683 125163566154143077246964525)
          ·
            refine ⟨46936337307803653967611697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 125163566154143077246964525 46936337307803653967611697)
            ·
              refine ⟨35202252980852740475708773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46936337307803653967611697 35202252980852740475708773)
              ·
                refine ⟨6600422433909888839195395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35202252980852740475708773 6600422433909888839195395)
                ·
                  refine ⟨9900633650864833258793093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6600422433909888839195395 9900633650864833258793093)
                  ·
                    refine ⟨1856368809537156236023705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9900633650864833258793093 1856368809537156236023705)
                    ·
                      refine ⟨1392276607152867177017779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1856368809537156236023705 1392276607152867177017779)
                      ·
                        rfl

theorem cell23_2711449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 4, 1, 4, 2].length) (baseStart_2711449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2711449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2711449 prefixEnd_2711449 := by exact prefixLift 2711449
  have htrace : WordTrace (prefixWord ++ tailWord_2711449) baseStart_2711449 baseEnd_2711449 := by
    simpa [prefixWord, tailWord_2711449, baseEnd_2711449] using wordTrace_append hprefix tailTrace_2711449
  have hstable : (prefixWord ++ tailWord_2711449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2711449).length < 2 ^ (prefixWord ++ tailWord_2711449).sum := by decide
  have hdescent : baseEnd_2711449 < baseStart_2711449 := by decide
  rcases family_descends (prefixWord ++ tailWord_2711449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2711512 : List Nat := [2, 1, 2, 2, 2, 2, 1, 1, 3, 2, 5]
def baseStart_2711512 : Nat := 118140960795 + 2711512 * 2 ^ 59
def prefixEnd_2711512 : Nat := 4983230072969 + 3 ^ 40 * 2711512 * 2
def baseEnd_2711512 : Nat := 1392308956434100430529989

theorem tailTrace_2711512 : CollatzResearch.WordTrace tailWord_2711512 prefixEnd_2711512 1392308956434100430529989 := by
  unfold tailWord_2711512
  simp only [CollatzResearch.WordTrace]
  refine ⟨49448483676331294113140395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65931311568441725484187193 49448483676331294113140395)
  ·
    refine ⟨74172725514496941169710593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49448483676331294113140395 74172725514496941169710593)
    ·
      refine ⟨55629544135872705877282945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74172725514496941169710593 55629544135872705877282945)
      ·
        refine ⟨41722158101904529407962209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55629544135872705877282945 41722158101904529407962209)
        ·
          refine ⟨31291618576428397055971657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41722158101904529407962209 31291618576428397055971657)
          ·
            refine ⟨23468713932321297791978743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31291618576428397055971657 23468713932321297791978743)
            ·
              refine ⟨35203070898481946687968115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23468713932321297791978743 35203070898481946687968115)
              ·
                refine ⟨52804606347722920031952173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35203070898481946687968115 52804606347722920031952173)
                ·
                  refine ⟨19801727380396095011982065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52804606347722920031952173 19801727380396095011982065)
                  ·
                    refine ⟨14851295535297071258986549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19801727380396095011982065 14851295535297071258986549)
                    ·
                      refine ⟨1392308956434100430529989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14851295535297071258986549 1392308956434100430529989)
                      ·
                        rfl

theorem cell23_2711512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 1, 3, 2, 5].length) (baseStart_2711512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2711512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2711512 prefixEnd_2711512 := by exact prefixLift 2711512
  have htrace : WordTrace (prefixWord ++ tailWord_2711512) baseStart_2711512 baseEnd_2711512 := by
    simpa [prefixWord, tailWord_2711512, baseEnd_2711512] using wordTrace_append hprefix tailTrace_2711512
  have hstable : (prefixWord ++ tailWord_2711512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2711512).length < 2 ^ (prefixWord ++ tailWord_2711512).sum := by decide
  have hdescent : baseEnd_2711512 < baseStart_2711512 := by decide
  rcases family_descends (prefixWord ++ tailWord_2711512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2711519 : List Nat := [1, 1, 2, 3, 4, 1, 2, 2, 2, 5]
def baseStart_2711519 : Nat := 118140960795 + 2711519 * 2 ^ 59
def prefixEnd_2711519 : Nat := 4983230072969 + 3 ^ 40 * 2711519 * 2
def baseEnd_2711519 : Nat := 464104183599560634380819

theorem tailTrace_2711519 : CollatzResearch.WordTrace tailWord_2711519 prefixEnd_2711519 464104183599560634380819 := by
  unfold tailWord_2711519
  simp only [CollatzResearch.WordTrace]
  refine ⟨98897222663637228421785611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65931481775758152281190407 98897222663637228421785611)
  ·
    refine ⟨148345833995455842632678417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98897222663637228421785611 148345833995455842632678417)
    ·
      refine ⟨111259375496591881974508813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148345833995455842632678417 111259375496591881974508813)
      ·
        refine ⟨41722265811221955740440805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 111259375496591881974508813 41722265811221955740440805)
        ·
          refine ⟨7822924839604116701332651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41722265811221955740440805 7822924839604116701332651)
          ·
            refine ⟨11734387259406175051998977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7822924839604116701332651 11734387259406175051998977)
            ·
              refine ⟨8800790444554631288999233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11734387259406175051998977 8800790444554631288999233)
              ·
                refine ⟨6600592833415973466749425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8800790444554631288999233 6600592833415973466749425)
                ·
                  refine ⟨4950444625061980100062069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6600592833415973466749425 4950444625061980100062069)
                  ·
                    refine ⟨464104183599560634380819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4950444625061980100062069 464104183599560634380819)
                    ·
                      rfl

theorem cell23_2711519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 2, 2, 5].length) (baseStart_2711519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2711519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2711519 prefixEnd_2711519 := by exact prefixLift 2711519
  have htrace : WordTrace (prefixWord ++ tailWord_2711519) baseStart_2711519 baseEnd_2711519 := by
    simpa [prefixWord, tailWord_2711519, baseEnd_2711519] using wordTrace_append hprefix tailTrace_2711519
  have hstable : (prefixWord ++ tailWord_2711519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2711519).length < 2 ^ (prefixWord ++ tailWord_2711519).sum := by decide
  have hdescent : baseEnd_2711519 < baseStart_2711519 := by decide
  rcases family_descends (prefixWord ++ tailWord_2711519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2711523 : List Nat := [1, 1, 1, 6, 1, 4, 2, 2, 5]
def baseStart_2711523 : Nat := 118140960795 + 2711523 * 2 ^ 59
def prefixEnd_2711523 : Nat := 4983230072969 + 3 ^ 40 * 2711523 * 2
def baseEnd_2711523 : Nat := 154701622746811098610271

theorem tailTrace_2711523 : CollatzResearch.WordTrace tailWord_2711523 prefixEnd_2711523 154701622746811098610271 := by
  unfold tailWord_2711523
  simp only [CollatzResearch.WordTrace]
  refine ⟨98897368555622737104931223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65931579037081824736620815 98897368555622737104931223)
  ·
    refine ⟨148346052833434105657396835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98897368555622737104931223 148346052833434105657396835)
    ·
      refine ⟨222519079250151158486095253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148346052833434105657396835 222519079250151158486095253)
      ·
        refine ⟨10430581839850835554035715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 222519079250151158486095253 10430581839850835554035715)
        ·
          refine ⟨15645872759776253331053573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10430581839850835554035715 15645872759776253331053573)
          ·
            refine ⟨2933601142458047499572545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15645872759776253331053573 2933601142458047499572545)
            ·
              refine ⟨2200200856843535624679409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2933601142458047499572545 2200200856843535624679409)
              ·
                refine ⟨1650150642632651718509557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2200200856843535624679409 1650150642632651718509557)
                ·
                  refine ⟨154701622746811098610271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1650150642632651718509557 154701622746811098610271)
                  ·
                    rfl

theorem cell23_2711523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 2, 2, 5].length) (baseStart_2711523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2711523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2711523 prefixEnd_2711523 := by exact prefixLift 2711523
  have htrace : WordTrace (prefixWord ++ tailWord_2711523) baseStart_2711523 baseEnd_2711523 := by
    simpa [prefixWord, tailWord_2711523, baseEnd_2711523] using wordTrace_append hprefix tailTrace_2711523
  have hstable : (prefixWord ++ tailWord_2711523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2711523).length < 2 ^ (prefixWord ++ tailWord_2711523).sum := by decide
  have hdescent : baseEnd_2711523 < baseStart_2711523 := by decide
  rcases family_descends (prefixWord ++ tailWord_2711523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2711533 : List Nat := [1, 5, 1, 4, 1, 1, 1, 1, 2, 3, 3]
def baseStart_2711533 : Nat := 118140960795 + 2711533 * 2 ^ 59
def prefixEnd_2711533 : Nat := 4983230072969 + 3 ^ 40 * 2711533 * 2
def baseEnd_2711533 : Nat := 1392319739527844848367393

theorem tailTrace_2711533 : CollatzResearch.WordTrace tailWord_2711533 prefixEnd_2711533 1392319739527844848367393 := by
  unfold tailWord_2711533
  simp only [CollatzResearch.WordTrace]
  refine ⟨98897733285586508812795253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65931822190391005875196835 98897733285586508812795253)
  ·
    refine ⟨9271662495523735201199555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 98897733285586508812795253 9271662495523735201199555)
    ·
      refine ⟨13907493743285602801799333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9271662495523735201199555 13907493743285602801799333)
      ·
        refine ⟨2607655076866050525337375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13907493743285602801799333 2607655076866050525337375)
        ·
          refine ⟨3911482615299075788006063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2607655076866050525337375 3911482615299075788006063)
          ·
            refine ⟨5867223922948613682009095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3911482615299075788006063 5867223922948613682009095)
            ·
              refine ⟨8800835884422920523013643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5867223922948613682009095 8800835884422920523013643)
              ·
                refine ⟨13201253826634380784520465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8800835884422920523013643 13201253826634380784520465)
                ·
                  refine ⟨9900940369975785588390349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13201253826634380784520465 9900940369975785588390349)
                  ·
                    refine ⟨3712852638740919595646381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9900940369975785588390349 3712852638740919595646381)
                    ·
                      refine ⟨1392319739527844848367393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3712852638740919595646381 1392319739527844848367393)
                      ·
                        rfl

theorem cell23_2711533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_2711533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2711533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2711533 prefixEnd_2711533 := by exact prefixLift 2711533
  have htrace : WordTrace (prefixWord ++ tailWord_2711533) baseStart_2711533 baseEnd_2711533 := by
    simpa [prefixWord, tailWord_2711533, baseEnd_2711533] using wordTrace_append hprefix tailTrace_2711533
  have hstable : (prefixWord ++ tailWord_2711533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2711533).length < 2 ^ (prefixWord ++ tailWord_2711533).sum := by decide
  have hdescent : baseEnd_2711533 < baseStart_2711533 := by decide
  rcases family_descends (prefixWord ++ tailWord_2711533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2711549 : List Nat := [1, 4, 1, 1, 1, 2, 3, 1, 5, 4]
def baseStart_2711549 : Nat := 118140960795 + 2711549 * 2 ^ 59
def prefixEnd_2711549 : Nat := 4983230072969 + 3 ^ 40 * 2711549 * 2
def baseEnd_2711549 : Nat := 464109318406105595255773

theorem tailTrace_2711549 : CollatzResearch.WordTrace tailWord_2711549 prefixEnd_2711549 464109318406105595255773 := by
  unfold tailWord_2711549
  simp only [CollatzResearch.WordTrace]
  refine ⟨98898316853528543545377701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65932211235685695696918467 98898316853528543545377701)
  ·
    refine ⟨18543434410036601914758319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 98898316853528543545377701 18543434410036601914758319)
    ·
      refine ⟨27815151615054902872137479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18543434410036601914758319 27815151615054902872137479)
      ·
        refine ⟨41722727422582354308206219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27815151615054902872137479 41722727422582354308206219)
        ·
          refine ⟨62584091133873531462309329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41722727422582354308206219 62584091133873531462309329)
          ·
            refine ⟨46938068350405148596731997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62584091133873531462309329 46938068350405148596731997)
            ·
              refine ⟨17601775631401930723774499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46938068350405148596731997 17601775631401930723774499)
              ·
                refine ⟨26402663447102896085661749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17601775631401930723774499 26402663447102896085661749)
                ·
                  refine ⟨2475249698165896508030789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26402663447102896085661749 2475249698165896508030789)
                  ·
                    refine ⟨464109318406105595255773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2475249698165896508030789 464109318406105595255773)
                    ·
                      rfl

theorem cell23_2711549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 1, 5, 4].length) (baseStart_2711549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2711549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2711549 prefixEnd_2711549 := by exact prefixLift 2711549
  have htrace : WordTrace (prefixWord ++ tailWord_2711549) baseStart_2711549 baseEnd_2711549 := by
    simpa [prefixWord, tailWord_2711549, baseEnd_2711549] using wordTrace_append hprefix tailTrace_2711549
  have hstable : (prefixWord ++ tailWord_2711549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2711549).length < 2 ^ (prefixWord ++ tailWord_2711549).sum := by decide
  have hdescent : baseEnd_2711549 < baseStart_2711549 := by decide
  rcases family_descends (prefixWord ++ tailWord_2711549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2711552 : List Nat := [2, 1, 1, 2, 1, 1, 1, 3, 1, 6, 4]
def baseStart_2711552 : Nat := 118140960795 + 2711552 * 2 ^ 59
def prefixEnd_2711552 : Nat := 4983230072969 + 3 ^ 40 * 2711552 * 2
def baseEnd_2711552 : Nat := 1392329495660280274029805

theorem tailTrace_2711552 : CollatzResearch.WordTrace tailWord_2711552 prefixEnd_2711552 1392329495660280274029805 := by
  unfold tailWord_2711552
  simp only [CollatzResearch.WordTrace]
  refine ⟨49449213136258837528868455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65932284181678450038491273 49449213136258837528868455)
  ·
    refine ⟨74173819704388256293302683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49449213136258837528868455 74173819704388256293302683)
    ·
      refine ⟨111260729556582384439954025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74173819704388256293302683 111260729556582384439954025)
      ·
        refine ⟨83445547167436788329965519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111260729556582384439954025 83445547167436788329965519)
        ·
          refine ⟨125168320751155182494948279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83445547167436788329965519 125168320751155182494948279)
          ·
            refine ⟨187752481126732773742422419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125168320751155182494948279 187752481126732773742422419)
            ·
              refine ⟨281628721690099160613633629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 187752481126732773742422419 281628721690099160613633629)
              ·
                refine ⟨105610770633787185230112611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 281628721690099160613633629 105610770633787185230112611)
                ·
                  refine ⟨158416155950680777845168917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 105610770633787185230112611 158416155950680777845168917)
                  ·
                    refine ⟨7425757310188161461492293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 158416155950680777845168917 7425757310188161461492293)
                    ·
                      refine ⟨1392329495660280274029805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7425757310188161461492293 1392329495660280274029805)
                      ·
                        rfl

theorem cell23_2711552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 1, 6, 4].length) (baseStart_2711552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2711552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2711552 prefixEnd_2711552 := by exact prefixLift 2711552
  have htrace : WordTrace (prefixWord ++ tailWord_2711552) baseStart_2711552 baseEnd_2711552 := by
    simpa [prefixWord, tailWord_2711552, baseEnd_2711552] using wordTrace_append hprefix tailTrace_2711552
  have hstable : (prefixWord ++ tailWord_2711552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2711552).length < 2 ^ (prefixWord ++ tailWord_2711552).sum := by decide
  have hdescent : baseEnd_2711552 < baseStart_2711552 := by decide
  rcases family_descends (prefixWord ++ tailWord_2711552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2711606 : List Nat := [5, 1, 2, 1, 1, 1, 1, 1, 2, 5, 3]
def baseStart_2711606 : Nat := 118140960795 + 2711606 * 2 ^ 59
def prefixEnd_2711606 : Nat := 4983230072969 + 3 ^ 40 * 2711606 * 2
def baseEnd_2711606 : Nat := 1392357223615623062754557

theorem tailTrace_2711606 : CollatzResearch.WordTrace tailWord_2711606 prefixEnd_2711606 1392357223615623062754557 := by
  unfold tailWord_2711606
  simp only [CollatzResearch.WordTrace]
  refine ⟨6181274738395127642512667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 65933597209548028186801781 6181274738395127642512667)
  ·
    refine ⟨9271912107592691463769001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6181274738395127642512667 9271912107592691463769001)
    ·
      refine ⟨6953934080694518597826751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9271912107592691463769001 6953934080694518597826751)
      ·
        refine ⟨10430901121041777896740127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6953934080694518597826751 10430901121041777896740127)
        ·
          refine ⟨15646351681562666845110191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10430901121041777896740127 15646351681562666845110191)
          ·
            refine ⟨23469527522344000267665287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15646351681562666845110191 23469527522344000267665287)
            ·
              refine ⟨35204291283516000401497931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23469527522344000267665287 35204291283516000401497931)
              ·
                refine ⟨52806436925274000602246897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35204291283516000401497931 52806436925274000602246897)
                ·
                  refine ⟨39604827693955500451685173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52806436925274000602246897 39604827693955500451685173)
                  ·
                    refine ⟨3712952596308328167345485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39604827693955500451685173 3712952596308328167345485)
                    ·
                      refine ⟨1392357223615623062754557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3712952596308328167345485 1392357223615623062754557)
                      ·
                        rfl

theorem cell23_2711606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 1, 2, 5, 3].length) (baseStart_2711606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2711606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2711606 prefixEnd_2711606 := by exact prefixLift 2711606
  have htrace : WordTrace (prefixWord ++ tailWord_2711606) baseStart_2711606 baseEnd_2711606 := by
    simpa [prefixWord, tailWord_2711606, baseEnd_2711606] using wordTrace_append hprefix tailTrace_2711606
  have hstable : (prefixWord ++ tailWord_2711606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2711606).length < 2 ^ (prefixWord ++ tailWord_2711606).sum := by decide
  have hdescent : baseEnd_2711606 < baseStart_2711606 := by decide
  rcases family_descends (prefixWord ++ tailWord_2711606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2711616 : List Nat := [2, 1, 1, 2, 2, 4, 2, 1, 1, 5, 2]
def baseStart_2711616 : Nat := 118140960795 + 2711616 * 2 ^ 59
def prefixEnd_2711616 : Nat := 4983230072969 + 3 ^ 40 * 2711616 * 2
def baseEnd_2711616 : Nat := 1392362358422168023629511

theorem tailTrace_2711616 : CollatzResearch.WordTrace tailWord_2711616 prefixEnd_2711616 1392362358422168023629511 := by
  unfold tailWord_2711616
  simp only [CollatzResearch.WordTrace]
  refine ⟨49450380272142906994033351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65933840362857209325377801 49450380272142906994033351)
  ·
    refine ⟨74175570408214360491050027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49450380272142906994033351 74175570408214360491050027)
    ·
      refine ⟨111263355612321540736575041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74175570408214360491050027 111263355612321540736575041)
      ·
        refine ⟨83447516709241155552431281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111263355612321540736575041 83447516709241155552431281)
        ·
          refine ⟨62585637531930866664323461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83447516709241155552431281 62585637531930866664323461)
          ·
            refine ⟨11734807037237037499560649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62585637531930866664323461 11734807037237037499560649)
            ·
              refine ⟨8801105277927778124670487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11734807037237037499560649 8801105277927778124670487)
              ·
                refine ⟨13201657916891667187005731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8801105277927778124670487 13201657916891667187005731)
                ·
                  refine ⟨19802486875337500780508597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13201657916891667187005731 19802486875337500780508597)
                  ·
                    refine ⟨1856483144562890698172681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 19802486875337500780508597 1856483144562890698172681)
                    ·
                      refine ⟨1392362358422168023629511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1856483144562890698172681 1392362358422168023629511)
                      ·
                        rfl

theorem cell23_2711616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 1, 1, 5, 2].length) (baseStart_2711616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2711616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2711616 prefixEnd_2711616 := by exact prefixLift 2711616
  have htrace : WordTrace (prefixWord ++ tailWord_2711616) baseStart_2711616 baseEnd_2711616 := by
    simpa [prefixWord, tailWord_2711616, baseEnd_2711616] using wordTrace_append hprefix tailTrace_2711616
  have hstable : (prefixWord ++ tailWord_2711616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2711616).length < 2 ^ (prefixWord ++ tailWord_2711616).sum := by decide
  have hdescent : baseEnd_2711616 < baseStart_2711616 := by decide
  rcases family_descends (prefixWord ++ tailWord_2711616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2711649 : List Nat := [1, 2, 3, 1, 1, 2, 1, 1, 2, 6, 3]
def baseStart_2711649 : Nat := 118140960795 + 2711649 * 2 ^ 59
def prefixEnd_2711649 : Nat := 4983230072969 + 3 ^ 40 * 2711649 * 2
def baseEnd_2711649 : Nat := 1392379303283766394516859

theorem tailTrace_2711649 : CollatzResearch.WordTrace tailWord_2711649 prefixEnd_2711649 1392379303283766394516859 := by
  unfold tailWord_2711649
  simp only [CollatzResearch.WordTrace]
  refine ⟨98901964153166260624018001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65934642768777507082678667 98901964153166260624018001)
  ·
    refine ⟨74176473114874695468013501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98901964153166260624018001 74176473114874695468013501)
    ·
      refine ⟨27816177418078010800505063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74176473114874695468013501 27816177418078010800505063)
      ·
        refine ⟨41724266127117016200757595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27816177418078010800505063 41724266127117016200757595)
        ·
          refine ⟨62586399190675524301136393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41724266127117016200757595 62586399190675524301136393)
          ·
            refine ⟨46939799393006643225852295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62586399190675524301136393 46939799393006643225852295)
            ·
              refine ⟨70409699089509964838778443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46939799393006643225852295 70409699089509964838778443)
              ·
                refine ⟨105614548634264947258167665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70409699089509964838778443 105614548634264947258167665)
                ·
                  refine ⟨79210911475698710443625749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 105614548634264947258167665 79210911475698710443625749)
                  ·
                    refine ⟨3713011475423377052044957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 79210911475698710443625749 3713011475423377052044957)
                    ·
                      refine ⟨1392379303283766394516859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3713011475423377052044957 1392379303283766394516859)
                      ·
                        rfl

theorem cell23_2711649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 1, 2, 6, 3].length) (baseStart_2711649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2711649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2711649 prefixEnd_2711649 := by exact prefixLift 2711649
  have htrace : WordTrace (prefixWord ++ tailWord_2711649) baseStart_2711649 baseEnd_2711649 := by
    simpa [prefixWord, tailWord_2711649, baseEnd_2711649] using wordTrace_append hprefix tailTrace_2711649
  have hstable : (prefixWord ++ tailWord_2711649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2711649).length < 2 ^ (prefixWord ++ tailWord_2711649).sum := by decide
  have hdescent : baseEnd_2711649 < baseStart_2711649 := by decide
  rcases family_descends (prefixWord ++ tailWord_2711649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2711663 : List Nat := [1, 1, 2, 1, 3, 6, 1, 2, 1, 1, 4]
def baseStart_2711663 : Nat := 118140960795 + 2711663 * 2 ^ 59
def prefixEnd_2711663 : Nat := 4983230072969 + 3 ^ 40 * 2711663 * 2
def baseEnd_2711663 : Nat := 1392386492012929339741795

theorem tailTrace_2711663 : CollatzResearch.WordTrace tailWord_2711663 prefixEnd_2711663 1392386492012929339741795 := by
  unfold tailWord_2711663
  simp only [CollatzResearch.WordTrace]
  refine ⟨98902474775115541015027643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65934983183410360676685095 98902474775115541015027643)
  ·
    refine ⟨148353712162673311522541465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98902474775115541015027643 148353712162673311522541465)
    ·
      refine ⟨111265284122004983641906099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148353712162673311522541465 111265284122004983641906099)
      ·
        refine ⟨166897926183007475462859149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111265284122004983641906099 166897926183007475462859149)
        ·
          refine ⟨62586722318627803298572181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 166897926183007475462859149 62586722318627803298572181)
          ·
            refine ⟨2933752608685678279620571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 62586722318627803298572181 2933752608685678279620571)
            ·
              refine ⟨4400628913028517419430857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2933752608685678279620571 4400628913028517419430857)
              ·
                refine ⟨3300471684771388064573143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4400628913028517419430857 3300471684771388064573143)
                ·
                  refine ⟨4950707527157082096859715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3300471684771388064573143 4950707527157082096859715)
                  ·
                    refine ⟨7426061290735623145289573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4950707527157082096859715 7426061290735623145289573)
                    ·
                      refine ⟨1392386492012929339741795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7426061290735623145289573 1392386492012929339741795)
                      ·
                        rfl

theorem cell23_2711663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 1, 2, 1, 1, 4].length) (baseStart_2711663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2711663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2711663 prefixEnd_2711663 := by exact prefixLift 2711663
  have htrace : WordTrace (prefixWord ++ tailWord_2711663) baseStart_2711663 baseEnd_2711663 := by
    simpa [prefixWord, tailWord_2711663, baseEnd_2711663] using wordTrace_append hprefix tailTrace_2711663
  have hstable : (prefixWord ++ tailWord_2711663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2711663).length < 2 ^ (prefixWord ++ tailWord_2711663).sum := by decide
  have hdescent : baseEnd_2711663 < baseStart_2711663 := by decide
  rcases family_descends (prefixWord ++ tailWord_2711663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2711676 : List Nat := [2, 2, 2, 1, 1, 5, 1, 2, 1, 2, 4]
def baseStart_2711676 : Nat := 118140960795 + 2711676 * 2 ^ 59
def prefixEnd_2711676 : Nat := 4983230072969 + 3 ^ 40 * 2711676 * 2
def baseEnd_2711676 : Nat := 1392393167261437788879235

theorem tailTrace_2711676 : CollatzResearch.WordTrace tailWord_2711676 prefixEnd_2711676 1392393167261437788879235 := by
  unfold tailWord_2711676
  simp only [CollatzResearch.WordTrace]
  refine ⟨49451474462034222117625441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65935299282712296156833921 49451474462034222117625441)
  ·
    refine ⟨37088605846525666588219081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49451474462034222117625441 37088605846525666588219081)
    ·
      refine ⟨27816454384894249941164311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37088605846525666588219081 27816454384894249941164311)
      ·
        refine ⟨41724681577341374911746467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27816454384894249941164311 41724681577341374911746467)
        ·
          refine ⟨62587022366012062367619701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41724681577341374911746467 62587022366012062367619701)
          ·
            refine ⟨5867533346813630846964347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 62587022366012062367619701 5867533346813630846964347)
            ·
              refine ⟨8801300020220446270446521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5867533346813630846964347 8801300020220446270446521)
              ·
                refine ⟨6600975015165334702834891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8801300020220446270446521 6600975015165334702834891)
                ·
                  refine ⟨9901462522748002054252337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6600975015165334702834891 9901462522748002054252337)
                  ·
                    refine ⟨7426096892061001540689253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9901462522748002054252337 7426096892061001540689253)
                    ·
                      refine ⟨1392393167261437788879235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7426096892061001540689253 1392393167261437788879235)
                      ·
                        rfl

theorem cell23_2711676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 2, 1, 2, 4].length) (baseStart_2711676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2711676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2711676 prefixEnd_2711676 := by exact prefixLift 2711676
  have htrace : WordTrace (prefixWord ++ tailWord_2711676) baseStart_2711676 baseEnd_2711676 := by
    simpa [prefixWord, tailWord_2711676, baseEnd_2711676] using wordTrace_append hprefix tailTrace_2711676
  have hstable : (prefixWord ++ tailWord_2711676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2711676).length < 2 ^ (prefixWord ++ tailWord_2711676).sum := by decide
  have hdescent : baseEnd_2711676 < baseStart_2711676 := by decide
  rcases family_descends (prefixWord ++ tailWord_2711676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2711680 : List Nat := [2, 1, 1, 2, 1, 3, 1, 7, 1, 2, 2]
def baseStart_2711680 : Nat := 118140960795 + 2711680 * 2 ^ 59
def prefixEnd_2711680 : Nat := 4983230072969 + 3 ^ 40 * 2711680 * 2
def baseEnd_2711680 : Nat := 1392395221184055773229217

theorem tailTrace_2711680 : CollatzResearch.WordTrace tailWord_2711680 prefixEnd_2711680 1392395221184055773229217 := by
  unfold tailWord_2711680
  simp only [CollatzResearch.WordTrace]
  refine ⟨49451547408026976459198247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65935396544035968612264329 49451547408026976459198247)
  ·
    refine ⟨74177321112040464688797371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49451547408026976459198247 74177321112040464688797371)
    ·
      refine ⟨111265981668060697033196057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74177321112040464688797371 111265981668060697033196057)
      ·
        refine ⟨83449486251045522774897043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111265981668060697033196057 83449486251045522774897043)
        ·
          refine ⟨125174229376568284162345565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83449486251045522774897043 125174229376568284162345565)
          ·
            refine ⟨46940336016213106560879587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 125174229376568284162345565 46940336016213106560879587)
            ·
              refine ⟨70410504024319659841319381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46940336016213106560879587 70410504024319659841319381)
              ·
                refine ⟨1650246188069992027530923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 70410504024319659841319381 1650246188069992027530923)
                ·
                  refine ⟨2475369282104988041296385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1650246188069992027530923 2475369282104988041296385)
                  ·
                    refine ⟨1856526961578741030972289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2475369282104988041296385 1856526961578741030972289)
                    ·
                      refine ⟨1392395221184055773229217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1856526961578741030972289 1392395221184055773229217)
                      ·
                        rfl

theorem cell23_2711680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 7, 1, 2, 2].length) (baseStart_2711680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2711680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2711680 prefixEnd_2711680 := by exact prefixLift 2711680
  have htrace : WordTrace (prefixWord ++ tailWord_2711680) baseStart_2711680 baseEnd_2711680 := by
    simpa [prefixWord, tailWord_2711680, baseEnd_2711680] using wordTrace_append hprefix tailTrace_2711680
  have hstable : (prefixWord ++ tailWord_2711680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2711680).length < 2 ^ (prefixWord ++ tailWord_2711680).sum := by decide
  have hdescent : baseEnd_2711680 < baseStart_2711680 := by decide
  rcases family_descends (prefixWord ++ tailWord_2711680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2711703 : List Nat := [1, 1, 3, 3, 5, 1, 1, 8]
def baseStart_2711703 : Nat := 118140960795 + 2711703 * 2 ^ 59
def prefixEnd_2711703 : Nat := 4983230072969 + 3 ^ 40 * 2711703 * 2
def baseEnd_2711703 : Nat := 51570630786633673453393

theorem tailTrace_2711703 : CollatzResearch.WordTrace tailWord_2711703 prefixEnd_2711703 51570630786633673453393 := by
  unfold tailWord_2711703
  simp only [CollatzResearch.WordTrace]
  refine ⟨98903933694970627846483763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65935955796647085230989175 98903933694970627846483763)
  ·
    refine ⟨148355900542455941769725645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98903933694970627846483763 148355900542455941769725645)
    ·
      refine ⟨55633462703420978163647117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 148355900542455941769725645 55633462703420978163647117)
      ·
        refine ⟨20862548513782866811367669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55633462703420978163647117 20862548513782866811367669)
        ·
          refine ⟨1955863923167143763565719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 20862548513782866811367669 1955863923167143763565719)
          ·
            refine ⟨2933795884750715645348579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1955863923167143763565719 2933795884750715645348579)
            ·
              refine ⟨4400693827126073468022869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2933795884750715645348579 4400693827126073468022869)
              ·
                refine ⟨51570630786633673453393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4400693827126073468022869 51570630786633673453393)
                ·
                  rfl

theorem cell23_2711703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 1, 8].length) (baseStart_2711703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2711703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2711703 prefixEnd_2711703 := by exact prefixLift 2711703
  have htrace : WordTrace (prefixWord ++ tailWord_2711703) baseStart_2711703 baseEnd_2711703 := by
    simpa [prefixWord, tailWord_2711703, baseEnd_2711703] using wordTrace_append hprefix tailTrace_2711703
  have hstable : (prefixWord ++ tailWord_2711703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2711703).length < 2 ^ (prefixWord ++ tailWord_2711703).sum := by decide
  have hdescent : baseEnd_2711703 < baseStart_2711703 := by decide
  rcases family_descends (prefixWord ++ tailWord_2711703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2711710 : List Nat := [4, 3, 1, 1, 3, 1, 2, 1, 1, 2, 4]
def baseStart_2711710 : Nat := 118140960795 + 2711710 * 2 ^ 59
def prefixEnd_2711710 : Nat := 4983230072969 + 3 ^ 40 * 2711710 * 2
def baseEnd_2711710 : Nat := 1392410625603690655854079

theorem tailTrace_2711710 : CollatzResearch.WordTrace tailWord_2711710 prefixEnd_2711710 1392410625603690655854079 := by
  unfold tailWord_2711710
  simp only [CollatzResearch.WordTrace]
  refine ⟨12363023625743158505248573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65936126003963512027992389 12363023625743158505248573)
  ·
    refine ⟨4636133859653684439468215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12363023625743158505248573 4636133859653684439468215)
    ·
      refine ⟨6954200789480526659202323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4636133859653684439468215 6954200789480526659202323)
      ·
        refine ⟨10431301184220789988803485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6954200789480526659202323 10431301184220789988803485)
        ·
          refine ⟨3911737944082796245801307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10431301184220789988803485 3911737944082796245801307)
          ·
            refine ⟨5867606916124194368701961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3911737944082796245801307 5867606916124194368701961)
            ·
              refine ⟨4400705187093145776526471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5867606916124194368701961 4400705187093145776526471)
              ·
                refine ⟨6601057780639718664789707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4400705187093145776526471 6601057780639718664789707)
                ·
                  refine ⟨9901586670959577997184561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6601057780639718664789707 9901586670959577997184561)
                  ·
                    refine ⟨7426190003219683497888421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9901586670959577997184561 7426190003219683497888421)
                    ·
                      refine ⟨1392410625603690655854079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7426190003219683497888421 1392410625603690655854079)
                      ·
                        rfl

theorem cell23_2711710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 2, 1, 1, 2, 4].length) (baseStart_2711710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2711710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2711710 prefixEnd_2711710 := by exact prefixLift 2711710
  have htrace : WordTrace (prefixWord ++ tailWord_2711710) baseStart_2711710 baseEnd_2711710 := by
    simpa [prefixWord, tailWord_2711710, baseEnd_2711710] using wordTrace_append hprefix tailTrace_2711710
  have hstable : (prefixWord ++ tailWord_2711710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2711710).length < 2 ^ (prefixWord ++ tailWord_2711710).sum := by decide
  have hdescent : baseEnd_2711710 < baseStart_2711710 := by decide
  rcases family_descends (prefixWord ++ tailWord_2711710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2711713 : List Nat := [1, 2, 3, 3, 1, 3, 2, 1, 1, 3, 3]
def baseStart_2711713 : Nat := 118140960795 + 2711713 * 2 ^ 59
def prefixEnd_2711713 : Nat := 4983230072969 + 3 ^ 40 * 2711713 * 2
def baseEnd_2711713 : Nat := 1392412166045654144116565

theorem tailTrace_2711713 : CollatzResearch.WordTrace tailWord_2711713 prefixEnd_2711713 1392412166045654144116565 := by
  unfold tailWord_2711713
  simp only [CollatzResearch.WordTrace]
  refine ⟨98904298424934399554347793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65936198949956266369565195 98904298424934399554347793)
  ·
    refine ⟨74178223818700799665760845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98904298424934399554347793 74178223818700799665760845)
    ·
      refine ⟨27816833932012799874660317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74178223818700799665760845 27816833932012799874660317)
      ·
        refine ⟨10431312724504799952997619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27816833932012799874660317 10431312724504799952997619)
        ·
          refine ⟨15646969086757199929496429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10431312724504799952997619 15646969086757199929496429)
          ·
            refine ⟨5867613407533949973561161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15646969086757199929496429 5867613407533949973561161)
            ·
              refine ⟨4400710055650462480170871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5867613407533949973561161 4400710055650462480170871)
              ·
                refine ⟨6601065083475693720256307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4400710055650462480170871 6601065083475693720256307)
                ·
                  refine ⟨9901597625213540580384461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6601065083475693720256307 9901597625213540580384461)
                  ·
                    refine ⟨3713099109455077717644173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9901597625213540580384461 3713099109455077717644173)
                    ·
                      refine ⟨1392412166045654144116565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3713099109455077717644173 1392412166045654144116565)
                      ·
                        rfl

theorem cell23_2711713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 2, 1, 1, 3, 3].length) (baseStart_2711713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2711713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2711713 prefixEnd_2711713 := by exact prefixLift 2711713
  have htrace : WordTrace (prefixWord ++ tailWord_2711713) baseStart_2711713 baseEnd_2711713 := by
    simpa [prefixWord, tailWord_2711713, baseEnd_2711713] using wordTrace_append hprefix tailTrace_2711713
  have hstable : (prefixWord ++ tailWord_2711713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2711713).length < 2 ^ (prefixWord ++ tailWord_2711713).sum := by decide
  have hdescent : baseEnd_2711713 < baseStart_2711713 := by decide
  rcases family_descends (prefixWord ++ tailWord_2711713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2711739 : List Nat := [1, 1, 1, 1, 1, 2, 6, 1, 1, 3, 5]
def baseStart_2711739 : Nat := 118140960795 + 2711739 * 2 ^ 59
def prefixEnd_2711739 : Nat := 4983230072969 + 3 ^ 40 * 2711739 * 2
def baseEnd_2711739 : Nat := 1392425516542671042391445

theorem tailTrace_2711739 : CollatzResearch.WordTrace tailWord_2711739 prefixEnd_2711739 1392425516542671042391445 := by
  unfold tailWord_2711739
  simp only [CollatzResearch.WordTrace]
  refine ⟨98905246722840205994794271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65936831148560137329862847 98905246722840205994794271)
  ·
    refine ⟨148357870084260308992191407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98905246722840205994794271 148357870084260308992191407)
    ·
      refine ⟨222536805126390463488287111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148357870084260308992191407 222536805126390463488287111)
      ·
        refine ⟨333805207689585695232430667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222536805126390463488287111 333805207689585695232430667)
        ·
          refine ⟨500707811534378542848646001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 333805207689585695232430667 500707811534378542848646001)
          ·
            refine ⟨375530858650783907136484501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 500707811534378542848646001 375530858650783907136484501)
            ·
              refine ⟨17603008999255495647022711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 375530858650783907136484501 17603008999255495647022711)
              ·
                refine ⟨26404513498883243470534067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17603008999255495647022711 26404513498883243470534067)
                ·
                  refine ⟨39606770248324865205801101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26404513498883243470534067 39606770248324865205801101)
                  ·
                    refine ⟨14852538843121824452175413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39606770248324865205801101 14852538843121824452175413)
                    ·
                      refine ⟨1392425516542671042391445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14852538843121824452175413 1392425516542671042391445)
                      ·
                        rfl

theorem cell23_2711739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 1, 1, 3, 5].length) (baseStart_2711739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2711739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2711739 prefixEnd_2711739 := by exact prefixLift 2711739
  have htrace : WordTrace (prefixWord ++ tailWord_2711739) baseStart_2711739 baseEnd_2711739 := by
    simpa [prefixWord, tailWord_2711739, baseEnd_2711739] using wordTrace_append hprefix tailTrace_2711739
  have hstable : (prefixWord ++ tailWord_2711739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2711739).length < 2 ^ (prefixWord ++ tailWord_2711739).sum := by decide
  have hdescent : baseEnd_2711739 < baseStart_2711739 := by decide
  rcases family_descends (prefixWord ++ tailWord_2711739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2711770 : List Nat := [3, 1, 1, 2, 2, 1, 2, 5, 2, 2, 2]
def baseStart_2711770 : Nat := 118140960795 + 2711770 * 2 ^ 59
def prefixEnd_2711770 : Nat := 4983230072969 + 3 ^ 40 * 2711770 * 2
def baseEnd_2711770 : Nat := 1392441434442960421103803

theorem tailTrace_2711770 : CollatzResearch.WordTrace tailWord_2711770 prefixEnd_2711770 1392441434442960421103803 := by
  unfold tailWord_2711770
  simp only [CollatzResearch.WordTrace]
  refine ⟨24726594346431974572293191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65937584923818598859448509 24726594346431974572293191)
  ·
    refine ⟨37089891519647961858439787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24726594346431974572293191 37089891519647961858439787)
    ·
      refine ⟨55634837279471942787659681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37089891519647961858439787 55634837279471942787659681)
      ·
        refine ⟨41726127959603957090744761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55634837279471942787659681 41726127959603957090744761)
        ·
          refine ⟨31294595969702967818058571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41726127959603957090744761 31294595969702967818058571)
          ·
            refine ⟨46941893954554451727087857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31294595969702967818058571 46941893954554451727087857)
            ·
              refine ⟨35206420465915838795315893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46941893954554451727087857 35206420465915838795315893)
              ·
                refine ⟨3300601918679609887060865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35206420465915838795315893 3300601918679609887060865)
                ·
                  refine ⟨2475451439009707415295649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3300601918679609887060865 2475451439009707415295649)
                  ·
                    refine ⟨1856588579257280561471737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2475451439009707415295649 1856588579257280561471737)
                    ·
                      refine ⟨1392441434442960421103803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1856588579257280561471737 1392441434442960421103803)
                      ·
                        rfl

theorem cell23_2711770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 5, 2, 2, 2].length) (baseStart_2711770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2711770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2711770 prefixEnd_2711770 := by exact prefixLift 2711770
  have htrace : WordTrace (prefixWord ++ tailWord_2711770) baseStart_2711770 baseEnd_2711770 := by
    simpa [prefixWord, tailWord_2711770, baseEnd_2711770] using wordTrace_append hprefix tailTrace_2711770
  have hstable : (prefixWord ++ tailWord_2711770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2711770).length < 2 ^ (prefixWord ++ tailWord_2711770).sum := by decide
  have hdescent : baseEnd_2711770 < baseStart_2711770 := by decide
  rcases family_descends (prefixWord ++ tailWord_2711770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2711793 : List Nat := [1, 2, 2, 2, 2, 1, 5, 3, 5]
def baseStart_2711793 : Nat := 118140960795 + 2711793 * 2 ^ 59
def prefixEnd_2711793 : Nat := 4983230072969 + 3 ^ 40 * 2711793 * 2
def baseEnd_2711793 : Nat := 154717027166445981235133

theorem tailTrace_2711793 : CollatzResearch.WordTrace tailWord_2711793 prefixEnd_2711793 154717027166445981235133 := by
  unfold tailWord_2711793
  simp only [CollatzResearch.WordTrace]
  refine ⟨98907216264644573217260033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65938144176429715478173355 98907216264644573217260033)
  ·
    refine ⟨74180412198483429912945025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98907216264644573217260033 74180412198483429912945025)
    ·
      refine ⟨55635309148862572434708769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74180412198483429912945025 55635309148862572434708769)
      ·
        refine ⟨41726481861646929326031577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55635309148862572434708769 41726481861646929326031577)
        ·
          refine ⟨31294861396235196994523683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41726481861646929326031577 31294861396235196994523683)
          ·
            refine ⟨46942292094352795491785525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31294861396235196994523683 46942292094352795491785525)
            ·
              refine ⟨4400839883845574577354893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 46942292094352795491785525 4400839883845574577354893)
              ·
                refine ⟨1650314956442090466508085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4400839883845574577354893 1650314956442090466508085)
                ·
                  refine ⟨154717027166445981235133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1650314956442090466508085 154717027166445981235133)
                  ·
                    rfl

theorem cell23_2711793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 5, 3, 5].length) (baseStart_2711793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2711793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2711793 prefixEnd_2711793 := by exact prefixLift 2711793
  have htrace : WordTrace (prefixWord ++ tailWord_2711793) baseStart_2711793 baseEnd_2711793 := by
    simpa [prefixWord, tailWord_2711793, baseEnd_2711793] using wordTrace_append hprefix tailTrace_2711793
  have hstable : (prefixWord ++ tailWord_2711793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2711793).length < 2 ^ (prefixWord ++ tailWord_2711793).sum := by decide
  have hdescent : baseEnd_2711793 < baseStart_2711793 := by decide
  rcases family_descends (prefixWord ++ tailWord_2711793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2711810 : List Nat := [3, 4, 1, 1, 2, 3, 1, 1, 7]
def baseStart_2711810 : Nat := 118140960795 + 2711810 * 2 ^ 59
def prefixEnd_2711810 : Nat := 4983230072969 + 3 ^ 40 * 2711810 * 2
def baseEnd_2711810 : Nat := 154717997074348918289291

theorem tailTrace_2711810 : CollatzResearch.WordTrace tailWord_2711810 prefixEnd_2711810 154717997074348918289291 := by
  unfold tailWord_2711810
  simp only [CollatzResearch.WordTrace]
  refine ⟨24726959076395746280157221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65938557537055323413752589 24726959076395746280157221)
  ·
    refine ⟨4636304826824202427529479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24726959076395746280157221 4636304826824202427529479)
    ·
      refine ⟨6954457240236303641294219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4636304826824202427529479 6954457240236303641294219)
      ·
        refine ⟨10431685860354455461941329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6954457240236303641294219 10431685860354455461941329)
        ·
          refine ⟨7823764395265841596455997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10431685860354455461941329 7823764395265841596455997)
          ·
            refine ⟨2933911648224690598670999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7823764395265841596455997 2933911648224690598670999)
            ·
              refine ⟨4400867472337035898006499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2933911648224690598670999 4400867472337035898006499)
              ·
                refine ⟨6601301208505553847009749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4400867472337035898006499 6601301208505553847009749)
                ·
                  refine ⟨154717997074348918289291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6601301208505553847009749 154717997074348918289291)
                  ·
                    rfl

theorem cell23_2711810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 1, 1, 7].length) (baseStart_2711810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2711810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2711810 prefixEnd_2711810 := by exact prefixLift 2711810
  have htrace : WordTrace (prefixWord ++ tailWord_2711810) baseStart_2711810 baseEnd_2711810 := by
    simpa [prefixWord, tailWord_2711810, baseEnd_2711810] using wordTrace_append hprefix tailTrace_2711810
  have hstable : (prefixWord ++ tailWord_2711810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2711810).length < 2 ^ (prefixWord ++ tailWord_2711810).sum := by decide
  have hdescent : baseEnd_2711810 < baseStart_2711810 := by decide
  rcases family_descends (prefixWord ++ tailWord_2711810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2711816 : List Nat := [2, 1, 3, 2, 3, 1, 1, 1, 1, 1, 7]
def baseStart_2711816 : Nat := 118140960795 + 2711816 * 2 ^ 59
def prefixEnd_2711816 : Nat := 4983230072969 + 3 ^ 40 * 2711816 * 2
def baseEnd_2711816 : Nat := 1392465054553067241128591

theorem tailTrace_2711816 : CollatzResearch.WordTrace tailWord_2711816 prefixEnd_2711816 1392465054553067241128591 := by
  unfold tailWord_2711816
  simp only [CollatzResearch.WordTrace]
  refine ⟨49454027571780624072673651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65938703429040832096898201 49454027571780624072673651)
  ·
    refine ⟨74181041357670936109010477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49454027571780624072673651 74181041357670936109010477)
    ·
      refine ⟨27817890509126601040878929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74181041357670936109010477 27817890509126601040878929)
      ·
        refine ⟨20863417881844950780659197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27817890509126601040878929 20863417881844950780659197)
        ·
          refine ⟨7823781705691856542747199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20863417881844950780659197 7823781705691856542747199)
          ·
            refine ⟨11735672558537784814120799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7823781705691856542747199 11735672558537784814120799)
            ·
              refine ⟨17603508837806677221181199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11735672558537784814120799 17603508837806677221181199)
              ·
                refine ⟨26405263256710015831771799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17603508837806677221181199 26405263256710015831771799)
                ·
                  refine ⟨39607894885065023747657699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26405263256710015831771799 39607894885065023747657699)
                  ·
                    refine ⟨59411842327597535621486549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39607894885065023747657699 59411842327597535621486549)
                    ·
                      refine ⟨1392465054553067241128591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 59411842327597535621486549 1392465054553067241128591)
                      ·
                        rfl

theorem cell23_2711816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 1, 1, 1, 7].length) (baseStart_2711816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2711816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2711816 prefixEnd_2711816 := by exact prefixLift 2711816
  have htrace : WordTrace (prefixWord ++ tailWord_2711816) baseStart_2711816 baseEnd_2711816 := by
    simpa [prefixWord, tailWord_2711816, baseEnd_2711816] using wordTrace_append hprefix tailTrace_2711816
  have hstable : (prefixWord ++ tailWord_2711816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2711816).length < 2 ^ (prefixWord ++ tailWord_2711816).sum := by decide
  have hdescent : baseEnd_2711816 < baseStart_2711816 := by decide
  rcases family_descends (prefixWord ++ tailWord_2711816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2711843 : List Nat := [1, 1, 1, 4, 2, 2, 4, 1, 2, 1, 4]
def baseStart_2711843 : Nat := 118140960795 + 2711843 * 2 ^ 59
def prefixEnd_2711843 : Nat := 4983230072969 + 3 ^ 40 * 2711843 * 2
def baseEnd_2711843 : Nat := 1392478918530738635490967

theorem tailTrace_2711843 : CollatzResearch.WordTrace tailWord_2711843 prefixEnd_2711843 1392478918530738635490967 := by
  unfold tailWord_2711843
  simp only [CollatzResearch.WordTrace]
  refine ⟨98909039914463431756580183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65939359942975621171053455 98909039914463431756580183)
  ·
    refine ⟨148363559871695147634870275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98909039914463431756580183 148363559871695147634870275)
    ·
      refine ⟨222545339807542721452305413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148363559871695147634870275 222545339807542721452305413)
      ·
        refine ⟨41727251213914260272307265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 222545339807542721452305413 41727251213914260272307265)
        ·
          refine ⟨31295438410435695204230449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41727251213914260272307265 31295438410435695204230449)
          ·
            refine ⟨23471578807826771403172837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31295438410435695204230449 23471578807826771403172837)
            ·
              refine ⟨4400921026467519638094907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23471578807826771403172837 4400921026467519638094907)
              ·
                refine ⟨6601381539701279457142361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4400921026467519638094907 6601381539701279457142361)
                ·
                  refine ⟨4951036154775959592856771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6601381539701279457142361 4951036154775959592856771)
                  ·
                    refine ⟨7426554232163939389285157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4951036154775959592856771 7426554232163939389285157)
                    ·
                      refine ⟨1392478918530738635490967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7426554232163939389285157 1392478918530738635490967)
                      ·
                        rfl

theorem cell23_2711843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 4, 1, 2, 1, 4].length) (baseStart_2711843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2711843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2711843 prefixEnd_2711843 := by exact prefixLift 2711843
  have htrace : WordTrace (prefixWord ++ tailWord_2711843) baseStart_2711843 baseEnd_2711843 := by
    simpa [prefixWord, tailWord_2711843, baseEnd_2711843] using wordTrace_append hprefix tailTrace_2711843
  have hstable : (prefixWord ++ tailWord_2711843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2711843).length < 2 ^ (prefixWord ++ tailWord_2711843).sum := by decide
  have hdescent : baseEnd_2711843 < baseStart_2711843 := by decide
  rcases family_descends (prefixWord ++ tailWord_2711843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2711860 : List Nat := [2, 5, 1, 1, 1, 2, 2, 2, 2, 1, 4]
def baseStart_2711860 : Nat := 118140960795 + 2711860 * 2 ^ 59
def prefixEnd_2711860 : Nat := 4983230072969 + 3 ^ 40 * 2711860 * 2
def baseEnd_2711860 : Nat := 1392487647701865068978389

theorem tailTrace_2711860 : CollatzResearch.WordTrace tailWord_2711860 prefixEnd_2711860 1392487647701865068978389 := by
  unfold tailWord_2711860
  simp only [CollatzResearch.WordTrace]
  refine ⟨49454829977700921829974517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65939773303601229106632689 49454829977700921829974517)
  ·
    refine ⟨4636390310409461421560111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 49454829977700921829974517 4636390310409461421560111)
    ·
      refine ⟨6954585465614192132340167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4636390310409461421560111 6954585465614192132340167)
      ·
        refine ⟨10431878198421288198510251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6954585465614192132340167 10431878198421288198510251)
        ·
          refine ⟨15647817297631932297765377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10431878198421288198510251 15647817297631932297765377)
          ·
            refine ⟨11735862973223949223324033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15647817297631932297765377 11735862973223949223324033)
            ·
              refine ⟨8801897229917961917493025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11735862973223949223324033 8801897229917961917493025)
              ·
                refine ⟨6601422922438471438119769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8801897229917961917493025 6601422922438471438119769)
                ·
                  refine ⟨4951067191828853578589827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6601422922438471438119769 4951067191828853578589827)
                  ·
                    refine ⟨7426600787743280367884741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4951067191828853578589827 7426600787743280367884741)
                    ·
                      refine ⟨1392487647701865068978389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7426600787743280367884741 1392487647701865068978389)
                      ·
                        rfl

theorem cell23_2711860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 2, 2, 1, 4].length) (baseStart_2711860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2711860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2711860 prefixEnd_2711860 := by exact prefixLift 2711860
  have htrace : WordTrace (prefixWord ++ tailWord_2711860) baseStart_2711860 baseEnd_2711860 := by
    simpa [prefixWord, tailWord_2711860, baseEnd_2711860] using wordTrace_append hprefix tailTrace_2711860
  have hstable : (prefixWord ++ tailWord_2711860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2711860).length < 2 ^ (prefixWord ++ tailWord_2711860).sum := by decide
  have hdescent : baseEnd_2711860 < baseStart_2711860 := by decide
  rcases family_descends (prefixWord ++ tailWord_2711860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2711886 : List Nat := [4, 1, 1, 1, 1, 1, 2, 1, 3, 2, 6]
def baseStart_2711886 : Nat := 118140960795 + 2711886 * 2 ^ 59
def prefixEnd_2711886 : Nat := 4983230072969 + 3 ^ 40 * 2711886 * 2
def baseEnd_2711886 : Nat := 1392500998198881967253269

theorem tailTrace_2711886 : CollatzResearch.WordTrace tailWord_2711886 prefixEnd_2711886 1392500998198881967253269 := by
  unfold tailWord_2711886
  simp only [CollatzResearch.WordTrace]
  refine ⟨12363826031663456262549439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65940405502205100066930341 12363826031663456262549439)
  ·
    refine ⟨18545739047495184393824159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12363826031663456262549439 18545739047495184393824159)
    ·
      refine ⟨27818608571242776590736239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18545739047495184393824159 27818608571242776590736239)
      ·
        refine ⟨41727912856864164886104359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27818608571242776590736239 41727912856864164886104359)
        ·
          refine ⟨62591869285296247329156539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41727912856864164886104359 62591869285296247329156539)
          ·
            refine ⟨93887803927944370993734809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62591869285296247329156539 93887803927944370993734809)
            ·
              refine ⟨70415852945958278245301107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93887803927944370993734809 70415852945958278245301107)
              ·
                refine ⟨105623779418937417367951661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70415852945958278245301107 105623779418937417367951661)
                ·
                  refine ⟨39608917282101531512981873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 105623779418937417367951661 39608917282101531512981873)
                  ·
                    refine ⟨29706687961576148634736405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39608917282101531512981873 29706687961576148634736405)
                    ·
                      refine ⟨1392500998198881967253269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 29706687961576148634736405 1392500998198881967253269)
                      ·
                        rfl

theorem cell23_2711886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 1, 3, 2, 6].length) (baseStart_2711886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2711886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2711886 prefixEnd_2711886 := by exact prefixLift 2711886
  have htrace : WordTrace (prefixWord ++ tailWord_2711886) baseStart_2711886 baseEnd_2711886 := by
    simpa [prefixWord, tailWord_2711886, baseEnd_2711886] using wordTrace_append hprefix tailTrace_2711886
  have hstable : (prefixWord ++ tailWord_2711886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2711886).length < 2 ^ (prefixWord ++ tailWord_2711886).sum := by decide
  have hdescent : baseEnd_2711886 < baseStart_2711886 := by decide
  rcases family_descends (prefixWord ++ tailWord_2711886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2711913 : List Nat := [1, 2, 1, 1, 1, 3, 5, 3, 1, 5]
def baseStart_2711913 : Nat := 118140960795 + 2711913 * 2 ^ 59
def prefixEnd_2711913 : Nat := 4983230072969 + 3 ^ 40 * 2711913 * 2
def baseEnd_2711913 : Nat := 464171620725517787205215

theorem tailTrace_2711913 : CollatzResearch.WordTrace tailWord_2711913 prefixEnd_2711913 464171620725517787205215 := by
  unfold tailWord_2711913
  simp only [CollatzResearch.WordTrace]
  refine ⟨98911593024209833711628393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65941062016139889141085595 98911593024209833711628393)
  ·
    refine ⟨74183694768157375283721295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98911593024209833711628393 74183694768157375283721295)
    ·
      refine ⟨111275542152236062925581943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74183694768157375283721295 111275542152236062925581943)
      ·
        refine ⟨166913313228354094388372915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111275542152236062925581943 166913313228354094388372915)
        ·
          refine ⟨250369969842531141582559373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166913313228354094388372915 250369969842531141582559373)
          ·
            refine ⟨93888738690949178093459765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 250369969842531141582559373 93888738690949178093459765)
            ·
              refine ⟨8802069252276485446261853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 93888738690949178093459765 8802069252276485446261853)
              ·
                refine ⟨3300775969603682042348195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8802069252276485446261853 3300775969603682042348195)
                ·
                  refine ⟨4951163954405523063522293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3300775969603682042348195 4951163954405523063522293)
                  ·
                    refine ⟨464171620725517787205215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4951163954405523063522293 464171620725517787205215)
                    ·
                      rfl

theorem cell23_2711913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 3, 1, 5].length) (baseStart_2711913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2711913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2711913 prefixEnd_2711913 := by exact prefixLift 2711913
  have htrace : WordTrace (prefixWord ++ tailWord_2711913) baseStart_2711913 baseEnd_2711913 := by
    simpa [prefixWord, tailWord_2711913, baseEnd_2711913] using wordTrace_append hprefix tailTrace_2711913
  have hstable : (prefixWord ++ tailWord_2711913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2711913).length < 2 ^ (prefixWord ++ tailWord_2711913).sum := by decide
  have hdescent : baseEnd_2711913 < baseStart_2711913 := by decide
  rcases family_descends (prefixWord ++ tailWord_2711913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2711960 : List Nat := [2, 1, 2, 5, 1, 1, 1, 2, 4, 4]
def baseStart_2711960 : Nat := 118140960795 + 2711960 * 2 ^ 59
def prefixEnd_2711960 : Nat := 4983230072969 + 3 ^ 40 * 2711960 * 2
def baseEnd_2711960 : Nat := 464179665255771559242643

theorem tailTrace_2711960 : CollatzResearch.WordTrace tailWord_2711960 prefixEnd_2711960 464179665255771559242643 := by
  unfold tailWord_2711960
  simp only [CollatzResearch.WordTrace]
  refine ⟨49456653627519780369294667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65942204836693040492392889 49456653627519780369294667)
  ·
    refine ⟨74184980441279670553942001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49456653627519780369294667 74184980441279670553942001)
    ·
      refine ⟨55638735330959752915456501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74184980441279670553942001 55638735330959752915456501)
      ·
        refine ⟨5216131437277476835824047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 55638735330959752915456501 5216131437277476835824047)
        ·
          refine ⟨7824197155916215253736071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5216131437277476835824047 7824197155916215253736071)
          ·
            refine ⟨11736295733874322880604107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7824197155916215253736071 11736295733874322880604107)
            ·
              refine ⟨17604443600811484320906161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11736295733874322880604107 17604443600811484320906161)
              ·
                refine ⟨13203332700608613240679621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17604443600811484320906161 13203332700608613240679621)
                ·
                  refine ⟨2475624881364114982627429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13203332700608613240679621 2475624881364114982627429)
                  ·
                    refine ⟨464179665255771559242643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2475624881364114982627429 464179665255771559242643)
                    ·
                      rfl

theorem cell23_2711960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 2, 4, 4].length) (baseStart_2711960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2711960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2711960 prefixEnd_2711960 := by exact prefixLift 2711960
  have htrace : WordTrace (prefixWord ++ tailWord_2711960) baseStart_2711960 baseEnd_2711960 := by
    simpa [prefixWord, tailWord_2711960, baseEnd_2711960] using wordTrace_append hprefix tailTrace_2711960
  have hstable : (prefixWord ++ tailWord_2711960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2711960).length < 2 ^ (prefixWord ++ tailWord_2711960).sum := by decide
  have hdescent : baseEnd_2711960 < baseStart_2711960 := by decide
  rcases family_descends (prefixWord ++ tailWord_2711960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2711970 : List Nat := [3, 3, 1, 2, 1, 1, 4, 1, 1, 1, 5]
def baseStart_2711970 : Nat := 118140960795 + 2711970 * 2 ^ 59
def prefixEnd_2711970 : Nat := 4983230072969 + 3 ^ 40 * 2711970 * 2
def baseEnd_2711970 : Nat := 1392544130573859638602883

theorem tailTrace_2711970 : CollatzResearch.WordTrace tailWord_2711970 prefixEnd_2711970 1392544130573859638602883 := by
  unfold tailWord_2711970
  simp only [CollatzResearch.WordTrace]
  refine ⟨24728417996250833111613341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65942447990002221630968909 24728417996250833111613341)
  ·
    refine ⟨9273156748594062416855003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24728417996250833111613341 9273156748594062416855003)
    ·
      refine ⟨13909735122891093625282505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9273156748594062416855003 13909735122891093625282505)
      ·
        refine ⟨10432301342168320218961879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13909735122891093625282505 10432301342168320218961879)
        ·
          refine ⟨15648452013252480328442819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10432301342168320218961879 15648452013252480328442819)
          ·
            refine ⟨23472678019878720492664229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15648452013252480328442819 23472678019878720492664229)
            ·
              refine ⟨4401127128727260092374543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23472678019878720492664229 4401127128727260092374543)
              ·
                refine ⟨6601690693090890138561815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4401127128727260092374543 6601690693090890138561815)
                ·
                  refine ⟨9902536039636335207842723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6601690693090890138561815 9902536039636335207842723)
                  ·
                    refine ⟨14853804059454502811764085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9902536039636335207842723 14853804059454502811764085)
                    ·
                      refine ⟨1392544130573859638602883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14853804059454502811764085 1392544130573859638602883)
                      ·
                        rfl

theorem cell23_2711970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 4, 1, 1, 1, 5].length) (baseStart_2711970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2711970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2711970 prefixEnd_2711970 := by exact prefixLift 2711970
  have htrace : WordTrace (prefixWord ++ tailWord_2711970) baseStart_2711970 baseEnd_2711970 := by
    simpa [prefixWord, tailWord_2711970, baseEnd_2711970] using wordTrace_append hprefix tailTrace_2711970
  have hstable : (prefixWord ++ tailWord_2711970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2711970).length < 2 ^ (prefixWord ++ tailWord_2711970).sum := by decide
  have hdescent : baseEnd_2711970 < baseStart_2711970 := by decide
  rcases family_descends (prefixWord ++ tailWord_2711970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2711978 : List Nat := [3, 1, 6, 1, 1, 2, 1, 1, 3, 1, 3]
def baseStart_2711978 : Nat := 118140960795 + 2711978 * 2 ^ 59
def prefixEnd_2711978 : Nat := 4983230072969 + 3 ^ 40 * 2711978 * 2
def baseEnd_2711978 : Nat := 1392548238419095607302847

theorem tailTrace_2711978 : CollatzResearch.WordTrace tailWord_2711978 prefixEnd_2711978 1392548238419095607302847 := by
  unfold tailWord_2711978
  simp only [CollatzResearch.WordTrace]
  refine ⟨24728490942243587453186147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65942642512649566541829725 24728490942243587453186147)
  ·
    refine ⟨37092736413365381179779221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24728490942243587453186147 37092736413365381179779221)
    ·
      refine ⟨1738722019376502242802151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 37092736413365381179779221 1738722019376502242802151)
      ·
        refine ⟨2608083029064753364203227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1738722019376502242802151 2608083029064753364203227)
        ·
          refine ⟨3912124543597130046304841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2608083029064753364203227 3912124543597130046304841)
          ·
            refine ⟨2934093407697847534728631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3912124543597130046304841 2934093407697847534728631)
            ·
              refine ⟨4401140111546771302092947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2934093407697847534728631 4401140111546771302092947)
              ·
                refine ⟨6601710167320156953139421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4401140111546771302092947 6601710167320156953139421)
                ·
                  refine ⟨2475641312745058857427283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6601710167320156953139421 2475641312745058857427283)
                  ·
                    refine ⟨3713461969117588286140925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2475641312745058857427283 3713461969117588286140925)
                    ·
                      refine ⟨1392548238419095607302847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3713461969117588286140925 1392548238419095607302847)
                      ·
                        rfl

theorem cell23_2711978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_2711978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2711978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2711978 prefixEnd_2711978 := by exact prefixLift 2711978
  have htrace : WordTrace (prefixWord ++ tailWord_2711978) baseStart_2711978 baseEnd_2711978 := by
    simpa [prefixWord, tailWord_2711978, baseEnd_2711978] using wordTrace_append hprefix tailTrace_2711978
  have hstable : (prefixWord ++ tailWord_2711978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2711978).length < 2 ^ (prefixWord ++ tailWord_2711978).sum := by decide
  have hdescent : baseEnd_2711978 < baseStart_2711978 := by decide
  rcases family_descends (prefixWord ++ tailWord_2711978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2712033 : List Nat := [1, 2, 3, 1, 2, 2, 2, 2, 2, 6]
def baseStart_2712033 : Nat := 118140960795 + 2712033 * 2 ^ 59
def prefixEnd_2712033 : Nat := 4983230072969 + 3 ^ 40 * 2712033 * 2
def baseEnd_2712033 : Nat := 464192159951697630705031

theorem tailTrace_2712033 : CollatzResearch.WordTrace tailWord_2712033 prefixEnd_2712033 464192159951697630705031 := by
  unfold tailWord_2712033
  simp only [CollatzResearch.WordTrace]
  refine ⟨98915969783775094205996753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65943979855850062803997835 98915969783775094205996753)
  ·
    refine ⟨74186977337831320654497565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98915969783775094205996753 74186977337831320654497565)
    ·
      refine ⟨27820116501686745245436587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74186977337831320654497565 27820116501686745245436587)
      ·
        refine ⟨41730174752530117868154881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27820116501686745245436587 41730174752530117868154881)
        ·
          refine ⟨31297631064397588401116161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41730174752530117868154881 31297631064397588401116161)
          ·
            refine ⟨23473223298298191300837121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31297631064397588401116161 23473223298298191300837121)
            ·
              refine ⟨17604917473723643475627841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23473223298298191300837121 17604917473723643475627841)
              ·
                refine ⟨13203688105292732606720881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17604917473723643475627841 13203688105292732606720881)
                ·
                  refine ⟨9902766078969549455040661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13203688105292732606720881 9902766078969549455040661)
                  ·
                    refine ⟨464192159951697630705031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9902766078969549455040661 464192159951697630705031)
                    ·
                      rfl

theorem cell23_2712033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 2, 2, 6].length) (baseStart_2712033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2712033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2712033 prefixEnd_2712033 := by exact prefixLift 2712033
  have htrace : WordTrace (prefixWord ++ tailWord_2712033) baseStart_2712033 baseEnd_2712033 := by
    simpa [prefixWord, tailWord_2712033, baseEnd_2712033] using wordTrace_append hprefix tailTrace_2712033
  have hstable : (prefixWord ++ tailWord_2712033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2712033).length < 2 ^ (prefixWord ++ tailWord_2712033).sum := by decide
  have hdescent : baseEnd_2712033 < baseStart_2712033 := by decide
  rcases family_descends (prefixWord ++ tailWord_2712033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2712035 : List Nat := [1, 1, 1, 6, 4, 1, 2, 2, 1, 2, 2]
def baseStart_2712035 : Nat := 118140960795 + 2712035 * 2 ^ 59
def prefixEnd_2712035 : Nat := 4983230072969 + 3 ^ 40 * 2712035 * 2
def baseEnd_2712035 : Nat := 1392577506816401884290085

theorem tailTrace_2712035 : CollatzResearch.WordTrace tailWord_2712035 prefixEnd_2712035 1392577506816401884290085 := by
  unfold tailWord_2712035
  simp only [CollatzResearch.WordTrace]
  refine ⟨98916042729767848547569559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65944028486511899031713039 98916042729767848547569559)
  ·
    refine ⟨148374064094651772821354339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98916042729767848547569559 148374064094651772821354339)
    ·
      refine ⟨222561096141977659232031509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148374064094651772821354339 222561096141977659232031509)
      ·
        refine ⟨10432551381655202776501477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 222561096141977659232031509 10432551381655202776501477)
        ·
          refine ⟨1956103384060350520594027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10432551381655202776501477 1956103384060350520594027)
          ·
            refine ⟨2934155076090525780891041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1956103384060350520594027 2934155076090525780891041)
            ·
              refine ⟨2200616307067894335668281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2934155076090525780891041 2200616307067894335668281)
              ·
                refine ⟨1650462230300920751751211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2200616307067894335668281 1650462230300920751751211)
                ·
                  refine ⟨2475693345451381127626817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1650462230300920751751211 2475693345451381127626817)
                  ·
                    refine ⟨1856770009088535845720113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2475693345451381127626817 1856770009088535845720113)
                    ·
                      refine ⟨1392577506816401884290085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1856770009088535845720113 1392577506816401884290085)
                      ·
                        rfl

theorem cell23_2712035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 2, 2, 1, 2, 2].length) (baseStart_2712035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2712035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2712035 prefixEnd_2712035 := by exact prefixLift 2712035
  have htrace : WordTrace (prefixWord ++ tailWord_2712035) baseStart_2712035 baseEnd_2712035 := by
    simpa [prefixWord, tailWord_2712035, baseEnd_2712035] using wordTrace_append hprefix tailTrace_2712035
  have hstable : (prefixWord ++ tailWord_2712035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2712035).length < 2 ^ (prefixWord ++ tailWord_2712035).sum := by decide
  have hdescent : baseEnd_2712035 < baseStart_2712035 := by decide
  rcases family_descends (prefixWord ++ tailWord_2712035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2712043 : List Nat := [1, 1, 1, 1, 2, 3, 3, 1, 1, 6, 3]
def baseStart_2712043 : Nat := 118140960795 + 2712043 * 2 ^ 59
def prefixEnd_2712043 : Nat := 4983230072969 + 3 ^ 40 * 2712043 * 2
def baseEnd_2712043 : Nat := 1392581614661637852990047

theorem tailTrace_2712043 : CollatzResearch.WordTrace tailWord_2712043 prefixEnd_2712043 1392581614661637852990047 := by
  unfold tailWord_2712043
  simp only [CollatzResearch.WordTrace]
  refine ⟨98916334513738865913860783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65944223009159243942573855 98916334513738865913860783)
  ·
    refine ⟨148374501770608298870791175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98916334513738865913860783 148374501770608298870791175)
    ·
      refine ⟨222561752655912448306186763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148374501770608298870791175 222561752655912448306186763)
      ·
        refine ⟨333842628983868672459280145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222561752655912448306186763 333842628983868672459280145)
        ·
          refine ⟨250381971737901504344460109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 333842628983868672459280145 250381971737901504344460109)
          ·
            refine ⟨93893239401713064129172541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 250381971737901504344460109 93893239401713064129172541)
            ·
              refine ⟨35209964775642399048439703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 93893239401713064129172541 35209964775642399048439703)
              ·
                refine ⟨52814947163463598572659555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35209964775642399048439703 52814947163463598572659555)
                ·
                  refine ⟨79222420745195397858989333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52814947163463598572659555 79222420745195397858989333)
                  ·
                    refine ⟨3713550972431034274640125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 79222420745195397858989333 3713550972431034274640125)
                    ·
                      refine ⟨1392581614661637852990047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3713550972431034274640125 1392581614661637852990047)
                      ·
                        rfl

theorem cell23_2712043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 1, 1, 6, 3].length) (baseStart_2712043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2712043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2712043 prefixEnd_2712043 := by exact prefixLift 2712043
  have htrace : WordTrace (prefixWord ++ tailWord_2712043) baseStart_2712043 baseEnd_2712043 := by
    simpa [prefixWord, tailWord_2712043, baseEnd_2712043] using wordTrace_append hprefix tailTrace_2712043
  have hstable : (prefixWord ++ tailWord_2712043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2712043).length < 2 ^ (prefixWord ++ tailWord_2712043).sum := by decide
  have hdescent : baseEnd_2712043 < baseStart_2712043 := by decide
  rcases family_descends (prefixWord ++ tailWord_2712043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2712063 : List Nat := [1, 1, 2, 2, 1, 2, 5, 2, 7]
def baseStart_2712063 : Nat := 118140960795 + 2712063 * 2 ^ 59
def prefixEnd_2712063 : Nat := 4983230072969 + 3 ^ 40 * 2712063 * 2
def baseEnd_2712063 : Nat := 154732431586080863859995

theorem tailTrace_2712063 : CollatzResearch.WordTrace tailWord_2712063 prefixEnd_2712063 154732431586080863859995 := by
  unfold tailWord_2712063
  simp only [CollatzResearch.WordTrace]
  refine ⟨98917063973666409329588843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65944709315777606219725895 98917063973666409329588843)
  ·
    refine ⟨148375595960499613994383265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98917063973666409329588843 148375595960499613994383265)
    ·
      refine ⟨111281696970374710495787449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148375595960499613994383265 111281696970374710495787449)
      ·
        refine ⟨83461272727781032871840587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111281696970374710495787449 83461272727781032871840587)
        ·
          refine ⟨125191909091671549307760881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83461272727781032871840587 125191909091671549307760881)
          ·
            refine ⟨93893931818753661980820661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 125191909091671549307760881 93893931818753661980820661)
            ·
              refine ⟨8802556108008155810701937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 93893931818753661980820661 8802556108008155810701937)
              ·
                refine ⟨6601917081006116858026453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8802556108008155810701937 6601917081006116858026453)
                ·
                  refine ⟨154732431586080863859995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6601917081006116858026453 154732431586080863859995)
                  ·
                    rfl

theorem cell23_2712063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 2, 7].length) (baseStart_2712063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2712063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2712063 prefixEnd_2712063 := by exact prefixLift 2712063
  have htrace : WordTrace (prefixWord ++ tailWord_2712063) baseStart_2712063 baseEnd_2712063 := by
    simpa [prefixWord, tailWord_2712063, baseEnd_2712063] using wordTrace_append hprefix tailTrace_2712063
  have hstable : (prefixWord ++ tailWord_2712063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2712063).length < 2 ^ (prefixWord ++ tailWord_2712063).sum := by decide
  have hdescent : baseEnd_2712063 < baseStart_2712063 := by decide
  rcases family_descends (prefixWord ++ tailWord_2712063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2712090 : List Nat := [3, 1, 1, 3, 1, 1, 3, 2, 2, 3, 3]
def baseStart_2712090 : Nat := 118140960795 + 2712090 * 2 ^ 59
def prefixEnd_2712090 : Nat := 4983230072969 + 3 ^ 40 * 2712090 * 2
def baseEnd_2712090 : Nat := 1392605748252399169102331

theorem tailTrace_2712090 : CollatzResearch.WordTrace tailWord_2712090 prefixEnd_2712090 1392605748252399169102331 := by
  unfold tailWord_2712090
  simp only [CollatzResearch.WordTrace]
  refine ⟨24729512186142148235205431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65945365829712395293881149 24729512186142148235205431)
  ·
    refine ⟨37094268279213222352808147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24729512186142148235205431 37094268279213222352808147)
    ·
      refine ⟨55641402418819833529212221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37094268279213222352808147 55641402418819833529212221)
      ·
        refine ⟨20865525907057437573454583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55641402418819833529212221 20865525907057437573454583)
        ·
          refine ⟨31298288860586156360181875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20865525907057437573454583 31298288860586156360181875)
          ·
            refine ⟨46947433290879234540272813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31298288860586156360181875 46947433290879234540272813)
            ·
              refine ⟨17605287484079712952602305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46947433290879234540272813 17605287484079712952602305)
              ·
                refine ⟨13203965613059784714451729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17605287484079712952602305 13203965613059784714451729)
                ·
                  refine ⟨9902974209794838535838797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13203965613059784714451729 9902974209794838535838797)
                  ·
                    refine ⟨3713615328673064450939549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9902974209794838535838797 3713615328673064450939549)
                    ·
                      refine ⟨1392605748252399169102331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3713615328673064450939549 1392605748252399169102331)
                      ·
                        rfl

theorem cell23_2712090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 2, 2, 3, 3].length) (baseStart_2712090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2712090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2712090 prefixEnd_2712090 := by exact prefixLift 2712090
  have htrace : WordTrace (prefixWord ++ tailWord_2712090) baseStart_2712090 baseEnd_2712090 := by
    simpa [prefixWord, tailWord_2712090, baseEnd_2712090] using wordTrace_append hprefix tailTrace_2712090
  have hstable : (prefixWord ++ tailWord_2712090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2712090).length < 2 ^ (prefixWord ++ tailWord_2712090).sum := by decide
  have hdescent : baseEnd_2712090 < baseStart_2712090 := by decide
  rcases family_descends (prefixWord ++ tailWord_2712090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2712143 : List Nat := [1, 1, 2, 1, 1, 2, 4, 1, 1, 3, 6]
def baseStart_2712143 : Nat := 118140960795 + 2712143 * 2 ^ 59
def prefixEnd_2712143 : Nat := 4983230072969 + 3 ^ 40 * 2712143 * 2
def baseEnd_2712143 : Nat := 1392632962727087461739587

theorem tailTrace_2712143 : CollatzResearch.WordTrace tailWord_2712143 prefixEnd_2712143 1392632962727087461739587 := by
  unfold tailWord_2712143
  simp only [CollatzResearch.WordTrace]
  refine ⟨98919981813376582992501083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65946654542251055328334055 98919981813376582992501083)
  ·
    refine ⟨148379972720064874488751625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98919981813376582992501083 148379972720064874488751625)
    ·
      refine ⟨111284979540048655866563719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148379972720064874488751625 111284979540048655866563719)
      ·
        refine ⟨166927469310072983799845579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111284979540048655866563719 166927469310072983799845579)
        ·
          refine ⟨250391203965109475699768369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166927469310072983799845579 250391203965109475699768369)
          ·
            refine ⟨187793402973832106774826277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 250391203965109475699768369 187793402973832106774826277)
            ·
              refine ⟨35211263057593520020279927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 187793402973832106774826277 35211263057593520020279927)
              ·
                refine ⟨52816894586390280030419891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35211263057593520020279927 52816894586390280030419891)
                ·
                  refine ⟨79225341879585420045629837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52816894586390280030419891 79225341879585420045629837)
                  ·
                    refine ⟨29709503204844532517111189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 79225341879585420045629837 29709503204844532517111189)
                    ·
                      refine ⟨1392632962727087461739587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 29709503204844532517111189 1392632962727087461739587)
                      ·
                        rfl

theorem cell23_2712143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 1, 1, 3, 6].length) (baseStart_2712143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2712143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2712143 prefixEnd_2712143 := by exact prefixLift 2712143
  have htrace : WordTrace (prefixWord ++ tailWord_2712143) baseStart_2712143 baseEnd_2712143 := by
    simpa [prefixWord, tailWord_2712143, baseEnd_2712143] using wordTrace_append hprefix tailTrace_2712143
  have hstable : (prefixWord ++ tailWord_2712143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2712143).length < 2 ^ (prefixWord ++ tailWord_2712143).sum := by decide
  have hdescent : baseEnd_2712143 < baseStart_2712143 := by decide
  rcases family_descends (prefixWord ++ tailWord_2712143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2712241 : List Nat := [1, 2, 2, 6, 1, 1, 1, 1, 1, 5, 2]
def baseStart_2712241 : Nat := 118140960795 + 2712241 * 2 ^ 59
def prefixEnd_2712241 : Nat := 4983230072969 + 3 ^ 40 * 2712241 * 2
def baseEnd_2712241 : Nat := 1392683283831228078314137

theorem tailTrace_2712241 : CollatzResearch.WordTrace tailWord_2712241 prefixEnd_2712241 1392683283831228078314137 := by
  unfold tailWord_2712241
  simp only [CollatzResearch.WordTrace]
  refine ⟨98923556167021545729568577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65949037444681030486379051 98923556167021545729568577)
  ·
    refine ⟨74192667125266159297176433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98923556167021545729568577 74192667125266159297176433)
    ·
      refine ⟨55644500343949619472882325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74192667125266159297176433 55644500343949619472882325)
      ·
        refine ⟨2608335953622638412791359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 55644500343949619472882325 2608335953622638412791359)
        ·
          refine ⟨3912503930433957619187039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2608335953622638412791359 3912503930433957619187039)
          ·
            refine ⟨5868755895650936428780559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3912503930433957619187039 5868755895650936428780559)
            ·
              refine ⟨8803133843476404643170839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5868755895650936428780559 8803133843476404643170839)
              ·
                refine ⟨13204700765214606964756259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8803133843476404643170839 13204700765214606964756259)
                ·
                  refine ⟨19807051147821910447134389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13204700765214606964756259 19807051147821910447134389)
                  ·
                    refine ⟨1856911045108304104418849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 19807051147821910447134389 1856911045108304104418849)
                    ·
                      refine ⟨1392683283831228078314137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1856911045108304104418849 1392683283831228078314137)
                      ·
                        rfl

theorem cell23_2712241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 1, 1, 5, 2].length) (baseStart_2712241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2712241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2712241 prefixEnd_2712241 := by exact prefixLift 2712241
  have htrace : WordTrace (prefixWord ++ tailWord_2712241) baseStart_2712241 baseEnd_2712241 := by
    simpa [prefixWord, tailWord_2712241, baseEnd_2712241] using wordTrace_append hprefix tailTrace_2712241
  have hstable : (prefixWord ++ tailWord_2712241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2712241).length < 2 ^ (prefixWord ++ tailWord_2712241).sum := by decide
  have hdescent : baseEnd_2712241 < baseStart_2712241 := by decide
  rcases family_descends (prefixWord ++ tailWord_2712241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2712254 : List Nat := [4, 2, 1, 1, 2, 1, 3, 3, 1, 1, 4]
def baseStart_2712254 : Nat := 118140960795 + 2712254 * 2 ^ 59
def prefixEnd_2712254 : Nat := 4983230072969 + 3 ^ 40 * 2712254 * 2
def baseEnd_2712254 : Nat := 1392689959079736527451577

theorem tailTrace_2712254 : CollatzResearch.WordTrace tailWord_2712254 prefixEnd_2712254 1392689959079736527451577 := by
  unfold tailWord_2712254
  simp only [CollatzResearch.WordTrace]
  refine ⟨12365503789496806118723977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65949353543982965966527877 12365503789496806118723977)
  ·
    refine ⟨9274127842122604589042983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12365503789496806118723977 9274127842122604589042983)
    ·
      refine ⟨13911191763183906883564475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9274127842122604589042983 13911191763183906883564475)
      ·
        refine ⟨20866787644775860325346713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13911191763183906883564475 20866787644775860325346713)
        ·
          refine ⟨15650090733581895244010035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20866787644775860325346713 15650090733581895244010035)
          ·
            refine ⟨23475136100372842866015053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15650090733581895244010035 23475136100372842866015053)
            ·
              refine ⟨8803176037639816074755645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23475136100372842866015053 8803176037639816074755645)
              ·
                refine ⟨3301191014114931028033367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8803176037639816074755645 3301191014114931028033367)
                ·
                  refine ⟨4951786521172396542050051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3301191014114931028033367 4951786521172396542050051)
                  ·
                    refine ⟨7427679781758594813075077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4951786521172396542050051 7427679781758594813075077)
                    ·
                      refine ⟨1392689959079736527451577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7427679781758594813075077 1392689959079736527451577)
                      ·
                        rfl

theorem cell23_2712254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 3, 1, 1, 4].length) (baseStart_2712254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2712254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2712254 prefixEnd_2712254 := by exact prefixLift 2712254
  have htrace : WordTrace (prefixWord ++ tailWord_2712254) baseStart_2712254 baseEnd_2712254 := by
    simpa [prefixWord, tailWord_2712254, baseEnd_2712254] using wordTrace_append hprefix tailTrace_2712254
  have hstable : (prefixWord ++ tailWord_2712254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2712254).length < 2 ^ (prefixWord ++ tailWord_2712254).sum := by decide
  have hdescent : baseEnd_2712254 < baseStart_2712254 := by decide
  rcases family_descends (prefixWord ++ tailWord_2712254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2712264 : List Nat := [2, 1, 3, 1, 2, 3, 3, 2, 2, 4]
def baseStart_2712264 : Nat := 118140960795 + 2712264 * 2 ^ 59
def prefixEnd_2712264 : Nat := 4983230072969 + 3 ^ 40 * 2712264 * 2
def baseEnd_2712264 : Nat := 464231697962093829442177

theorem tailTrace_2712264 : CollatzResearch.WordTrace tailWord_2712264 prefixEnd_2712264 464231697962093829442177 := by
  unfold tailWord_2712264
  simp only [CollatzResearch.WordTrace]
  refine ⟨49462197522969110328827923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65949596697292147105103897 49462197522969110328827923)
  ·
    refine ⟨74193296284453665493241885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49462197522969110328827923 74193296284453665493241885)
    ·
      refine ⟨27822486106670124559965707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74193296284453665493241885 27822486106670124559965707)
      ·
        refine ⟨41733729160005186839948561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27822486106670124559965707 41733729160005186839948561)
        ·
          refine ⟨31300296870003890129961421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41733729160005186839948561 31300296870003890129961421)
          ·
            refine ⟨11737611326251458798735533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31300296870003890129961421 11737611326251458798735533)
            ·
              refine ⟨4401604247344297049525825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11737611326251458798735533 4401604247344297049525825)
              ·
                refine ⟨3301203185508222787144369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4401604247344297049525825 3301203185508222787144369)
                ·
                  refine ⟨2475902389131167090358277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3301203185508222787144369 2475902389131167090358277)
                  ·
                    refine ⟨464231697962093829442177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2475902389131167090358277 464231697962093829442177)
                    ·
                      rfl

theorem cell23_2712264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 3, 2, 2, 4].length) (baseStart_2712264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2712264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2712264 prefixEnd_2712264 := by exact prefixLift 2712264
  have htrace : WordTrace (prefixWord ++ tailWord_2712264) baseStart_2712264 baseEnd_2712264 := by
    simpa [prefixWord, tailWord_2712264, baseEnd_2712264] using wordTrace_append hprefix tailTrace_2712264
  have hstable : (prefixWord ++ tailWord_2712264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2712264).length < 2 ^ (prefixWord ++ tailWord_2712264).sum := by decide
  have hdescent : baseEnd_2712264 < baseStart_2712264 := by decide
  rcases family_descends (prefixWord ++ tailWord_2712264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2712274 : List Nat := [3, 2, 2, 2, 3, 1, 1, 2, 1, 1, 5]
def baseStart_2712274 : Nat := 118140960795 + 2712274 * 2 ^ 59
def prefixEnd_2712274 : Nat := 4983230072969 + 3 ^ 40 * 2712274 * 2
def baseEnd_2712274 : Nat := 1392700228692826449201485

theorem tailTrace_2712274 : CollatzResearch.WordTrace tailWord_2712274 prefixEnd_2712274 1392700228692826449201485 := by
  unfold tailWord_2712274
  simp only [CollatzResearch.WordTrace]
  refine ⟨24731189943975498091379969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65949839850601328243679917 24731189943975498091379969)
  ·
    refine ⟨18548392457981623568534977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24731189943975498091379969 18548392457981623568534977)
    ·
      refine ⟨13911294343486217676401233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18548392457981623568534977 13911294343486217676401233)
      ·
        refine ⟨10433470757614663257300925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13911294343486217676401233 10433470757614663257300925)
        ·
          refine ⟨3912551534105498721487847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10433470757614663257300925 3912551534105498721487847)
          ·
            refine ⟨5868827301158248082231771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3912551534105498721487847 5868827301158248082231771)
            ·
              refine ⟨8803240951737372123347657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5868827301158248082231771 8803240951737372123347657)
              ·
                refine ⟨6602430713803029092510743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8803240951737372123347657 6602430713803029092510743)
                ·
                  refine ⟨9903646070704543638766115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6602430713803029092510743 9903646070704543638766115)
                  ·
                    refine ⟨14855469106056815458149173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9903646070704543638766115 14855469106056815458149173)
                    ·
                      refine ⟨1392700228692826449201485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14855469106056815458149173 1392700228692826449201485)
                      ·
                        rfl

theorem cell23_2712274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 2, 1, 1, 5].length) (baseStart_2712274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2712274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2712274 prefixEnd_2712274 := by exact prefixLift 2712274
  have htrace : WordTrace (prefixWord ++ tailWord_2712274) baseStart_2712274 baseEnd_2712274 := by
    simpa [prefixWord, tailWord_2712274, baseEnd_2712274] using wordTrace_append hprefix tailTrace_2712274
  have hstable : (prefixWord ++ tailWord_2712274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2712274).length < 2 ^ (prefixWord ++ tailWord_2712274).sum := by decide
  have hdescent : baseEnd_2712274 < baseStart_2712274 := by decide
  rcases family_descends (prefixWord ++ tailWord_2712274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2712284 : List Nat := [2, 2, 5, 1, 1, 2, 1, 1, 1, 1, 6]
def baseStart_2712284 : Nat := 118140960795 + 2712284 * 2 ^ 59
def prefixEnd_2712284 : Nat := 4983230072969 + 3 ^ 40 * 2712284 * 2
def baseEnd_2712284 : Nat := 1392705363499371410076439

theorem tailTrace_2712284 : CollatzResearch.WordTrace tailWord_2712284 prefixEnd_2712284 1392705363499371410076439 := by
  unfold tailWord_2712284
  simp only [CollatzResearch.WordTrace]
  refine ⟨49462562252932882036691953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65950083003910509382255937 49462562252932882036691953)
  ·
    refine ⟨37096921689699661527518965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49462562252932882036691953 37096921689699661527518965)
    ·
      refine ⟨3477836408409343268204903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 37096921689699661527518965 3477836408409343268204903)
      ·
        refine ⟨5216754612614014902307355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3477836408409343268204903 5216754612614014902307355)
        ·
          refine ⟨7825131918921022353461033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5216754612614014902307355 7825131918921022353461033)
          ·
            refine ⟨5868848939190766765095775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7825131918921022353461033 5868848939190766765095775)
            ·
              refine ⟨8803273408786150147643663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5868848939190766765095775 8803273408786150147643663)
              ·
                refine ⟨13204910113179225221465495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8803273408786150147643663 13204910113179225221465495)
                ·
                  refine ⟨19807365169768837832198243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13204910113179225221465495 19807365169768837832198243)
                  ·
                    refine ⟨29711047754653256748297365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19807365169768837832198243 29711047754653256748297365)
                    ·
                      refine ⟨1392705363499371410076439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 29711047754653256748297365 1392705363499371410076439)
                      ·
                        rfl

theorem cell23_2712284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_2712284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2712284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2712284 prefixEnd_2712284 := by exact prefixLift 2712284
  have htrace : WordTrace (prefixWord ++ tailWord_2712284) baseStart_2712284 baseEnd_2712284 := by
    simpa [prefixWord, tailWord_2712284, baseEnd_2712284] using wordTrace_append hprefix tailTrace_2712284
  have hstable : (prefixWord ++ tailWord_2712284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2712284).length < 2 ^ (prefixWord ++ tailWord_2712284).sum := by decide
  have hdescent : baseEnd_2712284 < baseStart_2712284 := by decide
  rcases family_descends (prefixWord ++ tailWord_2712284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2712291 : List Nat := [1, 1, 1, 7, 1, 2, 2, 2, 1, 2, 3]
def baseStart_2712291 : Nat := 118140960795 + 2712291 * 2 ^ 59
def prefixEnd_2712291 : Nat := 4983230072969 + 3 ^ 40 * 2712291 * 2
def baseEnd_2712291 : Nat := 1392708957863952882688907

theorem tailTrace_2712291 : CollatzResearch.WordTrace tailWord_2712291 prefixEnd_2712291 1392708957863952882688907 := by
  unfold tailWord_2712291
  simp only [CollatzResearch.WordTrace]
  refine ⟨98925379816840404268888727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65950253211226936179259151 98925379816840404268888727)
  ·
    refine ⟨148388069725260606403333091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98925379816840404268888727 148388069725260606403333091)
    ·
      refine ⟨222582104587890909604999637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148388069725260606403333091 222582104587890909604999637)
      ·
        refine ⟨5216768076278693193867179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 222582104587890909604999637 5216768076278693193867179)
        ·
          refine ⟨7825152114418039790800769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5216768076278693193867179 7825152114418039790800769)
          ·
            refine ⟨5868864085813529843100577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7825152114418039790800769 5868864085813529843100577)
            ·
              refine ⟨4401648064360147382325433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5868864085813529843100577 4401648064360147382325433)
              ·
                refine ⟨3301236048270110536744075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4401648064360147382325433 3301236048270110536744075)
                ·
                  refine ⟨4951854072405165805116113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3301236048270110536744075 4951854072405165805116113)
                  ·
                    refine ⟨3713890554303874353837085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4951854072405165805116113 3713890554303874353837085)
                    ·
                      refine ⟨1392708957863952882688907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3713890554303874353837085 1392708957863952882688907)
                      ·
                        rfl

theorem cell23_2712291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 2, 2, 1, 2, 3].length) (baseStart_2712291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2712291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2712291 prefixEnd_2712291 := by exact prefixLift 2712291
  have htrace : WordTrace (prefixWord ++ tailWord_2712291) baseStart_2712291 baseEnd_2712291 := by
    simpa [prefixWord, tailWord_2712291, baseEnd_2712291] using wordTrace_append hprefix tailTrace_2712291
  have hstable : (prefixWord ++ tailWord_2712291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2712291).length < 2 ^ (prefixWord ++ tailWord_2712291).sum := by decide
  have hdescent : baseEnd_2712291 < baseStart_2712291 := by decide
  rcases family_descends (prefixWord ++ tailWord_2712291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2712308 : List Nat := [2, 6, 1, 1, 2, 1, 2, 1, 1, 1, 5]
def baseStart_2712308 : Nat := 118140960795 + 2712308 * 2 ^ 59
def prefixEnd_2712308 : Nat := 4983230072969 + 3 ^ 40 * 2712308 * 2
def baseEnd_2712308 : Nat := 1392717687035079316176329

theorem tailTrace_2712308 : CollatzResearch.WordTrace tailWord_2712308 prefixEnd_2712308 1392717687035079316176329 := by
  unfold tailWord_2712308
  simp only [CollatzResearch.WordTrace]
  refine ⟨49462999928889408086128789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65950666571852544114838385 49462999928889408086128789)
  ·
    refine ⟨2318578121666691004037287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 49462999928889408086128789 2318578121666691004037287)
    ·
      refine ⟨3477867182500036506055931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2318578121666691004037287 3477867182500036506055931)
      ·
        refine ⟨5216800773750054759083897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3477867182500036506055931 5216800773750054759083897)
        ·
          refine ⟨3912600580312541069312923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5216800773750054759083897 3912600580312541069312923)
          ·
            refine ⟨5868900870468811603969385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3912600580312541069312923 5868900870468811603969385)
            ·
              refine ⟨4401675652851608702977039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5868900870468811603969385 4401675652851608702977039)
              ·
                refine ⟨6602513479277413054465559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4401675652851608702977039 6602513479277413054465559)
                ·
                  refine ⟨9903770218916119581698339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6602513479277413054465559 9903770218916119581698339)
                  ·
                    refine ⟨14855655328374179372547509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9903770218916119581698339 14855655328374179372547509)
                    ·
                      refine ⟨1392717687035079316176329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14855655328374179372547509 1392717687035079316176329)
                      ·
                        rfl

theorem cell23_2712308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 2, 1, 1, 1, 5].length) (baseStart_2712308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2712308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2712308 prefixEnd_2712308 := by exact prefixLift 2712308
  have htrace : WordTrace (prefixWord ++ tailWord_2712308) baseStart_2712308 baseEnd_2712308 := by
    simpa [prefixWord, tailWord_2712308, baseEnd_2712308] using wordTrace_append hprefix tailTrace_2712308
  have hstable : (prefixWord ++ tailWord_2712308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2712308).length < 2 ^ (prefixWord ++ tailWord_2712308).sum := by decide
  have hdescent : baseEnd_2712308 < baseStart_2712308 := by decide
  rcases family_descends (prefixWord ++ tailWord_2712308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2712322 : List Nat := [3, 4, 1, 1, 1, 3, 3, 2, 1, 2, 2]
def baseStart_2712322 : Nat := 118140960795 + 2712322 * 2 ^ 59
def prefixEnd_2712322 : Nat := 4983230072969 + 3 ^ 40 * 2712322 * 2
def baseEnd_2712322 : Nat := 1392724875764242261401265

theorem tailTrace_2712322 : CollatzResearch.WordTrace tailWord_2712322 prefixEnd_2712322 1392724875764242261401265 := by
  unfold tailWord_2712322
  simp only [CollatzResearch.WordTrace]
  refine ⟨24731627619932024140816805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65951006986485397708844813 24731627619932024140816805)
  ·
    refine ⟨4637180178737254526403151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24731627619932024140816805 4637180178737254526403151)
    ·
      refine ⟨6955770268105881789604727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4637180178737254526403151 6955770268105881789604727)
      ·
        refine ⟨10433655402158822684407091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6955770268105881789604727 10433655402158822684407091)
        ·
          refine ⟨15650483103238234026610637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10433655402158822684407091 15650483103238234026610637)
          ·
            refine ⟨5868931163714337759978989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15650483103238234026610637 5868931163714337759978989)
            ·
              refine ⟨2200849186392876659992121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5868931163714337759978989 2200849186392876659992121)
              ·
                refine ⟨1650636889794657494994091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2200849186392876659992121 1650636889794657494994091)
                ·
                  refine ⟨2475955334691986242491137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1650636889794657494994091 2475955334691986242491137)
                  ·
                    refine ⟨1856966501018989681868353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2475955334691986242491137 1856966501018989681868353)
                    ·
                      refine ⟨1392724875764242261401265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1856966501018989681868353 1392724875764242261401265)
                      ·
                        rfl

theorem cell23_2712322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 3, 2, 1, 2, 2].length) (baseStart_2712322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2712322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2712322 prefixEnd_2712322 := by exact prefixLift 2712322
  have htrace : WordTrace (prefixWord ++ tailWord_2712322) baseStart_2712322 baseEnd_2712322 := by
    simpa [prefixWord, tailWord_2712322, baseEnd_2712322] using wordTrace_append hprefix tailTrace_2712322
  have hstable : (prefixWord ++ tailWord_2712322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2712322).length < 2 ^ (prefixWord ++ tailWord_2712322).sum := by decide
  have hdescent : baseEnd_2712322 < baseStart_2712322 := by decide
  rcases family_descends (prefixWord ++ tailWord_2712322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2712344 : List Nat := [2, 1, 2, 3, 1, 1, 1, 5, 1, 4, 2]
def baseStart_2712344 : Nat := 118140960795 + 2712344 * 2 ^ 59
def prefixEnd_2712344 : Nat := 4983230072969 + 3 ^ 40 * 2712344 * 2
def baseEnd_2712344 : Nat := 1392736172338641175326163

theorem tailTrace_2712344 : CollatzResearch.WordTrace tailWord_2712344 prefixEnd_2712344 1392736172338641175326163 := by
  unfold tailWord_2712344
  simp only [CollatzResearch.WordTrace]
  refine ⟨49463656442824197160284043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65951541923765596213712057 49463656442824197160284043)
  ·
    refine ⟨74195484664236295740426065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49463656442824197160284043 74195484664236295740426065)
    ·
      refine ⟨55646613498177221805319549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74195484664236295740426065 55646613498177221805319549)
      ·
        refine ⟨20867480061816458176994831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55646613498177221805319549 20867480061816458176994831)
        ·
          refine ⟨31301220092724687265492247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20867480061816458176994831 31301220092724687265492247)
          ·
            refine ⟨46951830139087030898238371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31301220092724687265492247 46951830139087030898238371)
            ·
              refine ⟨70427745208630546347357557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46951830139087030898238371 70427745208630546347357557)
              ·
                refine ⟨6602601113309113720064771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 70427745208630546347357557 6602601113309113720064771)
                ·
                  refine ⟨9903901669963670580097157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6602601113309113720064771 9903901669963670580097157)
                  ·
                    refine ⟨1856981563118188233768217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9903901669963670580097157 1856981563118188233768217)
                    ·
                      refine ⟨1392736172338641175326163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1856981563118188233768217 1392736172338641175326163)
                      ·
                        rfl

theorem cell23_2712344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 5, 1, 4, 2].length) (baseStart_2712344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2712344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2712344 prefixEnd_2712344 := by exact prefixLift 2712344
  have htrace : WordTrace (prefixWord ++ tailWord_2712344) baseStart_2712344 baseEnd_2712344 := by
    simpa [prefixWord, tailWord_2712344, baseEnd_2712344] using wordTrace_append hprefix tailTrace_2712344
  have hstable : (prefixWord ++ tailWord_2712344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2712344).length < 2 ^ (prefixWord ++ tailWord_2712344).sum := by decide
  have hdescent : baseEnd_2712344 < baseStart_2712344 := by decide
  rcases family_descends (prefixWord ++ tailWord_2712344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2712348 : List Nat := [2, 2, 3, 1, 1, 5, 1, 2, 1, 3, 2]
def baseStart_2712348 : Nat := 118140960795 + 2712348 * 2 ^ 59
def prefixEnd_2712348 : Nat := 4983230072969 + 3 ^ 40 * 2712348 * 2
def baseEnd_2712348 : Nat := 1392738226261259159676145

theorem tailTrace_2712348 : CollatzResearch.WordTrace tailWord_2712348 prefixEnd_2712348 1392738226261259159676145 := by
  unfold tailWord_2712348
  simp only [CollatzResearch.WordTrace]
  refine ⟨49463729388816951501856849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65951639185089268669142465 49463729388816951501856849)
  ·
    refine ⟨37097797041612713626392637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49463729388816951501856849 37097797041612713626392637)
    ·
      refine ⟨13911673890604767609897239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37097797041612713626392637 13911673890604767609897239)
      ·
        refine ⟨20867510835907151414845859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13911673890604767609897239 20867510835907151414845859)
        ·
          refine ⟨31301266253860727122268789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20867510835907151414845859 31301266253860727122268789)
          ·
            refine ⟨2934493711299443167712699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 31301266253860727122268789 2934493711299443167712699)
            ·
              refine ⟨4401740566949164751569049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2934493711299443167712699 4401740566949164751569049)
              ·
                refine ⟨3301305425211873563676787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4401740566949164751569049 3301305425211873563676787)
                ·
                  refine ⟨4951958137817810345515181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3301305425211873563676787 4951958137817810345515181)
                  ·
                    refine ⟨1856984301681678879568193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4951958137817810345515181 1856984301681678879568193)
                    ·
                      refine ⟨1392738226261259159676145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1856984301681678879568193 1392738226261259159676145)
                      ·
                        rfl

theorem cell23_2712348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 1, 2, 1, 3, 2].length) (baseStart_2712348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2712348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2712348 prefixEnd_2712348 := by exact prefixLift 2712348
  have htrace : WordTrace (prefixWord ++ tailWord_2712348) baseStart_2712348 baseEnd_2712348 := by
    simpa [prefixWord, tailWord_2712348, baseEnd_2712348] using wordTrace_append hprefix tailTrace_2712348
  have hstable : (prefixWord ++ tailWord_2712348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2712348).length < 2 ^ (prefixWord ++ tailWord_2712348).sum := by decide
  have hdescent : baseEnd_2712348 < baseStart_2712348 := by decide
  rcases family_descends (prefixWord ++ tailWord_2712348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2712418 : List Nat := [3, 3, 2, 1, 3, 1, 2, 3, 5]
def baseStart_2712418 : Nat := 118140960795 + 2712418 * 2 ^ 59
def prefixEnd_2712418 : Nat := 4983230072969 + 3 ^ 40 * 2712418 * 2
def baseEnd_2712418 : Nat := 154752685545230431755647

theorem tailTrace_2712418 : CollatzResearch.WordTrace tailWord_2712418 prefixEnd_2712418 154752685545230431755647 := by
  unfold tailWord_2712418
  simp only [CollatzResearch.WordTrace]
  refine ⟨24732502971845076239690477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65953341258253536639174605 24732502971845076239690477)
  ·
    refine ⟨9274688614441903589883929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24732502971845076239690477 9274688614441903589883929)
    ·
      refine ⟨6956016460831427692412947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9274688614441903589883929 6956016460831427692412947)
      ·
        refine ⟨10434024691247141538619421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6956016460831427692412947 10434024691247141538619421)
        ·
          refine ⟨3912759259217678076982283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10434024691247141538619421 3912759259217678076982283)
          ·
            refine ⟨5869138888826517115473425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3912759259217678076982283 5869138888826517115473425)
            ·
              refine ⟨4401854166619887836605069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5869138888826517115473425 4401854166619887836605069)
              ·
                refine ⟨1650695312482457938726901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4401854166619887836605069 1650695312482457938726901)
                ·
                  refine ⟨154752685545230431755647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1650695312482457938726901 154752685545230431755647)
                  ·
                    rfl

theorem cell23_2712418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 2, 3, 5].length) (baseStart_2712418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2712418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2712418 prefixEnd_2712418 := by exact prefixLift 2712418
  have htrace : WordTrace (prefixWord ++ tailWord_2712418) baseStart_2712418 baseEnd_2712418 := by
    simpa [prefixWord, tailWord_2712418, baseEnd_2712418] using wordTrace_append hprefix tailTrace_2712418
  have hstable : (prefixWord ++ tailWord_2712418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2712418).length < 2 ^ (prefixWord ++ tailWord_2712418).sum := by decide
  have hdescent : baseEnd_2712418 < baseStart_2712418 := by decide
  rcases family_descends (prefixWord ++ tailWord_2712418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2712434 : List Nat := [3, 2, 1, 2, 1, 1, 2, 4, 2, 1, 4]
def baseStart_2712434 : Nat := 118140960795 + 2712434 * 2 ^ 59
def prefixEnd_2712434 : Nat := 4983230072969 + 3 ^ 40 * 2712434 * 2
def baseEnd_2712434 : Nat := 1392782385597545823200749

theorem tailTrace_2712434 : CollatzResearch.WordTrace tailWord_2712434 prefixEnd_2712434 1392782385597545823200749 := by
  unfold tailWord_2712434
  simp only [CollatzResearch.WordTrace]
  refine ⟨24732648863830584922836089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65953730303548226460896237 24732648863830584922836089)
  ·
    refine ⟨18549486647872938692127067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24732648863830584922836089 18549486647872938692127067)
    ·
      refine ⟨27824229971809408038190601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18549486647872938692127067 27824229971809408038190601)
      ·
        refine ⟨20868172478857056028642951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27824229971809408038190601 20868172478857056028642951)
        ·
          refine ⟨31302258718285584042964427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20868172478857056028642951 31302258718285584042964427)
          ·
            refine ⟨46953388077428376064446641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31302258718285584042964427 46953388077428376064446641)
            ·
              refine ⟨35215041058071282048334981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46953388077428376064446641 35215041058071282048334981)
              ·
                refine ⟨6602820198388365384062809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35215041058071282048334981 6602820198388365384062809)
                ·
                  refine ⟨4952115148791274038047107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6602820198388365384062809 4952115148791274038047107)
                  ·
                    refine ⟨7428172723186911057070661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4952115148791274038047107 7428172723186911057070661)
                    ·
                      refine ⟨1392782385597545823200749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7428172723186911057070661 1392782385597545823200749)
                      ·
                        rfl

theorem cell23_2712434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 4, 2, 1, 4].length) (baseStart_2712434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2712434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2712434 prefixEnd_2712434 := by exact prefixLift 2712434
  have htrace : WordTrace (prefixWord ++ tailWord_2712434) baseStart_2712434 baseEnd_2712434 := by
    simpa [prefixWord, tailWord_2712434, baseEnd_2712434] using wordTrace_append hprefix tailTrace_2712434
  have hstable : (prefixWord ++ tailWord_2712434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2712434).length < 2 ^ (prefixWord ++ tailWord_2712434).sum := by decide
  have hdescent : baseEnd_2712434 < baseStart_2712434 := by decide
  rcases family_descends (prefixWord ++ tailWord_2712434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2712538 : List Nat := [3, 1, 1, 2, 4, 2, 3, 1, 1, 5]
def baseStart_2712538 : Nat := 118140960795 + 2712538 * 2 ^ 59
def prefixEnd_2712538 : Nat := 4983230072969 + 3 ^ 40 * 2712538 * 2
def baseEnd_2712538 : Nat := 464278595861871138766757

theorem tailTrace_2712538 : CollatzResearch.WordTrace tailWord_2712538 prefixEnd_2712538 464278595861871138766757 := by
  unfold tailWord_2712538
  simp only [CollatzResearch.WordTrace]
  refine ⟨24733597161736391363282567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65956259097963710302086845 24733597161736391363282567)
  ·
    refine ⟨37100395742604587044923851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24733597161736391363282567 37100395742604587044923851)
    ·
      refine ⟨55650593613906880567385777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37100395742604587044923851 55650593613906880567385777)
      ·
        refine ⟨41737945210430160425539333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55650593613906880567385777 41737945210430160425539333)
        ·
          refine ⟨7825864726955655079788625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41737945210430160425539333 7825864726955655079788625)
          ·
            refine ⟨5869398545216741309841469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7825864726955655079788625 5869398545216741309841469)
            ·
              refine ⟨2201024454456277991190551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5869398545216741309841469 2201024454456277991190551)
              ·
                refine ⟨3301536681684416986785827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2201024454456277991190551 3301536681684416986785827)
                ·
                  refine ⟨4952305022526625480178741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3301536681684416986785827 4952305022526625480178741)
                  ·
                    refine ⟨464278595861871138766757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4952305022526625480178741 464278595861871138766757)
                    ·
                      rfl

theorem cell23_2712538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 3, 1, 1, 5].length) (baseStart_2712538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2712538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2712538 prefixEnd_2712538 := by exact prefixLift 2712538
  have htrace : WordTrace (prefixWord ++ tailWord_2712538) baseStart_2712538 baseEnd_2712538 := by
    simpa [prefixWord, tailWord_2712538, baseEnd_2712538] using wordTrace_append hprefix tailTrace_2712538
  have hstable : (prefixWord ++ tailWord_2712538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2712538).length < 2 ^ (prefixWord ++ tailWord_2712538).sum := by decide
  have hdescent : baseEnd_2712538 < baseStart_2712538 := by decide
  rcases family_descends (prefixWord ++ tailWord_2712538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2712561 : List Nat := [1, 2, 2, 2, 4, 1, 1, 2, 3, 2, 3]
def baseStart_2712561 : Nat := 118140960795 + 2712561 * 2 ^ 59
def prefixEnd_2712561 : Nat := 4983230072969 + 3 ^ 40 * 2712561 * 2
def baseEnd_2712561 : Nat := 1392847597640666826312665

theorem tailTrace_2712561 : CollatzResearch.WordTrace tailWord_2712561 prefixEnd_2712561 1392847597640666826312665 := by
  unfold tailWord_2712561
  simp only [CollatzResearch.WordTrace]
  refine ⟨98935227525862240381217537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65956818350574826920811691 98935227525862240381217537)
  ·
    refine ⟨74201420644396680285913153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98935227525862240381217537 74201420644396680285913153)
    ·
      refine ⟨55651065483297510214434865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74201420644396680285913153 55651065483297510214434865)
      ·
        refine ⟨41738299112473132660826149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55651065483297510214434865 41738299112473132660826149)
        ·
          refine ⟨7825931083588712373904903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41738299112473132660826149 7825931083588712373904903)
          ·
            refine ⟨11738896625383068560857355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7825931083588712373904903 11738896625383068560857355)
            ·
              refine ⟨17608344938074602841286033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11738896625383068560857355 17608344938074602841286033)
              ·
                refine ⟨13206258703555952130964525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17608344938074602841286033 13206258703555952130964525)
                ·
                  refine ⟨4952347013833482049111697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13206258703555952130964525 4952347013833482049111697)
                  ·
                    refine ⟨3714260260375111536833773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4952347013833482049111697 3714260260375111536833773)
                    ·
                      refine ⟨1392847597640666826312665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3714260260375111536833773 1392847597640666826312665)
                      ·
                        rfl

theorem cell23_2712561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 2, 3, 2, 3].length) (baseStart_2712561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2712561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2712561 prefixEnd_2712561 := by exact prefixLift 2712561
  have htrace : WordTrace (prefixWord ++ tailWord_2712561) baseStart_2712561 baseEnd_2712561 := by
    simpa [prefixWord, tailWord_2712561, baseEnd_2712561] using wordTrace_append hprefix tailTrace_2712561
  have hstable : (prefixWord ++ tailWord_2712561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2712561).length < 2 ^ (prefixWord ++ tailWord_2712561).sum := by decide
  have hdescent : baseEnd_2712561 < baseStart_2712561 := by decide
  rcases family_descends (prefixWord ++ tailWord_2712561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2712624 : List Nat := [2, 1, 1, 1, 2, 4, 1, 3, 2, 6]
def baseStart_2712624 : Nat := 118140960795 + 2712624 * 2 ^ 59
def prefixEnd_2712624 : Nat := 4983230072969 + 3 ^ 40 * 2712624 * 2
def baseEnd_2712624 : Nat := 464293315640633359941625

theorem tailTrace_2712624 : CollatzResearch.WordTrace tailWord_2712624 prefixEnd_2712624 464293315640633359941625 := by
  unfold tailWord_2712624
  simp only [CollatzResearch.WordTrace]
  refine ⟨49468762662317001070380463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65958350216422668093840617 49468762662317001070380463)
  ·
    refine ⟨74203143993475501605570695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49468762662317001070380463 74203143993475501605570695)
    ·
      refine ⟨111304715990213252408356043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74203143993475501605570695 111304715990213252408356043)
      ·
        refine ⟨166957073985319878612534065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111304715990213252408356043 166957073985319878612534065)
        ·
          refine ⟨125217805488989908959400549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 166957073985319878612534065 125217805488989908959400549)
          ·
            refine ⟨23478338529185607929887603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 125217805488989908959400549 23478338529185607929887603)
            ·
              refine ⟨35217507793778411894831405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23478338529185607929887603 35217507793778411894831405)
              ·
                refine ⟨13206565422666904460561777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35217507793778411894831405 13206565422666904460561777)
                ·
                  refine ⟨9904924067000178345421333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13206565422666904460561777 9904924067000178345421333)
                  ·
                    refine ⟨464293315640633359941625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9904924067000178345421333 464293315640633359941625)
                    ·
                      rfl

theorem cell23_2712624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 3, 2, 6].length) (baseStart_2712624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2712624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2712624 prefixEnd_2712624 := by exact prefixLift 2712624
  have htrace : WordTrace (prefixWord ++ tailWord_2712624) baseStart_2712624 baseEnd_2712624 := by
    simpa [prefixWord, tailWord_2712624, baseEnd_2712624] using wordTrace_append hprefix tailTrace_2712624
  have hstable : (prefixWord ++ tailWord_2712624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2712624).length < 2 ^ (prefixWord ++ tailWord_2712624).sum := by decide
  have hdescent : baseEnd_2712624 < baseStart_2712624 := by decide
  rcases family_descends (prefixWord ++ tailWord_2712624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2712625 : List Nat := [1, 2, 2, 3, 1, 2, 5, 1, 2, 1, 3]
def baseStart_2712625 : Nat := 118140960795 + 2712625 * 2 ^ 59
def prefixEnd_2712625 : Nat := 4983230072969 + 3 ^ 40 * 2712625 * 2
def baseEnd_2712625 : Nat := 1392880460402554575912371

theorem tailTrace_2712625 : CollatzResearch.WordTrace tailWord_2712625 prefixEnd_2712625 1392880460402554575912371 := by
  unfold tailWord_2712625
  simp only [CollatzResearch.WordTrace]
  refine ⟨98937561797630379311547329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65958374531753586207698219 98937561797630379311547329)
  ·
    refine ⟨74203171348222784483660497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98937561797630379311547329 74203171348222784483660497)
    ·
      refine ⟨55652378511167088362745373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74203171348222784483660497 55652378511167088362745373)
      ·
        refine ⟨20869641941687658136029515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55652378511167088362745373 20869641941687658136029515)
        ·
          refine ⟨31304462912531487204044273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20869641941687658136029515 31304462912531487204044273)
          ·
            refine ⟨23478347184398615403033205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31304462912531487204044273 23478347184398615403033205)
            ·
              refine ⟨2201095048537370194034363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23478347184398615403033205 2201095048537370194034363)
              ·
                refine ⟨3301642572806055291051545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2201095048537370194034363 3301642572806055291051545)
                ·
                  refine ⟨2476231929604541468288659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3301642572806055291051545 2476231929604541468288659)
                  ·
                    refine ⟨3714347894406812202432989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2476231929604541468288659 3714347894406812202432989)
                    ·
                      refine ⟨1392880460402554575912371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3714347894406812202432989 1392880460402554575912371)
                      ·
                        rfl

theorem cell23_2712625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 5, 1, 2, 1, 3].length) (baseStart_2712625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2712625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2712625 prefixEnd_2712625 := by exact prefixLift 2712625
  have htrace : WordTrace (prefixWord ++ tailWord_2712625) baseStart_2712625 baseEnd_2712625 := by
    simpa [prefixWord, tailWord_2712625, baseEnd_2712625] using wordTrace_append hprefix tailTrace_2712625
  have hstable : (prefixWord ++ tailWord_2712625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2712625).length < 2 ^ (prefixWord ++ tailWord_2712625).sum := by decide
  have hdescent : baseEnd_2712625 < baseStart_2712625 := by decide
  rcases family_descends (prefixWord ++ tailWord_2712625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2712648 : List Nat := [2, 1, 3, 1, 1, 1, 3, 1, 6, 2, 2]
def baseStart_2712648 : Nat := 118140960795 + 2712648 * 2 ^ 59
def prefixEnd_2712648 : Nat := 4983230072969 + 3 ^ 40 * 2712648 * 2
def baseEnd_2712648 : Nat := 1392892270457607985924765

theorem tailTrace_2712648 : CollatzResearch.WordTrace tailWord_2712648 prefixEnd_2712648 1392892270457607985924765 := by
  unfold tailWord_2712648
  simp only [CollatzResearch.WordTrace]
  refine ⟨49469200338273527119817299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65958933784364702826423065 49469200338273527119817299)
  ·
    refine ⟨74203800507410290679725949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49469200338273527119817299 74203800507410290679725949)
    ·
      refine ⟨27826425190278859004897231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74203800507410290679725949 27826425190278859004897231)
      ·
        refine ⟨41739637785418288507345847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27826425190278859004897231 41739637785418288507345847)
        ·
          refine ⟨62609456678127432761018771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41739637785418288507345847 62609456678127432761018771)
          ·
            refine ⟨93914185017191149141528157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62609456678127432761018771 93914185017191149141528157)
            ·
              refine ⟨35217819381446680928073059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 93914185017191149141528157 35217819381446680928073059)
              ·
                refine ⟨52826729072170021392109589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35217819381446680928073059 52826729072170021392109589)
                ·
                  refine ⟨2476252925257969752755137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 52826729072170021392109589 2476252925257969752755137)
                  ·
                    refine ⟨1857189693943477314566353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2476252925257969752755137 1857189693943477314566353)
                    ·
                      refine ⟨1392892270457607985924765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1857189693943477314566353 1392892270457607985924765)
                      ·
                        rfl

theorem cell23_2712648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 1, 6, 2, 2].length) (baseStart_2712648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2712648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2712648 prefixEnd_2712648 := by exact prefixLift 2712648
  have htrace : WordTrace (prefixWord ++ tailWord_2712648) baseStart_2712648 baseEnd_2712648 := by
    simpa [prefixWord, tailWord_2712648, baseEnd_2712648] using wordTrace_append hprefix tailTrace_2712648
  have hstable : (prefixWord ++ tailWord_2712648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2712648).length < 2 ^ (prefixWord ++ tailWord_2712648).sum := by decide
  have hdescent : baseEnd_2712648 < baseStart_2712648 := by decide
  rcases family_descends (prefixWord ++ tailWord_2712648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2712664 : List Nat := [2, 1, 2, 2, 1, 3, 1, 1, 1, 2, 7]
def baseStart_2712664 : Nat := 118140960795 + 2712664 * 2 ^ 59
def prefixEnd_2712664 : Nat := 4983230072969 + 3 ^ 40 * 2712664 * 2
def baseEnd_2712664 : Nat := 1392900486148079923324691

theorem tailTrace_2712664 : CollatzResearch.WordTrace tailWord_2712664 prefixEnd_2712664 1392900486148079923324691 := by
  unfold tailWord_2712664
  simp only [CollatzResearch.WordTrace]
  refine ⟨49469492122244544486108523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65959322829659392648144697 49469492122244544486108523)
  ·
    refine ⟨74204238183366816729162785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49469492122244544486108523 74204238183366816729162785)
    ·
      refine ⟨55653178637525112546872089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74204238183366816729162785 55653178637525112546872089)
      ·
        refine ⟨41739883978143834410154067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55653178637525112546872089 41739883978143834410154067)
        ·
          refine ⟨62609825967215751615231101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41739883978143834410154067 62609825967215751615231101)
          ·
            refine ⟨23478684737705906855711663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62609825967215751615231101 23478684737705906855711663)
            ·
              refine ⟨35218027106558860283567495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23478684737705906855711663 35218027106558860283567495)
              ·
                refine ⟨52827040659838290425351243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35218027106558860283567495 52827040659838290425351243)
                ·
                  refine ⟨79240560989757435638026865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52827040659838290425351243 79240560989757435638026865)
                  ·
                    refine ⟨59430420742318076728520149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 79240560989757435638026865 59430420742318076728520149)
                    ·
                      refine ⟨1392900486148079923324691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 59430420742318076728520149 1392900486148079923324691)
                      ·
                        rfl

theorem cell23_2712664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 1, 1, 2, 7].length) (baseStart_2712664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2712664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2712664 prefixEnd_2712664 := by exact prefixLift 2712664
  have htrace : WordTrace (prefixWord ++ tailWord_2712664) baseStart_2712664 baseEnd_2712664 := by
    simpa [prefixWord, tailWord_2712664, baseEnd_2712664] using wordTrace_append hprefix tailTrace_2712664
  have hstable : (prefixWord ++ tailWord_2712664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2712664).length < 2 ^ (prefixWord ++ tailWord_2712664).sum := by decide
  have hdescent : baseEnd_2712664 < baseStart_2712664 := by decide
  rcases family_descends (prefixWord ++ tailWord_2712664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2712682 : List Nat := [3, 1, 3, 2, 2, 2, 1, 3, 2, 2, 2]
def baseStart_2712682 : Nat := 118140960795 + 2712682 * 2 ^ 59
def prefixEnd_2712682 : Nat := 4983230072969 + 3 ^ 40 * 2712682 * 2
def baseEnd_2712682 : Nat := 1392909728799860852899609

theorem tailTrace_2712682 : CollatzResearch.WordTrace tailWord_2712682 prefixEnd_2712682 1392909728799860852899609 := by
  unfold tailWord_2712682
  simp only [CollatzResearch.WordTrace]
  refine ⟨24734910189605969511593075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65959760505615918697581533 24734910189605969511593075)
  ·
    refine ⟨37102365284408954267389613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24734910189605969511593075 37102365284408954267389613)
    ·
      refine ⟨13913386981653357850271105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37102365284408954267389613 13913386981653357850271105)
      ·
        refine ⟨10435040236240018387703329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13913386981653357850271105 10435040236240018387703329)
        ·
          refine ⟨7826280177180013790777497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10435040236240018387703329 7826280177180013790777497)
          ·
            refine ⟨5869710132885010343083123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7826280177180013790777497 5869710132885010343083123)
            ·
              refine ⟨8804565199327515514624685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5869710132885010343083123 8804565199327515514624685)
              ·
                refine ⟨3301711949747818317984257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8804565199327515514624685 3301711949747818317984257)
                ·
                  refine ⟨2476283962310863738488193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3301711949747818317984257 2476283962310863738488193)
                  ·
                    refine ⟨1857212971733147803866145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2476283962310863738488193 1857212971733147803866145)
                    ·
                      refine ⟨1392909728799860852899609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1857212971733147803866145 1392909728799860852899609)
                      ·
                        rfl

theorem cell23_2712682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 3, 2, 2, 2].length) (baseStart_2712682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2712682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2712682 prefixEnd_2712682 := by exact prefixLift 2712682
  have htrace : WordTrace (prefixWord ++ tailWord_2712682) baseStart_2712682 baseEnd_2712682 := by
    simpa [prefixWord, tailWord_2712682, baseEnd_2712682] using wordTrace_append hprefix tailTrace_2712682
  have hstable : (prefixWord ++ tailWord_2712682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2712682).length < 2 ^ (prefixWord ++ tailWord_2712682).sum := by decide
  have hdescent : baseEnd_2712682 < baseStart_2712682 := by decide
  rcases family_descends (prefixWord ++ tailWord_2712682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2712718 : List Nat := [4, 1, 1, 3, 2, 1, 2, 2, 2, 5]
def baseStart_2712718 : Nat := 118140960795 + 2712718 * 2 ^ 59
def prefixEnd_2712718 : Nat := 4983230072969 + 3 ^ 40 * 2712718 * 2
def baseEnd_2712718 : Nat := 464309404701140904016481

theorem tailTrace_2712718 : CollatzResearch.WordTrace tailWord_2712718 prefixEnd_2712718 464309404701140904016481 := by
  unfold tailWord_2712718
  simp only [CollatzResearch.WordTrace]
  refine ⟨12367619223286682024335351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65960635857528970796455205 12367619223286682024335351)
  ·
    refine ⟨18551428834930023036503027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12367619223286682024335351 18551428834930023036503027)
    ·
      refine ⟨27827143252395034554754541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18551428834930023036503027 27827143252395034554754541)
      ·
        refine ⟨10435178719648137958032953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27827143252395034554754541 10435178719648137958032953)
        ·
          refine ⟨7826384039736103468524715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10435178719648137958032953 7826384039736103468524715)
          ·
            refine ⟨11739576059604155202787073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7826384039736103468524715 11739576059604155202787073)
            ·
              refine ⟨8804682044703116402090305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11739576059604155202787073 8804682044703116402090305)
              ·
                refine ⟨6603511533527337301567729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8804682044703116402090305 6603511533527337301567729)
                ·
                  refine ⟨4952633650145502976175797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6603511533527337301567729 4952633650145502976175797)
                  ·
                    refine ⟨464309404701140904016481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4952633650145502976175797 464309404701140904016481)
                    ·
                      rfl

theorem cell23_2712718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 2, 2, 5].length) (baseStart_2712718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2712718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2712718 prefixEnd_2712718 := by exact prefixLift 2712718
  have htrace : WordTrace (prefixWord ++ tailWord_2712718) baseStart_2712718 baseEnd_2712718 := by
    simpa [prefixWord, tailWord_2712718, baseEnd_2712718] using wordTrace_append hprefix tailTrace_2712718
  have hstable : (prefixWord ++ tailWord_2712718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2712718).length < 2 ^ (prefixWord ++ tailWord_2712718).sum := by decide
  have hdescent : baseEnd_2712718 < baseStart_2712718 := by decide
  rcases family_descends (prefixWord ++ tailWord_2712718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2712722 : List Nat := [3, 2, 3, 1, 1, 4, 2, 2, 5]
def baseStart_2712722 : Nat := 118140960795 + 2712722 * 2 ^ 59
def prefixEnd_2712722 : Nat := 4983230072969 + 3 ^ 40 * 2712722 * 2
def baseEnd_2712722 : Nat := 154770029780671188488825

theorem tailTrace_2712722 : CollatzResearch.WordTrace tailWord_2712722 prefixEnd_2712722 154770029780671188488825 := by
  unfold tailWord_2712722
  simp only [CollatzResearch.WordTrace]
  refine ⟨24735274919569741219457105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65960733118852643251885613 24735274919569741219457105)
  ·
    refine ⟨18551456189677305914592829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24735274919569741219457105 18551456189677305914592829)
    ·
      refine ⟨6956796071128989717972311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18551456189677305914592829 6956796071128989717972311)
      ·
        refine ⟨10435194106693484576958467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6956796071128989717972311 10435194106693484576958467)
        ·
          refine ⟨15652791160040226865437701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10435194106693484576958467 15652791160040226865437701)
          ·
            refine ⟨2934898342507542537269569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15652791160040226865437701 2934898342507542537269569)
            ·
              refine ⟨2201173756880656902952177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2934898342507542537269569 2201173756880656902952177)
              ·
                refine ⟨1650880317660492677214133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2201173756880656902952177 1650880317660492677214133)
                ·
                  refine ⟨154770029780671188488825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1650880317660492677214133 154770029780671188488825)
                  ·
                    rfl

theorem cell23_2712722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 2, 2, 5].length) (baseStart_2712722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2712722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2712722 prefixEnd_2712722 := by exact prefixLift 2712722
  have htrace : WordTrace (prefixWord ++ tailWord_2712722) baseStart_2712722 baseEnd_2712722 := by
    simpa [prefixWord, tailWord_2712722, baseEnd_2712722] using wordTrace_append hprefix tailTrace_2712722
  have hstable : (prefixWord ++ tailWord_2712722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2712722).length < 2 ^ (prefixWord ++ tailWord_2712722).sum := by decide
  have hdescent : baseEnd_2712722 < baseStart_2712722 := by decide
  rcases family_descends (prefixWord ++ tailWord_2712722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2712765 : List Nat := [1, 4, 1, 2, 1, 1, 3, 5, 1, 4]
def baseStart_2712765 : Nat := 118140960795 + 2712765 * 2 ^ 59
def prefixEnd_2712765 : Nat := 4983230072969 + 3 ^ 40 * 2712765 * 2
def baseEnd_2712765 : Nat := 464317449231394676053909

theorem tailTrace_2712765 : CollatzResearch.WordTrace tailWord_2712765 prefixEnd_2712765 464317449231394676053909 := by
  unfold tailWord_2712765
  simp only [CollatzResearch.WordTrace]
  refine ⟨98942668017123183221643749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65961778678082122147762499 98942668017123183221643749)
  ·
    refine ⟨18551750253210596854058203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 98942668017123183221643749 18551750253210596854058203)
    ·
      refine ⟨27827625379815895281087305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18551750253210596854058203 27827625379815895281087305)
      ·
        refine ⟨20870719034861921460815479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27827625379815895281087305 20870719034861921460815479)
        ·
          refine ⟨31306078552292882191223219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20870719034861921460815479 31306078552292882191223219)
          ·
            refine ⟨46959117828439323286834829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31306078552292882191223219 46959117828439323286834829)
            ·
              refine ⟨17609669185664746232563061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46959117828439323286834829 17609669185664746232563061)
              ·
                refine ⟨1650906486156069959302787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17609669185664746232563061 1650906486156069959302787)
                ·
                  refine ⟨2476359729234104938954181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1650906486156069959302787 2476359729234104938954181)
                  ·
                    refine ⟨464317449231394676053909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2476359729234104938954181 464317449231394676053909)
                    ·
                      rfl

theorem cell23_2712765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 5, 1, 4].length) (baseStart_2712765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2712765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2712765 prefixEnd_2712765 := by exact prefixLift 2712765
  have htrace : WordTrace (prefixWord ++ tailWord_2712765) baseStart_2712765 baseEnd_2712765 := by
    simpa [prefixWord, tailWord_2712765, baseEnd_2712765] using wordTrace_append hprefix tailTrace_2712765
  have hstable : (prefixWord ++ tailWord_2712765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2712765).length < 2 ^ (prefixWord ++ tailWord_2712765).sum := by decide
  have hdescent : baseEnd_2712765 < baseStart_2712765 := by decide
  rcases family_descends (prefixWord ++ tailWord_2712765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2712778 : List Nat := [3, 1, 2, 1, 3, 2, 3, 2, 6]
def baseStart_2712778 : Nat := 118140960795 + 2712778 * 2 ^ 59
def prefixEnd_2712778 : Nat := 4983230072969 + 3 ^ 40 * 2712778 * 2
def baseEnd_2712778 : Nat := 154773224771410275255463

theorem tailTrace_2712778 : CollatzResearch.WordTrace tailWord_2712778 prefixEnd_2712778 154773224771410275255463 := by
  unfold tailWord_2712778
  simp only [CollatzResearch.WordTrace]
  refine ⟨24735785541519021610466747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65962094777384057627911325 24735785541519021610466747)
  ·
    refine ⟨37103678312278532415700121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24735785541519021610466747 37103678312278532415700121)
    ·
      refine ⟨27827758734208899311775091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37103678312278532415700121 27827758734208899311775091)
      ·
        refine ⟨41741638101313348967662637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27827758734208899311775091 41741638101313348967662637)
        ·
          refine ⟨15653114287992505862873489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41741638101313348967662637 15653114287992505862873489)
          ·
            refine ⟨11739835715994379397155117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15653114287992505862873489 11739835715994379397155117)
            ·
              refine ⟨4402438393497892273933169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11739835715994379397155117 4402438393497892273933169)
              ·
                refine ⟨3301828795123419205449877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4402438393497892273933169 3301828795123419205449877)
                ·
                  refine ⟨154773224771410275255463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3301828795123419205449877 154773224771410275255463)
                  ·
                    rfl

theorem cell23_2712778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 3, 2, 6].length) (baseStart_2712778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2712778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2712778 prefixEnd_2712778 := by exact prefixLift 2712778
  have htrace : WordTrace (prefixWord ++ tailWord_2712778) baseStart_2712778 baseEnd_2712778 := by
    simpa [prefixWord, tailWord_2712778, baseEnd_2712778] using wordTrace_append hprefix tailTrace_2712778
  have hstable : (prefixWord ++ tailWord_2712778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2712778).length < 2 ^ (prefixWord ++ tailWord_2712778).sum := by decide
  have hdescent : baseEnd_2712778 < baseStart_2712778 := by decide
  rcases family_descends (prefixWord ++ tailWord_2712778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2712791 : List Nat := [1, 1, 3, 2, 1, 2, 2, 1, 5, 5]
def baseStart_2712791 : Nat := 118140960795 + 2712791 * 2 ^ 59
def prefixEnd_2712791 : Nat := 4983230072969 + 3 ^ 40 * 2712791 * 2
def baseEnd_2712791 : Nat := 464321899397066975478869

theorem tailTrace_2712791 : CollatzResearch.WordTrace tailWord_2712791 prefixEnd_2712791 464321899397066975478869 := by
  unfold tailWord_2712791
  simp only [CollatzResearch.WordTrace]
  refine ⟨98943616315028989662090227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65962410876685993108060151 98943616315028989662090227)
  ·
    refine ⟨148415424472543484493135341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98943616315028989662090227 148415424472543484493135341)
    ·
      refine ⟨55655784177203806684925753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 148415424472543484493135341 55655784177203806684925753)
      ·
        refine ⟨41741838132902855013694315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55655784177203806684925753 41741838132902855013694315)
        ·
          refine ⟨62612757199354282520541473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41741838132902855013694315 62612757199354282520541473)
          ·
            refine ⟨46959567899515711890406105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62612757199354282520541473 46959567899515711890406105)
            ·
              refine ⟨35219675924636783917804579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46959567899515711890406105 35219675924636783917804579)
              ·
                refine ⟨52829513886955175876706869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35219675924636783917804579 52829513886955175876706869)
                ·
                  refine ⟨4952766926902047738441269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 52829513886955175876706869 4952766926902047738441269)
                  ·
                    refine ⟨464321899397066975478869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4952766926902047738441269 464321899397066975478869)
                    ·
                      rfl

theorem cell23_2712791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 1, 5, 5].length) (baseStart_2712791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2712791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2712791 prefixEnd_2712791 := by exact prefixLift 2712791
  have htrace : WordTrace (prefixWord ++ tailWord_2712791) baseStart_2712791 baseEnd_2712791 := by
    simpa [prefixWord, tailWord_2712791, baseEnd_2712791] using wordTrace_append hprefix tailTrace_2712791
  have hstable : (prefixWord ++ tailWord_2712791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2712791).length < 2 ^ (prefixWord ++ tailWord_2712791).sum := by decide
  have hdescent : baseEnd_2712791 < baseStart_2712791 := by decide
  rcases family_descends (prefixWord ++ tailWord_2712791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2712841 : List Nat := [1, 2, 1, 1, 3, 3, 1, 1, 3, 1, 6]
def baseStart_2712841 : Nat := 118140960795 + 2712841 * 2 ^ 59
def prefixEnd_2712841 : Nat := 4983230072969 + 3 ^ 40 * 2712841 * 2
def baseEnd_2712841 : Nat := 1392991372223925730811377

theorem tailTrace_2712841 : CollatzResearch.WordTrace tailWord_2712841 prefixEnd_2712841 1392991372223925730811377 := by
  unfold tailWord_2712841
  simp only [CollatzResearch.WordTrace]
  refine ⟨98945439964847848201410377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65963626643231898800940251 98945439964847848201410377)
  ·
    refine ⟨74209079973635886151057783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98945439964847848201410377 74209079973635886151057783)
    ·
      refine ⟨111313619960453829226586675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74209079973635886151057783 111313619960453829226586675)
      ·
        refine ⟨166970429940680743839880013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111313619960453829226586675 166970429940680743839880013)
        ·
          refine ⟨62613911227755278939955005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 166970429940680743839880013 62613911227755278939955005)
          ·
            refine ⟨23480216710408229602483127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62613911227755278939955005 23480216710408229602483127)
            ·
              refine ⟨35220325065612344403724691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23480216710408229602483127 35220325065612344403724691)
              ·
                refine ⟨52830487598418516605587037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35220325065612344403724691 52830487598418516605587037)
                ·
                  refine ⟨19811432849406943727095139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52830487598418516605587037 19811432849406943727095139)
                  ·
                    refine ⟨29717149274110415590642709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19811432849406943727095139 29717149274110415590642709)
                    ·
                      refine ⟨1392991372223925730811377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 29717149274110415590642709 1392991372223925730811377)
                      ·
                        rfl

theorem cell23_2712841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 1, 3, 1, 6].length) (baseStart_2712841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2712841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2712841 prefixEnd_2712841 := by exact prefixLift 2712841
  have htrace : WordTrace (prefixWord ++ tailWord_2712841) baseStart_2712841 baseEnd_2712841 := by
    simpa [prefixWord, tailWord_2712841, baseEnd_2712841] using wordTrace_append hprefix tailTrace_2712841
  have hstable : (prefixWord ++ tailWord_2712841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2712841).length < 2 ^ (prefixWord ++ tailWord_2712841).sum := by decide
  have hdescent : baseEnd_2712841 < baseStart_2712841 := by decide
  rcases family_descends (prefixWord ++ tailWord_2712841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2712855 : List Nat := [1, 1, 3, 4, 1, 1, 3, 3, 2, 4]
def baseStart_2712855 : Nat := 118140960795 + 2712855 * 2 ^ 59
def prefixEnd_2712855 : Nat := 4983230072969 + 3 ^ 40 * 2712855 * 2
def baseEnd_2712855 : Nat := 464332853651029558678771

theorem tailTrace_2712855 : CollatzResearch.WordTrace tailWord_2712855 prefixEnd_2712855 464332853651029558678771 := by
  unfold tailWord_2712855
  simp only [CollatzResearch.WordTrace]
  refine ⟨98945950586797128592420019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65963967057864752394946679 98945950586797128592420019)
  ·
    refine ⟨148418925880195692888630029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98945950586797128592420019 148418925880195692888630029)
    ·
      refine ⟨55657097205073384833236261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 148418925880195692888630029 55657097205073384833236261)
      ·
        refine ⟨10435705725951259656231799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55657097205073384833236261 10435705725951259656231799)
        ·
          refine ⟨15653558588926889484347699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10435705725951259656231799 15653558588926889484347699)
          ·
            refine ⟨23480337883390334226521549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15653558588926889484347699 23480337883390334226521549)
            ·
              refine ⟨8805126706271375334945581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23480337883390334226521549 8805126706271375334945581)
              ·
                refine ⟨3301922514851765750604593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8805126706271375334945581 3301922514851765750604593)
                ·
                  refine ⟨2476441886138824312953445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3301922514851765750604593 2476441886138824312953445)
                  ·
                    refine ⟨464332853651029558678771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2476441886138824312953445 464332853651029558678771)
                    ·
                      rfl

theorem cell23_2712855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 3, 2, 4].length) (baseStart_2712855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2712855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2712855 prefixEnd_2712855 := by exact prefixLift 2712855
  have htrace : WordTrace (prefixWord ++ tailWord_2712855) baseStart_2712855 baseEnd_2712855 := by
    simpa [prefixWord, tailWord_2712855, baseEnd_2712855] using wordTrace_append hprefix tailTrace_2712855
  have hstable : (prefixWord ++ tailWord_2712855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2712855).length < 2 ^ (prefixWord ++ tailWord_2712855).sum := by decide
  have hdescent : baseEnd_2712855 < baseStart_2712855 := by decide
  rcases family_descends (prefixWord ++ tailWord_2712855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2712858 : List Nat := [3, 1, 1, 3, 3, 1, 2, 1, 1, 1, 6]
def baseStart_2712858 : Nat := 118140960795 + 2712858 * 2 ^ 59
def prefixEnd_2712858 : Nat := 4983230072969 + 3 ^ 40 * 2712858 * 2
def baseEnd_2712858 : Nat := 1393000101395052164298799

theorem tailTrace_2712858 : CollatzResearch.WordTrace tailWord_2712858 prefixEnd_2712858 1393000101395052164298799 := by
  unfold tailWord_2712858
  simp only [CollatzResearch.WordTrace]
  refine ⟨24736515001446565026194807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65964040003857506736519485 24736515001446565026194807)
  ·
    refine ⟨37104772502169847539292211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24736515001446565026194807 37104772502169847539292211)
    ·
      refine ⟨55657158753254771308938317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37104772502169847539292211 55657158753254771308938317)
      ·
        refine ⟨20871434532470539240851869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55657158753254771308938317 20871434532470539240851869)
        ·
          refine ⟨7826787949676452215319451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20871434532470539240851869 7826787949676452215319451)
          ·
            refine ⟨11740181924514678322979177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7826787949676452215319451 11740181924514678322979177)
            ·
              refine ⟨8805136443386008742234383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11740181924514678322979177 8805136443386008742234383)
              ·
                refine ⟨13207704665079013113351575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8805136443386008742234383 13207704665079013113351575)
                ·
                  refine ⟨19811556997618519670027363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13207704665079013113351575 19811556997618519670027363)
                  ·
                    refine ⟨29717335496427779505041045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19811556997618519670027363 29717335496427779505041045)
                    ·
                      refine ⟨1393000101395052164298799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 29717335496427779505041045 1393000101395052164298799)
                      ·
                        rfl

theorem cell23_2712858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 1, 1, 1, 6].length) (baseStart_2712858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2712858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2712858 prefixEnd_2712858 := by exact prefixLift 2712858
  have htrace : WordTrace (prefixWord ++ tailWord_2712858) baseStart_2712858 baseEnd_2712858 := by
    simpa [prefixWord, tailWord_2712858, baseEnd_2712858] using wordTrace_append hprefix tailTrace_2712858
  have hstable : (prefixWord ++ tailWord_2712858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2712858).length < 2 ^ (prefixWord ++ tailWord_2712858).sum := by decide
  have hdescent : baseEnd_2712858 < baseStart_2712858 := by decide
  rcases family_descends (prefixWord ++ tailWord_2712858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2712891 : List Nat := [1, 1, 1, 1, 1, 2, 1, 1, 5, 4, 5]
def baseStart_2712891 : Nat := 118140960795 + 2712891 * 2 ^ 59
def prefixEnd_2712891 : Nat := 4983230072969 + 3 ^ 40 * 2712891 * 2
def baseEnd_2712891 : Nat := 1393017046256650535186147

theorem tailTrace_2712891 : CollatzResearch.WordTrace tailWord_2712891 prefixEnd_2712891 1393017046256650535186147 := by
  unfold tailWord_2712891
  simp only [CollatzResearch.WordTrace]
  refine ⟨98947263614666706740730527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65964842409777804493820351 98947263614666706740730527)
  ·
    refine ⟨148420895422000060111095791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98947263614666706740730527 148420895422000060111095791)
    ·
      refine ⟨222631343133000090166643687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148420895422000060111095791 222631343133000090166643687)
      ·
        refine ⟨333947014699500135249965531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222631343133000090166643687 333947014699500135249965531)
        ·
          refine ⟨500920522049250202874948297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 333947014699500135249965531 500920522049250202874948297)
          ·
            refine ⟨375690391536937652156211223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 500920522049250202874948297 375690391536937652156211223)
            ·
              refine ⟨563535587305406478234316835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 375690391536937652156211223 563535587305406478234316835)
              ·
                refine ⟨845303380958109717351475253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 563535587305406478234316835 845303380958109717351475253)
                ·
                  refine ⟨79247191964822786001700805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 845303380958109717351475253 79247191964822786001700805)
                  ·
                    refine ⟨14858848493404272375318901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 79247191964822786001700805 14858848493404272375318901)
                    ·
                      refine ⟨1393017046256650535186147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14858848493404272375318901 1393017046256650535186147)
                      ·
                        rfl

theorem cell23_2712891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 5, 4, 5].length) (baseStart_2712891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2712891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2712891 prefixEnd_2712891 := by exact prefixLift 2712891
  have htrace : WordTrace (prefixWord ++ tailWord_2712891) baseStart_2712891 baseEnd_2712891 := by
    simpa [prefixWord, tailWord_2712891, baseEnd_2712891] using wordTrace_append hprefix tailTrace_2712891
  have hstable : (prefixWord ++ tailWord_2712891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2712891).length < 2 ^ (prefixWord ++ tailWord_2712891).sum := by decide
  have hdescent : baseEnd_2712891 < baseStart_2712891 := by decide
  rcases family_descends (prefixWord ++ tailWord_2712891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2712905 : List Nat := [1, 2, 1, 1, 2, 3, 3, 2, 3, 3, 2]
def baseStart_2712905 : Nat := 118140960795 + 2712905 * 2 ^ 59
def prefixEnd_2712905 : Nat := 4983230072969 + 3 ^ 40 * 2712905 * 2
def baseEnd_2712905 : Nat := 1393024234985813480411083

theorem tailTrace_2712905 : CollatzResearch.WordTrace tailWord_2712905 prefixEnd_2712905 1393024234985813480411083 := by
  unfold tailWord_2712905
  simp only [CollatzResearch.WordTrace]
  refine ⟨98947774236615987131740169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65965182824410658087826779 98947774236615987131740169)
  ·
    refine ⟨74210830677461990348805127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98947774236615987131740169 74210830677461990348805127)
    ·
      refine ⟨111316246016192985523207691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74210830677461990348805127 111316246016192985523207691)
      ·
        refine ⟨166974369024289478284811537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111316246016192985523207691 166974369024289478284811537)
        ·
          refine ⟨125230776768217108713608653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 166974369024289478284811537 125230776768217108713608653)
          ·
            refine ⟨46961541288081415767603245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 125230776768217108713608653 46961541288081415767603245)
            ·
              refine ⟨17610577983030530912851217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46961541288081415767603245 17610577983030530912851217)
              ·
                refine ⟨13207933487272898184638413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17610577983030530912851217 13207933487272898184638413)
                ·
                  refine ⟨4952975057727336819239405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13207933487272898184638413 4952975057727336819239405)
                  ·
                    refine ⟨1857365646647751307214777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4952975057727336819239405 1857365646647751307214777)
                    ·
                      refine ⟨1393024234985813480411083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1857365646647751307214777 1393024234985813480411083)
                      ·
                        rfl

theorem cell23_2712905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 2, 3, 3, 2].length) (baseStart_2712905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2712905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2712905 prefixEnd_2712905 := by exact prefixLift 2712905
  have htrace : WordTrace (prefixWord ++ tailWord_2712905) baseStart_2712905 baseEnd_2712905 := by
    simpa [prefixWord, tailWord_2712905, baseEnd_2712905] using wordTrace_append hprefix tailTrace_2712905
  have hstable : (prefixWord ++ tailWord_2712905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2712905).length < 2 ^ (prefixWord ++ tailWord_2712905).sum := by decide
  have hdescent : baseEnd_2712905 < baseStart_2712905 := by decide
  rcases family_descends (prefixWord ++ tailWord_2712905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2712909 : List Nat := [1, 6, 1, 3, 1, 1, 2, 1, 1, 2, 4]
def baseStart_2712909 : Nat := 118140960795 + 2712909 * 2 ^ 59
def prefixEnd_2712909 : Nat := 4983230072969 + 3 ^ 40 * 2712909 * 2
def baseEnd_2712909 : Nat := 1393026288908431464761065

theorem tailTrace_2712909 : CollatzResearch.WordTrace tailWord_2712909 prefixEnd_2712909 1393026288908431464761065 := by
  unfold tailWord_2712909
  simp only [CollatzResearch.WordTrace]
  refine ⟨98947920128601495814885781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65965280085734330543257187 98947920128601495814885781)
  ·
    refine ⟨4638183756028195116322771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 98947920128601495814885781 4638183756028195116322771)
    ·
      refine ⟨6957275634042292674484157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4638183756028195116322771 6957275634042292674484157)
      ·
        refine ⟨2608978362765859752931559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6957275634042292674484157 2608978362765859752931559)
        ·
          refine ⟨3913467544148789629397339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2608978362765859752931559 3913467544148789629397339)
          ·
            refine ⟨5870201316223184444096009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3913467544148789629397339 5870201316223184444096009)
            ·
              refine ⟨4402650987167388333072007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5870201316223184444096009 4402650987167388333072007)
              ·
                refine ⟨6603976480751082499608011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4402650987167388333072007 6603976480751082499608011)
                ·
                  refine ⟨9905964721126623749412017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6603976480751082499608011 9905964721126623749412017)
                  ·
                    refine ⟨7429473540844967812059013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9905964721126623749412017 7429473540844967812059013)
                    ·
                      refine ⟨1393026288908431464761065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7429473540844967812059013 1393026288908431464761065)
                      ·
                        rfl

theorem cell23_2712909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_2712909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2712909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2712909 prefixEnd_2712909 := by exact prefixLift 2712909
  have htrace : WordTrace (prefixWord ++ tailWord_2712909) baseStart_2712909 baseEnd_2712909 := by
    simpa [prefixWord, tailWord_2712909, baseEnd_2712909] using wordTrace_append hprefix tailTrace_2712909
  have hstable : (prefixWord ++ tailWord_2712909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2712909).length < 2 ^ (prefixWord ++ tailWord_2712909).sum := by decide
  have hdescent : baseEnd_2712909 < baseStart_2712909 := by decide
  rcases family_descends (prefixWord ++ tailWord_2712909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2712962 : List Nat := [3, 4, 2, 1, 1, 1, 2, 1, 2, 6]
def baseStart_2712962 : Nat := 118140960795 + 2712962 * 2 ^ 59
def prefixEnd_2712962 : Nat := 4983230072969 + 3 ^ 40 * 2712962 * 2
def baseEnd_2712962 : Nat := 464351167794373252466107

theorem tailTrace_2712962 : CollatzResearch.WordTrace tailWord_2712962 prefixEnd_2712962 464351167794373252466107 := by
  unfold tailWord_2712962
  simp only [CollatzResearch.WordTrace]
  refine ⟨24737463299352371466641285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65966568798272990577710093 24737463299352371466641285)
  ·
    refine ⟨4638274368628569649995241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24737463299352371466641285 4638274368628569649995241)
    ·
      refine ⟨3478705776471427237496431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4638274368628569649995241 3478705776471427237496431)
      ·
        refine ⟨5218058664707140856244647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3478705776471427237496431 5218058664707140856244647)
        ·
          refine ⟨7827087997060711284366971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5218058664707140856244647 7827087997060711284366971)
          ·
            refine ⟨11740631995591066926550457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7827087997060711284366971 11740631995591066926550457)
            ·
              refine ⟨8805473996693300194912843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11740631995591066926550457 8805473996693300194912843)
              ·
                refine ⟨13208210995039950292369265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8805473996693300194912843 13208210995039950292369265)
                ·
                  refine ⟨9906158246279962719276949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13208210995039950292369265 9906158246279962719276949)
                  ·
                    refine ⟨464351167794373252466107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9906158246279962719276949 464351167794373252466107)
                    ·
                      rfl

theorem cell23_2712962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 1, 2, 6].length) (baseStart_2712962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2712962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2712962 prefixEnd_2712962 := by exact prefixLift 2712962
  have htrace : WordTrace (prefixWord ++ tailWord_2712962) baseStart_2712962 baseEnd_2712962 := by
    simpa [prefixWord, tailWord_2712962, baseEnd_2712962] using wordTrace_append hprefix tailTrace_2712962
  have hstable : (prefixWord ++ tailWord_2712962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2712962).length < 2 ^ (prefixWord ++ tailWord_2712962).sum := by decide
  have hdescent : baseEnd_2712962 < baseStart_2712962 := by decide
  rcases family_descends (prefixWord ++ tailWord_2712962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2712969 : List Nat := [1, 2, 1, 1, 7, 2, 1, 1, 1, 4, 2]
def baseStart_2712969 : Nat := 118140960795 + 2712969 * 2 ^ 59
def prefixEnd_2712969 : Nat := 4983230072969 + 3 ^ 40 * 2712969 * 2
def baseEnd_2712969 : Nat := 1393057097747701230010789

theorem tailTrace_2712969 : CollatzResearch.WordTrace tailWord_2712969 prefixEnd_2712969 1393057097747701230010789 := by
  unfold tailWord_2712969
  simp only [CollatzResearch.WordTrace]
  refine ⟨98950108508384126062069961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65966739005589417374713307 98950108508384126062069961)
  ·
    refine ⟨74212581381288094546552471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98950108508384126062069961 74212581381288094546552471)
    ·
      refine ⟨111318872071932141819828707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74212581381288094546552471 111318872071932141819828707)
      ·
        refine ⟨166978308107898212729743061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111318872071932141819828707 166978308107898212729743061)
        ·
          refine ⟨3913554096278864360853353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 166978308107898212729743061 3913554096278864360853353)
          ·
            refine ⟨2935165572209148270640015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3913554096278864360853353 2935165572209148270640015)
            ·
              refine ⟨4402748358313722405960023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2935165572209148270640015 4402748358313722405960023)
              ·
                refine ⟨6604122537470583608940035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4402748358313722405960023 6604122537470583608940035)
                ·
                  refine ⟨9906183806205875413410053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6604122537470583608940035 9906183806205875413410053)
                  ·
                    refine ⟨1857409463663601640014385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9906183806205875413410053 1857409463663601640014385)
                    ·
                      refine ⟨1393057097747701230010789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1857409463663601640014385 1393057097747701230010789)
                      ·
                        rfl

theorem cell23_2712969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 1, 1, 1, 4, 2].length) (baseStart_2712969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2712969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2712969 prefixEnd_2712969 := by exact prefixLift 2712969
  have htrace : WordTrace (prefixWord ++ tailWord_2712969) baseStart_2712969 baseEnd_2712969 := by
    simpa [prefixWord, tailWord_2712969, baseEnd_2712969] using wordTrace_append hprefix tailTrace_2712969
  have hstable : (prefixWord ++ tailWord_2712969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2712969).length < 2 ^ (prefixWord ++ tailWord_2712969).sum := by decide
  have hdescent : baseEnd_2712969 < baseStart_2712969 := by decide
  rcases family_descends (prefixWord ++ tailWord_2712969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2713008 : List Nat := [2, 1, 1, 1, 2, 1, 1, 4, 3, 3, 4]
def baseStart_2713008 : Nat := 118140960795 + 2713008 * 2 ^ 59
def prefixEnd_2713008 : Nat := 4983230072969 + 3 ^ 40 * 2713008 * 2
def baseEnd_2713008 : Nat := 1393077123493226577423109

theorem tailTrace_2713008 : CollatzResearch.WordTrace tailWord_2713008 prefixEnd_2713008 1393077123493226577423109 := by
  unfold tailWord_2713008
  simp only [CollatzResearch.WordTrace]
  refine ⟨49475765477621417861369839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65967687303495223815159785 49475765477621417861369839)
  ·
    refine ⟨74213648216432126792054759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49475765477621417861369839 74213648216432126792054759)
    ·
      refine ⟨111320472324648190188082139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74213648216432126792054759 111320472324648190188082139)
      ·
        refine ⟨166980708486972285282123209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111320472324648190188082139 166980708486972285282123209)
        ·
          refine ⟨125235531365229213961592407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 166980708486972285282123209 125235531365229213961592407)
          ·
            refine ⟨187853297047843820942388611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125235531365229213961592407 187853297047843820942388611)
            ·
              refine ⟨281779945571765731413582917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 187853297047843820942388611 281779945571765731413582917)
              ·
                refine ⟨52833739794706074640046797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 281779945571765731413582917 52833739794706074640046797)
                ·
                  refine ⟨19812652423014777990017549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52833739794706074640046797 19812652423014777990017549)
                  ·
                    refine ⟨7429744658630541746256581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19812652423014777990017549 7429744658630541746256581)
                    ·
                      refine ⟨1393077123493226577423109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7429744658630541746256581 1393077123493226577423109)
                      ·
                        rfl

theorem cell23_2713008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 4, 3, 3, 4].length) (baseStart_2713008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2713008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2713008 prefixEnd_2713008 := by exact prefixLift 2713008
  have htrace : WordTrace (prefixWord ++ tailWord_2713008) baseStart_2713008 baseEnd_2713008 := by
    simpa [prefixWord, tailWord_2713008, baseEnd_2713008] using wordTrace_append hprefix tailTrace_2713008
  have hstable : (prefixWord ++ tailWord_2713008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2713008).length < 2 ^ (prefixWord ++ tailWord_2713008).sum := by decide
  have hdescent : baseEnd_2713008 < baseStart_2713008 := by decide
  rcases family_descends (prefixWord ++ tailWord_2713008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2713020 : List Nat := [2, 2, 2, 4, 3, 1, 2, 1, 2, 2, 2]
def baseStart_2713020 : Nat := 118140960795 + 2713020 * 2 ^ 59
def prefixEnd_2713020 : Nat := 4983230072969 + 3 ^ 40 * 2713020 * 2
def baseEnd_2713020 : Nat := 1393083285261080530473055

theorem tailTrace_2713020 : CollatzResearch.WordTrace tailWord_2713020 prefixEnd_2713020 1393083285261080530473055 := by
  unfold tailWord_2713020
  simp only [CollatzResearch.WordTrace]
  refine ⟨49475984315599680886088257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65967979087466241181451009 49475984315599680886088257)
  ·
    refine ⟨37106988236699760664566193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49475984315599680886088257 37106988236699760664566193)
    ·
      refine ⟨27830241177524820498424645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37106988236699760664566193 27830241177524820498424645)
      ·
        refine ⟨5218170220785903843454621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27830241177524820498424645 5218170220785903843454621)
        ·
          refine ⟨1956813832794713941295483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5218170220785903843454621 1956813832794713941295483)
          ·
            refine ⟨2935220749192070911943225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1956813832794713941295483 2935220749192070911943225)
            ·
              refine ⟨2201415561894053183957419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2935220749192070911943225 2201415561894053183957419)
              ·
                refine ⟨3302123342841079775936129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2201415561894053183957419 3302123342841079775936129)
                ·
                  refine ⟨2476592507130809831952097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3302123342841079775936129 2476592507130809831952097)
                  ·
                    refine ⟨1857444380348107373964073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2476592507130809831952097 1857444380348107373964073)
                    ·
                      refine ⟨1393083285261080530473055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1857444380348107373964073 1393083285261080530473055)
                      ·
                        rfl

theorem cell23_2713020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 2, 1, 2, 2, 2].length) (baseStart_2713020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2713020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2713020 prefixEnd_2713020 := by exact prefixLift 2713020
  have htrace : WordTrace (prefixWord ++ tailWord_2713020) baseStart_2713020 baseEnd_2713020 := by
    simpa [prefixWord, tailWord_2713020, baseEnd_2713020] using wordTrace_append hprefix tailTrace_2713020
  have hstable : (prefixWord ++ tailWord_2713020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2713020).length < 2 ^ (prefixWord ++ tailWord_2713020).sum := by decide
  have hdescent : baseEnd_2713020 < baseStart_2713020 := by decide
  rcases family_descends (prefixWord ++ tailWord_2713020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2713035 : List Nat := [1, 1, 1, 1, 3, 3, 2, 4, 3, 4]
def baseStart_2713035 : Nat := 118140960795 + 2713035 * 2 ^ 59
def prefixEnd_2713035 : Nat := 4983230072969 + 3 ^ 40 * 2713035 * 2
def baseEnd_2713035 : Nat := 464363662490299323928495

theorem tailTrace_2713035 : CollatzResearch.WordTrace tailWord_2713035 prefixEnd_2713035 464363662490299323928495 := by
  unfold tailWord_2713035
  simp only [CollatzResearch.WordTrace]
  refine ⟨98952515726145019333972559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65968343817430012889315039 98952515726145019333972559)
  ·
    refine ⟨148428773589217529000958839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98952515726145019333972559 148428773589217529000958839)
    ·
      refine ⟨222643160383826293501438259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148428773589217529000958839 222643160383826293501438259)
      ·
        refine ⟨333964740575739440252157389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222643160383826293501438259 333964740575739440252157389)
        ·
          refine ⟨125236777715902290094559021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 333964740575739440252157389 125236777715902290094559021)
          ·
            refine ⟨46963791643463358785459633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 125236777715902290094559021 46963791643463358785459633)
            ·
              refine ⟨35222843732597519089094725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46963791643463358785459633 35222843732597519089094725)
              ·
                refine ⟨6604283199862034829205261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35222843732597519089094725 6604283199862034829205261)
                ·
                  refine ⟨2476606199948263060951973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6604283199862034829205261 2476606199948263060951973)
                  ·
                    refine ⟨464363662490299323928495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2476606199948263060951973 464363662490299323928495)
                    ·
                      rfl

theorem cell23_2713035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 4, 3, 4].length) (baseStart_2713035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2713035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2713035 prefixEnd_2713035 := by exact prefixLift 2713035
  have htrace : WordTrace (prefixWord ++ tailWord_2713035) baseStart_2713035 baseEnd_2713035 := by
    simpa [prefixWord, tailWord_2713035, baseEnd_2713035] using wordTrace_append hprefix tailTrace_2713035
  have hstable : (prefixWord ++ tailWord_2713035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2713035).length < 2 ^ (prefixWord ++ tailWord_2713035).sum := by decide
  have hdescent : baseEnd_2713035 < baseStart_2713035 := by decide
  rcases family_descends (prefixWord ++ tailWord_2713035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2713048 : List Nat := [2, 1, 2, 2, 2, 1, 2, 1, 10]
def baseStart_2713048 : Nat := 118140960795 + 2713048 * 2 ^ 59
def prefixEnd_2713048 : Nat := 4983230072969 + 3 ^ 40 * 2713048 * 2
def baseEnd_2713048 : Nat := 154788629191045157880325

theorem tailTrace_2713048 : CollatzResearch.WordTrace tailWord_2713048 prefixEnd_2713048 154788629191045157880325 := by
  unfold tailWord_2713048
  simp only [CollatzResearch.WordTrace]
  refine ⟨49476494937548961277097899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65968659916731948369463865 49476494937548961277097899)
  ·
    refine ⟨74214742406323441915646849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49476494937548961277097899 74214742406323441915646849)
    ·
      refine ⟨55661056804742581436735137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74214742406323441915646849 55661056804742581436735137)
      ·
        refine ⟨41745792603556936077551353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55661056804742581436735137 41745792603556936077551353)
        ·
          refine ⟨31309344452667702058163515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41745792603556936077551353 31309344452667702058163515)
          ·
            refine ⟨46964016679001553087245273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31309344452667702058163515 46964016679001553087245273)
            ·
              refine ⟨35223012509251164815433955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46964016679001553087245273 35223012509251164815433955)
              ·
                refine ⟨52834518763876747223150933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35223012509251164815433955 52834518763876747223150933)
                ·
                  refine ⟨154788629191045157880325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 52834518763876747223150933 154788629191045157880325)
                  ·
                    rfl

theorem cell23_2713048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 1, 10].length) (baseStart_2713048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2713048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2713048 prefixEnd_2713048 := by exact prefixLift 2713048
  have htrace : WordTrace (prefixWord ++ tailWord_2713048) baseStart_2713048 baseEnd_2713048 := by
    simpa [prefixWord, tailWord_2713048, baseEnd_2713048] using wordTrace_append hprefix tailTrace_2713048
  have hstable : (prefixWord ++ tailWord_2713048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2713048).length < 2 ^ (prefixWord ++ tailWord_2713048).sum := by decide
  have hdescent : baseEnd_2713048 < baseStart_2713048 := by decide
  rcases family_descends (prefixWord ++ tailWord_2713048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2713086 : List Nat := [4, 2, 2, 3, 1, 1, 1, 2, 3, 4]
def baseStart_2713086 : Nat := 118140960795 + 2713086 * 2 ^ 59
def prefixEnd_2713086 : Nat := 4983230072969 + 3 ^ 40 * 2713086 * 2
def baseEnd_2713086 : Nat := 464372391661425757415917

theorem tailTrace_2713086 : CollatzResearch.WordTrace tailWord_2713086 prefixEnd_2713086 464372391661425757415917 := by
  unfold tailWord_2713086
  simp only [CollatzResearch.WordTrace]
  refine ⟨12369296981120031880509889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65969583899306836696052741 12369296981120031880509889)
  ·
    refine ⟨9276972735840023910382417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12369296981120031880509889 9276972735840023910382417)
    ·
      refine ⟨6957729551880017932786813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9276972735840023910382417 6957729551880017932786813)
      ·
        refine ⟨2609148581955006724795055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6957729551880017932786813 2609148581955006724795055)
        ·
          refine ⟨3913722872932510087192583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2609148581955006724795055 3913722872932510087192583)
          ·
            refine ⟨5870584309398765130788875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3913722872932510087192583 5870584309398765130788875)
            ·
              refine ⟨8805876464098147696183313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5870584309398765130788875 8805876464098147696183313)
              ·
                refine ⟨6604407348073610772137485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8805876464098147696183313 6604407348073610772137485)
                ·
                  refine ⟨2476652755527604039551557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6604407348073610772137485 2476652755527604039551557)
                  ·
                    refine ⟨464372391661425757415917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2476652755527604039551557 464372391661425757415917)
                    ·
                      rfl

theorem cell23_2713086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 2, 3, 4].length) (baseStart_2713086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2713086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2713086 prefixEnd_2713086 := by exact prefixLift 2713086
  have htrace : WordTrace (prefixWord ++ tailWord_2713086) baseStart_2713086 baseEnd_2713086 := by
    simpa [prefixWord, tailWord_2713086, baseEnd_2713086] using wordTrace_append hprefix tailTrace_2713086
  have hstable : (prefixWord ++ tailWord_2713086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2713086).length < 2 ^ (prefixWord ++ tailWord_2713086).sum := by decide
  have hdescent : baseEnd_2713086 < baseStart_2713086 := by decide
  rcases family_descends (prefixWord ++ tailWord_2713086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2713185 : List Nat := [1, 2, 3, 1, 1, 3, 2, 1, 2, 7]
def baseStart_2713185 : Nat := 118140960795 + 2713185 * 2 ^ 59
def prefixEnd_2713185 : Nat := 4983230072969 + 3 ^ 40 * 2713185 * 2
def baseEnd_2713185 : Nat := 464389336523024128303265

theorem tailTrace_2713185 : CollatzResearch.WordTrace tailWord_2713185 prefixEnd_2713185 464389336523024128303265 := by
  unfold tailWord_2713185
  simp only [CollatzResearch.WordTrace]
  refine ⟨98957986675601594951933009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65971991117067729967955339 98957986675601594951933009)
  ·
    refine ⟨74218490006701196213949757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98957986675601594951933009 74218490006701196213949757)
    ·
      refine ⟨27831933752512948580231159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74218490006701196213949757 27831933752512948580231159)
      ·
        refine ⟨41747900628769422870346739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27831933752512948580231159 41747900628769422870346739)
        ·
          refine ⟨62621850943154134305520109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41747900628769422870346739 62621850943154134305520109)
          ·
            refine ⟨23483194103682800364570041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62621850943154134305520109 23483194103682800364570041)
            ·
              refine ⟨17612395577762100273427531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23483194103682800364570041 17612395577762100273427531)
              ·
                refine ⟨26418593366643150410141297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17612395577762100273427531 26418593366643150410141297)
                ·
                  refine ⟨19813945024982362807605973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26418593366643150410141297 19813945024982362807605973)
                  ·
                    refine ⟨464389336523024128303265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19813945024982362807605973 464389336523024128303265)
                    ·
                      rfl

theorem cell23_2713185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 1, 2, 7].length) (baseStart_2713185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2713185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2713185 prefixEnd_2713185 := by exact prefixLift 2713185
  have htrace : WordTrace (prefixWord ++ tailWord_2713185) baseStart_2713185 baseEnd_2713185 := by
    simpa [prefixWord, tailWord_2713185, baseEnd_2713185] using wordTrace_append hprefix tailTrace_2713185
  have hstable : (prefixWord ++ tailWord_2713185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2713185).length < 2 ^ (prefixWord ++ tailWord_2713185).sum := by decide
  have hdescent : baseEnd_2713185 < baseStart_2713185 := by decide
  rcases family_descends (prefixWord ++ tailWord_2713185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2713209 : List Nat := [1, 2, 1, 3, 3, 1, 3, 1, 3, 3, 2]
def baseStart_2713209 : Nat := 118140960795 + 2713209 * 2 ^ 59
def prefixEnd_2713209 : Nat := 4983230072969 + 3 ^ 40 * 2713209 * 2
def baseEnd_2713209 : Nat := 1393180333104780291009685

theorem tailTrace_2713209 : CollatzResearch.WordTrace tailWord_2713209 prefixEnd_2713209 1393180333104780291009685 := by
  unfold tailWord_2713209
  simp only [CollatzResearch.WordTrace]
  refine ⟨98958862027514647050806681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65972574685009764700537787 98958862027514647050806681)
  ·
    refine ⟨74219146520635985288105011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98958862027514647050806681 74219146520635985288105011)
    ·
      refine ⟨111328719780953977932157517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74219146520635985288105011 111328719780953977932157517)
      ·
        refine ⟨41748269917857741724559069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 111328719780953977932157517 41748269917857741724559069)
        ·
          refine ⟨15655601219196653146709651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41748269917857741724559069 15655601219196653146709651)
          ·
            refine ⟨23483401828794979720064477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15655601219196653146709651 23483401828794979720064477)
            ·
              refine ⟨8806275685798117395024179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23483401828794979720064477 8806275685798117395024179)
              ·
                refine ⟨13209413528697176092536269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8806275685798117395024179 13209413528697176092536269)
                ·
                  refine ⟨4953530073261441034701101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13209413528697176092536269 4953530073261441034701101)
                  ·
                    refine ⟨1857573777473040388012913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4953530073261441034701101 1857573777473040388012913)
                    ·
                      refine ⟨1393180333104780291009685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1857573777473040388012913 1393180333104780291009685)
                      ·
                        rfl

theorem cell23_2713209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 1, 3, 3, 2].length) (baseStart_2713209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2713209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2713209 prefixEnd_2713209 := by exact prefixLift 2713209
  have htrace : WordTrace (prefixWord ++ tailWord_2713209) baseStart_2713209 baseEnd_2713209 := by
    simpa [prefixWord, tailWord_2713209, baseEnd_2713209] using wordTrace_append hprefix tailTrace_2713209
  have hstable : (prefixWord ++ tailWord_2713209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2713209).length < 2 ^ (prefixWord ++ tailWord_2713209).sum := by decide
  have hdescent : baseEnd_2713209 < baseStart_2713209 := by decide
  rcases family_descends (prefixWord ++ tailWord_2713209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2713234 : List Nat := [3, 2, 3, 1, 4, 1, 2, 2, 1, 2, 2]
def baseStart_2713234 : Nat := 118140960795 + 2713234 * 2 ^ 59
def prefixEnd_2713234 : Nat := 4983230072969 + 3 ^ 40 * 2713234 * 2
def baseEnd_2713234 : Nat := 1393193170121142693197071

theorem tailTrace_2713234 : CollatzResearch.WordTrace tailWord_2713234 prefixEnd_2713234 1393193170121142693197071 := by
  unfold tailWord_2713234
  simp only [CollatzResearch.WordTrace]
  refine ⟨24739943463106019080116689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65973182568282717546977837 24739943463106019080116689)
  ·
    refine ⟨18554957597329514310087517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24739943463106019080116689 18554957597329514310087517)
    ·
      refine ⟨6958109098998567866282819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18554957597329514310087517 6958109098998567866282819)
      ·
        refine ⟨10437163648497851799424229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6958109098998567866282819 10437163648497851799424229)
        ·
          refine ⟨1956968184093347212392043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10437163648497851799424229 1956968184093347212392043)
          ·
            refine ⟨2935452276140020818588065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1956968184093347212392043 2935452276140020818588065)
            ·
              refine ⟨2201589207105015613941049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2935452276140020818588065 2201589207105015613941049)
              ·
                refine ⟨1651191905328761710455787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2201589207105015613941049 1651191905328761710455787)
                ·
                  refine ⟨2476787857993142565683681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1651191905328761710455787 2476787857993142565683681)
                  ·
                    refine ⟨1857590893494856924262761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2476787857993142565683681 1857590893494856924262761)
                    ·
                      refine ⟨1393193170121142693197071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1857590893494856924262761 1393193170121142693197071)
                      ·
                        rfl

theorem cell23_2713234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 2, 2, 1, 2, 2].length) (baseStart_2713234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2713234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2713234 prefixEnd_2713234 := by exact prefixLift 2713234
  have htrace : WordTrace (prefixWord ++ tailWord_2713234) baseStart_2713234 baseEnd_2713234 := by
    simpa [prefixWord, tailWord_2713234, baseEnd_2713234] using wordTrace_append hprefix tailTrace_2713234
  have hstable : (prefixWord ++ tailWord_2713234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2713234).length < 2 ^ (prefixWord ++ tailWord_2713234).sum := by decide
  have hdescent : baseEnd_2713234 < baseStart_2713234 := by decide
  rcases family_descends (prefixWord ++ tailWord_2713234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2713252 : List Nat := [2, 3, 1, 2, 2, 2, 1, 1, 1, 4, 4]
def baseStart_2713252 : Nat := 118140960795 + 2713252 * 2 ^ 59
def prefixEnd_2713252 : Nat := 4983230072969 + 3 ^ 40 * 2713252 * 2
def baseEnd_2713252 : Nat := 1393202412772923622771987

theorem tailTrace_2713252 : CollatzResearch.WordTrace tailWord_2713252 prefixEnd_2713252 1393202412772923622771987 := by
  unfold tailWord_2713252
  simp only [CollatzResearch.WordTrace]
  refine ⟨49480215183179432697311005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65973620244239243596414673 49480215183179432697311005)
  ·
    refine ⟨18555080693692287261491627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49480215183179432697311005 18555080693692287261491627)
    ·
      refine ⟨27832621040538430892237441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18555080693692287261491627 27832621040538430892237441)
      ·
        refine ⟨20874465780403823169178081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27832621040538430892237441 20874465780403823169178081)
        ·
          refine ⟨15655849335302867376883561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20874465780403823169178081 15655849335302867376883561)
          ·
            refine ⟨11741887001477150532662671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15655849335302867376883561 11741887001477150532662671)
            ·
              refine ⟨17612830502215725798994007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11741887001477150532662671 17612830502215725798994007)
              ·
                refine ⟨26419245753323588698491011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17612830502215725798994007 26419245753323588698491011)
                ·
                  refine ⟨39628868629985383047736517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26419245753323588698491011 39628868629985383047736517)
                  ·
                    refine ⟨7430412868122259321450597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39628868629985383047736517 7430412868122259321450597)
                    ·
                      refine ⟨1393202412772923622771987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7430412868122259321450597 1393202412772923622771987)
                      ·
                        rfl

theorem cell23_2713252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 1, 1, 4, 4].length) (baseStart_2713252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2713252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2713252 prefixEnd_2713252 := by exact prefixLift 2713252
  have htrace : WordTrace (prefixWord ++ tailWord_2713252) baseStart_2713252 baseEnd_2713252 := by
    simpa [prefixWord, tailWord_2713252, baseEnd_2713252] using wordTrace_append hprefix tailTrace_2713252
  have hstable : (prefixWord ++ tailWord_2713252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2713252).length < 2 ^ (prefixWord ++ tailWord_2713252).sum := by decide
  have hdescent : baseEnd_2713252 < baseStart_2713252 := by decide
  rcases family_descends (prefixWord ++ tailWord_2713252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2713279 : List Nat := [1, 1, 2, 2, 2, 3, 4, 3, 5]
def baseStart_2713279 : Nat := 118140960795 + 2713279 * 2 ^ 59
def prefixEnd_2713279 : Nat := 4983230072969 + 3 ^ 40 * 2713279 * 2
def baseEnd_2713279 : Nat := 154801808527843890792707

theorem tailTrace_2713279 : CollatzResearch.WordTrace tailWord_2713279 prefixEnd_2713279 154801808527843890792707 := by
  unfold tailWord_2713279
  simp only [CollatzResearch.WordTrace]
  refine ⟨98961415137261049005854891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65974276758174032670569927 98961415137261049005854891)
  ·
    refine ⟨148442122705891573508782337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98961415137261049005854891 148442122705891573508782337)
    ·
      refine ⟨111331592029418680131586753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148442122705891573508782337 111331592029418680131586753)
      ·
        refine ⟨83498694022064010098690065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111331592029418680131586753 83498694022064010098690065)
        ·
          refine ⟨62624020516548007574017549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83498694022064010098690065 62624020516548007574017549)
          ·
            refine ⟨23484007693705502840256581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62624020516548007574017549 23484007693705502840256581)
            ·
              refine ⟨4403251442569781782548109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23484007693705502840256581 4403251442569781782548109)
              ·
                refine ⟨1651219290963668168455541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4403251442569781782548109 1651219290963668168455541)
                ·
                  refine ⟨154801808527843890792707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1651219290963668168455541 154801808527843890792707)
                  ·
                    rfl

theorem cell23_2713279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 4, 3, 5].length) (baseStart_2713279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2713279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2713279 prefixEnd_2713279 := by exact prefixLift 2713279
  have htrace : WordTrace (prefixWord ++ tailWord_2713279) baseStart_2713279 baseEnd_2713279 := by
    simpa [prefixWord, tailWord_2713279, baseEnd_2713279] using wordTrace_append hprefix tailTrace_2713279
  have hstable : (prefixWord ++ tailWord_2713279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2713279).length < 2 ^ (prefixWord ++ tailWord_2713279).sum := by decide
  have hdescent : baseEnd_2713279 < baseStart_2713279 := by decide
  rcases family_descends (prefixWord ++ tailWord_2713279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2713290 : List Nat := [3, 1, 2, 1, 5, 2, 1, 2, 2, 2, 2]
def baseStart_2713290 : Nat := 118140960795 + 2713290 * 2 ^ 59
def prefixEnd_2713290 : Nat := 4983230072969 + 3 ^ 40 * 2713290 * 2
def baseEnd_2713290 : Nat := 1393221925037794474096813

theorem tailTrace_2713290 : CollatzResearch.WordTrace tailWord_2713290 prefixEnd_2713290 1393221925037794474096813 := by
  unfold tailWord_2713290
  simp only [CollatzResearch.WordTrace]
  refine ⟨24740454085055299471126331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65974544226814131923003549 24740454085055299471126331)
  ·
    refine ⟨37110681127582949206689497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24740454085055299471126331 37110681127582949206689497)
    ·
      refine ⟨27833010845687211905017123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37110681127582949206689497 27833010845687211905017123)
      ·
        refine ⟨41749516268530817857525685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27833010845687211905017123 41749516268530817857525685)
        ·
          refine ⟨3914017150174764174143033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 41749516268530817857525685 3914017150174764174143033)
          ·
            refine ⟨2935512862631073130607275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3914017150174764174143033 2935512862631073130607275)
            ·
              refine ⟨4403269293946609695910913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2935512862631073130607275 4403269293946609695910913)
              ·
                refine ⟨3302451970459957271933185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4403269293946609695910913 3302451970459957271933185)
                ·
                  refine ⟨2476838977844967953949889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3302451970459957271933185 2476838977844967953949889)
                  ·
                    refine ⟨1857629233383725965462417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2476838977844967953949889 1857629233383725965462417)
                    ·
                      refine ⟨1393221925037794474096813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1857629233383725965462417 1393221925037794474096813)
                      ·
                        rfl

theorem cell23_2713290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 1, 2, 2, 2, 2].length) (baseStart_2713290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2713290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2713290 prefixEnd_2713290 := by exact prefixLift 2713290
  have htrace : WordTrace (prefixWord ++ tailWord_2713290) baseStart_2713290 baseEnd_2713290 := by
    simpa [prefixWord, tailWord_2713290, baseEnd_2713290] using wordTrace_append hprefix tailTrace_2713290
  have hstable : (prefixWord ++ tailWord_2713290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2713290).length < 2 ^ (prefixWord ++ tailWord_2713290).sum := by decide
  have hdescent : baseEnd_2713290 < baseStart_2713290 := by decide
  rcases family_descends (prefixWord ++ tailWord_2713290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2713312 : List Nat := [2, 1, 1, 3, 1, 2, 3, 2, 1, 3, 4]
def baseStart_2713312 : Nat := 118140960795 + 2713312 * 2 ^ 59
def prefixEnd_2713312 : Nat := 4983230072969 + 3 ^ 40 * 2713312 * 2
def baseEnd_2713312 : Nat := 1393233221612193388021711

theorem tailTrace_2713312 : CollatzResearch.WordTrace tailWord_2713312 prefixEnd_2713312 1393233221612193388021711 := by
  unfold tailWord_2713312
  simp only [CollatzResearch.WordTrace]
  refine ⟨49481309373070747820903095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65975079164094330427870793 49481309373070747820903095)
  ·
    refine ⟨74221964059606121731354643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49481309373070747820903095 74221964059606121731354643)
    ·
      refine ⟨111332946089409182597031965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74221964059606121731354643 111332946089409182597031965)
      ·
        refine ⟨41749854783528443473886987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 111332946089409182597031965 41749854783528443473886987)
        ·
          refine ⟨62624782175292665210830481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41749854783528443473886987 62624782175292665210830481)
          ·
            refine ⟨46968586631469498908122861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62624782175292665210830481 46968586631469498908122861)
            ·
              refine ⟨17613219986801062090546073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46968586631469498908122861 17613219986801062090546073)
              ·
                refine ⟨13209914990100796567909555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17613219986801062090546073 13209914990100796567909555)
                ·
                  refine ⟨19814872485151194851864333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13209914990100796567909555 19814872485151194851864333)
                  ·
                    refine ⟨7430577181931698069449125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19814872485151194851864333 7430577181931698069449125)
                    ·
                      refine ⟨1393233221612193388021711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7430577181931698069449125 1393233221612193388021711)
                      ·
                        rfl

theorem cell23_2713312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 2, 1, 3, 4].length) (baseStart_2713312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2713312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2713312 prefixEnd_2713312 := by exact prefixLift 2713312
  have htrace : WordTrace (prefixWord ++ tailWord_2713312) baseStart_2713312 baseEnd_2713312 := by
    simpa [prefixWord, tailWord_2713312, baseEnd_2713312] using wordTrace_append hprefix tailTrace_2713312
  have hstable : (prefixWord ++ tailWord_2713312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2713312).length < 2 ^ (prefixWord ++ tailWord_2713312).sum := by decide
  have hdescent : baseEnd_2713312 < baseStart_2713312 := by decide
  rcases family_descends (prefixWord ++ tailWord_2713312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2713346 : List Nat := [3, 4, 1, 1, 1, 1, 3, 2, 2, 1, 4]
def baseStart_2713346 : Nat := 118140960795 + 2713346 * 2 ^ 59
def prefixEnd_2713346 : Nat := 4983230072969 + 3 ^ 40 * 2713346 * 2
def baseEnd_2713346 : Nat := 1393250679954446254996555

theorem tailTrace_2713346 : CollatzResearch.WordTrace tailWord_2713346 prefixEnd_2713346 1393250679954446254996555 := by
  unfold tailWord_2713346
  simp only [CollatzResearch.WordTrace]
  refine ⟨24740964707004579862135973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65975905885345546299029261 24740964707004579862135973)
  ·
    refine ⟨4638930882563358724150495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24740964707004579862135973 4638930882563358724150495)
    ·
      refine ⟨6958396323845038086225743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4638930882563358724150495 6958396323845038086225743)
      ·
        refine ⟨10437594485767557129338615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6958396323845038086225743 10437594485767557129338615)
        ·
          refine ⟨15656391728651335694007923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10437594485767557129338615 15656391728651335694007923)
          ·
            refine ⟨23484587592977003541011885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15656391728651335694007923 23484587592977003541011885)
            ·
              refine ⟨8806720347366376327879457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23484587592977003541011885 8806720347366376327879457)
              ·
                refine ⟨6605040260524782245909593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8806720347366376327879457 6605040260524782245909593)
                ·
                  refine ⟨4953780195393586684432195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6605040260524782245909593 4953780195393586684432195)
                  ·
                    refine ⟨7430670293090380026648293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4953780195393586684432195 7430670293090380026648293)
                    ·
                      refine ⟨1393250679954446254996555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7430670293090380026648293 1393250679954446254996555)
                      ·
                        rfl

theorem cell23_2713346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 2, 2, 1, 4].length) (baseStart_2713346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2713346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2713346 prefixEnd_2713346 := by exact prefixLift 2713346
  have htrace : WordTrace (prefixWord ++ tailWord_2713346) baseStart_2713346 baseEnd_2713346 := by
    simpa [prefixWord, tailWord_2713346, baseEnd_2713346] using wordTrace_append hprefix tailTrace_2713346
  have hstable : (prefixWord ++ tailWord_2713346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2713346).length < 2 ^ (prefixWord ++ tailWord_2713346).sum := by decide
  have hdescent : baseEnd_2713346 < baseStart_2713346 := by decide
  rcases family_descends (prefixWord ++ tailWord_2713346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2713352 : List Nat := [2, 1, 3, 2, 2, 1, 1, 3, 8]
def baseStart_2713352 : Nat := 118140960795 + 2713352 * 2 ^ 59
def prefixEnd_2713352 : Nat := 4983230072969 + 3 ^ 40 * 2713352 * 2
def baseEnd_2713352 : Nat := 154805973426485914613503

theorem tailTrace_2713352 : CollatzResearch.WordTrace tailWord_2713352 prefixEnd_2713352 154805973426485914613503 := by
  unfold tailWord_2713352
  simp only [CollatzResearch.WordTrace]
  refine ⟨49482038832998291236631155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65976051777331054982174873 49482038832998291236631155)
  ·
    refine ⟨74223058249497436854946733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49482038832998291236631155 74223058249497436854946733)
    ·
      refine ⟨27833646843561538820605025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74223058249497436854946733 27833646843561538820605025)
      ·
        refine ⟨20875235132671154115453769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27833646843561538820605025 20875235132671154115453769)
        ·
          refine ⟨15656426349503365586590327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20875235132671154115453769 15656426349503365586590327)
          ·
            refine ⟨23484639524255048379885491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15656426349503365586590327 23484639524255048379885491)
            ·
              refine ⟨35226959286382572569828237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23484639524255048379885491 35226959286382572569828237)
              ·
                refine ⟨13210109732393464713685589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35226959286382572569828237 13210109732393464713685589)
                ·
                  refine ⟨154805973426485914613503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13210109732393464713685589 154805973426485914613503)
                  ·
                    rfl

theorem cell23_2713352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 3, 8].length) (baseStart_2713352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2713352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2713352 prefixEnd_2713352 := by exact prefixLift 2713352
  have htrace : WordTrace (prefixWord ++ tailWord_2713352) baseStart_2713352 baseEnd_2713352 := by
    simpa [prefixWord, tailWord_2713352, baseEnd_2713352] using wordTrace_append hprefix tailTrace_2713352
  have hstable : (prefixWord ++ tailWord_2713352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2713352).length < 2 ^ (prefixWord ++ tailWord_2713352).sum := by decide
  have hdescent : baseEnd_2713352 < baseStart_2713352 := by decide
  rcases family_descends (prefixWord ++ tailWord_2713352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2713356 : List Nat := [2, 2, 1, 2, 2, 1, 2, 6, 1, 4]
def baseStart_2713356 : Nat := 118140960795 + 2713356 * 2 ^ 59
def prefixEnd_2713356 : Nat := 4983230072969 + 3 ^ 40 * 2713356 * 2
def baseEnd_2713356 : Nat := 464418604920330405290503

theorem tailTrace_2713356 : CollatzResearch.WordTrace tailWord_2713356 prefixEnd_2713356 464418604920330405290503 := by
  unfold tailWord_2713356
  simp only [CollatzResearch.WordTrace]
  refine ⟨49482111778991045578203961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65976149038654727437605281 49482111778991045578203961)
  ·
    refine ⟨37111583834243284183652971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49482111778991045578203961 37111583834243284183652971)
    ·
      refine ⟨55667375751364926275479457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37111583834243284183652971 55667375751364926275479457)
      ·
        refine ⟨41750531813523694706609593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55667375751364926275479457 41750531813523694706609593)
        ·
          refine ⟨31312898860142771029957195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41750531813523694706609593 31312898860142771029957195)
          ·
            refine ⟨46969348290214156544935793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31312898860142771029957195 46969348290214156544935793)
            ·
              refine ⟨35227011217660617408701845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46969348290214156544935793 35227011217660617408701845)
              ·
                refine ⟨1651266150827841441032899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 35227011217660617408701845 1651266150827841441032899)
                ·
                  refine ⟨2476899226241762161549349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1651266150827841441032899 2476899226241762161549349)
                  ·
                    refine ⟨464418604920330405290503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2476899226241762161549349 464418604920330405290503)
                    ·
                      rfl

theorem cell23_2713356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 6, 1, 4].length) (baseStart_2713356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2713356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2713356 prefixEnd_2713356 := by exact prefixLift 2713356
  have htrace : WordTrace (prefixWord ++ tailWord_2713356) baseStart_2713356 baseEnd_2713356 := by
    simpa [prefixWord, tailWord_2713356, baseEnd_2713356] using wordTrace_append hprefix tailTrace_2713356
  have hstable : (prefixWord ++ tailWord_2713356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2713356).length < 2 ^ (prefixWord ++ tailWord_2713356).sum := by decide
  have hdescent : baseEnd_2713356 < baseStart_2713356 := by decide
  rcases family_descends (prefixWord ++ tailWord_2713356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2713407 : List Nat := [1, 1, 2, 2, 7, 1, 2, 2, 1, 4]
def baseStart_2713407 : Nat := 118140960795 + 2713407 * 2 ^ 59
def prefixEnd_2713407 : Nat := 4983230072969 + 3 ^ 40 * 2713407 * 2
def baseEnd_2713407 : Nat := 464427334091456838777925

theorem tailTrace_2713407 : CollatzResearch.WordTrace tailWord_2713407 prefixEnd_2713407 464427334091456838777925 := by
  unfold tailWord_2713407
  simp only [CollatzResearch.WordTrace]
  refine ⟨98966083680797326866514475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65977389120531551244342983 98966083680797326866514475)
  ·
    refine ⟨148449125521195990299771713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98966083680797326866514475 148449125521195990299771713)
    ·
      refine ⟨111336844140896992724828785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148449125521195990299771713 111336844140896992724828785)
      ·
        refine ⟨83502633105672744543621589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111336844140896992724828785 83502633105672744543621589)
        ·
          refine ⟨1957092963414204950241131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 83502633105672744543621589 1957092963414204950241131)
          ·
            refine ⟨2935639445121307425361697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1957092963414204950241131 2935639445121307425361697)
            ·
              refine ⟨2201729583840980569021273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2935639445121307425361697 2201729583840980569021273)
              ·
                refine ⟨1651297187880735426765955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2201729583840980569021273 1651297187880735426765955)
                ·
                  refine ⟨2476945781821103140148933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1651297187880735426765955 2476945781821103140148933)
                  ·
                    refine ⟨464427334091456838777925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2476945781821103140148933 464427334091456838777925)
                    ·
                      rfl

theorem cell23_2713407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 2, 2, 1, 4].length) (baseStart_2713407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2713407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2713407 prefixEnd_2713407 := by exact prefixLift 2713407
  have htrace : WordTrace (prefixWord ++ tailWord_2713407) baseStart_2713407 baseEnd_2713407 := by
    simpa [prefixWord, tailWord_2713407, baseEnd_2713407] using wordTrace_append hprefix tailTrace_2713407
  have hstable : (prefixWord ++ tailWord_2713407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2713407).length < 2 ^ (prefixWord ++ tailWord_2713407).sum := by decide
  have hdescent : baseEnd_2713407 < baseStart_2713407 := by decide
  rcases family_descends (prefixWord ++ tailWord_2713407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2713413 : List Nat := [1, 3, 1, 1, 1, 2, 5, 4, 1, 1, 3]
def baseStart_2713413 : Nat := 118140960795 + 2713413 * 2 ^ 59
def prefixEnd_2713413 : Nat := 4983230072969 + 3 ^ 40 * 2713413 * 2
def baseEnd_2713413 : Nat := 1393285083158297492858747

theorem tailTrace_2713413 : CollatzResearch.WordTrace tailWord_2713413 prefixEnd_2713413 1393285083158297492858747 := by
  unfold tailWord_2713413
  simp only [CollatzResearch.WordTrace]
  refine ⟨98966302518775589891232893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65977535012517059927488595 98966302518775589891232893)
  ·
    refine ⟨37112363444540846209212335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98966302518775589891232893 37112363444540846209212335)
    ·
      refine ⟨55668545166811269313818503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37112363444540846209212335 55668545166811269313818503)
      ·
        refine ⟨83502817750216903970727755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55668545166811269313818503 83502817750216903970727755)
        ·
          refine ⟨125254226625325355956091633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83502817750216903970727755 125254226625325355956091633)
          ·
            refine ⟨93940669968994016967068725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 125254226625325355956091633 93940669968994016967068725)
            ·
              refine ⟨8806937809593189090662693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 93940669968994016967068725 8806937809593189090662693)
              ·
                refine ⟨1651300839298722954499255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8806937809593189090662693 1651300839298722954499255)
                ·
                  refine ⟨2476951258948084431748883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1651300839298722954499255 2476951258948084431748883)
                  ·
                    refine ⟨3715426888422126647623325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2476951258948084431748883 3715426888422126647623325)
                    ·
                      refine ⟨1393285083158297492858747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3715426888422126647623325 1393285083158297492858747)
                      ·
                        rfl

theorem cell23_2713413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 4, 1, 1, 3].length) (baseStart_2713413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2713413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2713413 prefixEnd_2713413 := by exact prefixLift 2713413
  have htrace : WordTrace (prefixWord ++ tailWord_2713413) baseStart_2713413 baseEnd_2713413 := by
    simpa [prefixWord, tailWord_2713413, baseEnd_2713413] using wordTrace_append hprefix tailTrace_2713413
  have hstable : (prefixWord ++ tailWord_2713413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2713413).length < 2 ^ (prefixWord ++ tailWord_2713413).sum := by decide
  have hdescent : baseEnd_2713413 < baseStart_2713413 := by decide
  rcases family_descends (prefixWord ++ tailWord_2713413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2713429 : List Nat := [1, 3, 2, 2, 2, 2, 1, 3, 1, 6]
def baseStart_2713429 : Nat := 118140960795 + 2713429 * 2 ^ 59
def prefixEnd_2713429 : Nat := 4983230072969 + 3 ^ 40 * 2713429 * 2
def baseEnd_2713429 : Nat := 464431099616256476752891

theorem tailTrace_2713429 : CollatzResearch.WordTrace tailWord_2713429 prefixEnd_2713429 464431099616256476752891 := by
  unfold tailWord_2713429
  simp only [CollatzResearch.WordTrace]
  refine ⟨98966886086717624623815341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65977924057811749749210227 98966886086717624623815341)
  ·
    refine ⟨37112582282519109233930753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98966886086717624623815341 37112582282519109233930753)
    ·
      refine ⟨27834436711889331925448065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37112582282519109233930753 27834436711889331925448065)
      ·
        refine ⟨20875827533916998944086049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27834436711889331925448065 20875827533916998944086049)
        ·
          refine ⟨15656870650437749208064537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20875827533916998944086049 15656870650437749208064537)
          ·
            refine ⟨11742652987828311906048403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15656870650437749208064537 11742652987828311906048403)
            ·
              refine ⟨17613979481742467859072605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11742652987828311906048403 17613979481742467859072605)
              ·
                refine ⟨6605242305653425447152227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17613979481742467859072605 6605242305653425447152227)
                ·
                  refine ⟨9907863458480138170728341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6605242305653425447152227 9907863458480138170728341)
                  ·
                    refine ⟨464431099616256476752891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9907863458480138170728341 464431099616256476752891)
                    ·
                      rfl

theorem cell23_2713429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 3, 1, 6].length) (baseStart_2713429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2713429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2713429 prefixEnd_2713429 := by exact prefixLift 2713429
  have htrace : WordTrace (prefixWord ++ tailWord_2713429) baseStart_2713429 baseEnd_2713429 := by
    simpa [prefixWord, tailWord_2713429, baseEnd_2713429] using wordTrace_append hprefix tailTrace_2713429
  have hstable : (prefixWord ++ tailWord_2713429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2713429).length < 2 ^ (prefixWord ++ tailWord_2713429).sum := by decide
  have hdescent : baseEnd_2713429 < baseStart_2713429 := by decide
  rcases family_descends (prefixWord ++ tailWord_2713429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2713453 : List Nat := [1, 5, 1, 1, 1, 1, 6, 1, 1, 1, 4]
def baseStart_2713453 : Nat := 118140960795 + 2713453 * 2 ^ 59
def prefixEnd_2713453 : Nat := 4983230072969 + 3 ^ 40 * 2713453 * 2
def baseEnd_2713453 : Nat := 1393305622384477336358563

theorem tailTrace_2713453 : CollatzResearch.WordTrace tailWord_2713453 prefixEnd_2713453 1393305622384477336358563 := by
  unfold tailWord_2713453
  simp only [CollatzResearch.WordTrace]
  refine ⟨98967761438630676722689013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65978507625753784481792675 98967761438630676722689013)
  ·
    refine ⟨9278227634871625942752095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 98967761438630676722689013 9278227634871625942752095)
    ·
      refine ⟨13917341452307438914128143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9278227634871625942752095 13917341452307438914128143)
      ·
        refine ⟨20876012178461158371192215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13917341452307438914128143 20876012178461158371192215)
        ·
          refine ⟨31314018267691737556788323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20876012178461158371192215 31314018267691737556788323)
          ·
            refine ⟨46971027401537606335182485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31314018267691737556788323 46971027401537606335182485)
            ·
              refine ⟨2201766909447075296961679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 46971027401537606335182485 2201766909447075296961679)
              ·
                refine ⟨3302650364170612945442519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2201766909447075296961679 3302650364170612945442519)
                ·
                  refine ⟨4953975546255919418163779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3302650364170612945442519 4953975546255919418163779)
                  ·
                    refine ⟨7430963319383879127245669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4953975546255919418163779 7430963319383879127245669)
                    ·
                      refine ⟨1393305622384477336358563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7430963319383879127245669 1393305622384477336358563)
                      ·
                        rfl

theorem cell23_2713453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 6, 1, 1, 1, 4].length) (baseStart_2713453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2713453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2713453 prefixEnd_2713453 := by exact prefixLift 2713453
  have htrace : WordTrace (prefixWord ++ tailWord_2713453) baseStart_2713453 baseEnd_2713453 := by
    simpa [prefixWord, tailWord_2713453, baseEnd_2713453] using wordTrace_append hprefix tailTrace_2713453
  have hstable : (prefixWord ++ tailWord_2713453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2713453).length < 2 ^ (prefixWord ++ tailWord_2713453).sum := by decide
  have hdescent : baseEnd_2713453 < baseStart_2713453 := by decide
  rcases family_descends (prefixWord ++ tailWord_2713453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2713473 : List Nat := [1, 2, 4, 4, 1, 1, 1, 2, 1, 1, 5]
def baseStart_2713473 : Nat := 118140960795 + 2713473 * 2 ^ 59
def prefixEnd_2713473 : Nat := 4983230072969 + 3 ^ 40 * 2713473 * 2
def baseEnd_2713473 : Nat := 1393315891997567258108471

theorem tailTrace_2713473 : CollatzResearch.WordTrace tailWord_2713473 prefixEnd_2713473 1393315891997567258108471 := by
  unfold tailWord_2713473
  simp only [CollatzResearch.WordTrace]
  refine ⟨98968490898558220138417073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65978993932372146758944715 98968490898558220138417073)
  ·
    refine ⟨74226368173918665103812805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98968490898558220138417073 74226368173918665103812805)
    ·
      refine ⟨13917444032609749706964901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 74226368173918665103812805 13917444032609749706964901)
      ·
        refine ⟨2609520756114328070055919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13917444032609749706964901 2609520756114328070055919)
        ·
          refine ⟨3914281134171492105083879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2609520756114328070055919 3914281134171492105083879)
          ·
            refine ⟨5871421701257238157625819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3914281134171492105083879 5871421701257238157625819)
            ·
              refine ⟨8807132551885857236438729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5871421701257238157625819 8807132551885857236438729)
              ·
                refine ⟨6605349413914392927329047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8807132551885857236438729 6605349413914392927329047)
                ·
                  refine ⟨9908024120871589390993571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6605349413914392927329047 9908024120871589390993571)
                  ·
                    refine ⟨14862036181307384086490357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9908024120871589390993571 14862036181307384086490357)
                    ·
                      refine ⟨1393315891997567258108471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14862036181307384086490357 1393315891997567258108471)
                      ·
                        rfl

theorem cell23_2713473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_2713473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2713473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2713473 prefixEnd_2713473 := by exact prefixLift 2713473
  have htrace : WordTrace (prefixWord ++ tailWord_2713473) baseStart_2713473 baseEnd_2713473 := by
    simpa [prefixWord, tailWord_2713473, baseEnd_2713473] using wordTrace_append hprefix tailTrace_2713473
  have hstable : (prefixWord ++ tailWord_2713473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2713473).length < 2 ^ (prefixWord ++ tailWord_2713473).sum := by decide
  have hdescent : baseEnd_2713473 < baseStart_2713473 := by decide
  rcases family_descends (prefixWord ++ tailWord_2713473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2713480 : List Nat := [2, 1, 3, 3, 3, 1, 3, 1, 2, 4]
def baseStart_2713480 : Nat := 118140960795 + 2713480 * 2 ^ 59
def prefixEnd_2713480 : Nat := 4983230072969 + 3 ^ 40 * 2713480 * 2
def baseEnd_2713480 : Nat := 464439828787382910240313

theorem tailTrace_2713480 : CollatzResearch.WordTrace tailWord_2713480 prefixEnd_2713480 464439828787382910240313 := by
  unfold tailWord_2713480
  simp only [CollatzResearch.WordTrace]
  refine ⟨49484373104766430166960947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65979164139688573555947929 49484373104766430166960947)
  ·
    refine ⟨74226559657149645250441421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49484373104766430166960947 74226559657149645250441421)
    ·
      refine ⟨27834959871431116968915533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74226559657149645250441421 27834959871431116968915533)
      ·
        refine ⟨10438109951786668863343325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27834959871431116968915533 10438109951786668863343325)
        ·
          refine ⟨3914291231920000823753747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10438109951786668863343325 3914291231920000823753747)
          ·
            refine ⟨5871436847880001235630621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3914291231920000823753747 5871436847880001235630621)
            ·
              refine ⟨2201788817955000463361483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5871436847880001235630621 2201788817955000463361483)
              ·
                refine ⟨3302683226932500695042225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2201788817955000463361483 3302683226932500695042225)
                ·
                  refine ⟨2477012420199375521281669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3302683226932500695042225 2477012420199375521281669)
                  ·
                    refine ⟨464439828787382910240313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2477012420199375521281669 464439828787382910240313)
                    ·
                      rfl

theorem cell23_2713480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 3, 1, 2, 4].length) (baseStart_2713480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2713480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2713480 prefixEnd_2713480 := by exact prefixLift 2713480
  have htrace : WordTrace (prefixWord ++ tailWord_2713480) baseStart_2713480 baseEnd_2713480 := by
    simpa [prefixWord, tailWord_2713480, baseEnd_2713480] using wordTrace_append hprefix tailTrace_2713480
  have hstable : (prefixWord ++ tailWord_2713480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2713480).length < 2 ^ (prefixWord ++ tailWord_2713480).sum := by decide
  have hdescent : baseEnd_2713480 < baseStart_2713480 := by decide
  rcases family_descends (prefixWord ++ tailWord_2713480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2713490 : List Nat := [3, 2, 3, 2, 1, 2, 2, 2, 1, 2, 3]
def baseStart_2713490 : Nat := 118140960795 + 2713490 * 2 ^ 59
def prefixEnd_2713490 : Nat := 4983230072969 + 3 ^ 40 * 2713490 * 2
def baseEnd_2713490 : Nat := 1393324621168693691595893

theorem tailTrace_2713490 : CollatzResearch.WordTrace tailWord_2713490 prefixEnd_2713490 1393324621168693691595893 := by
  unfold tailWord_2713490
  simp only [CollatzResearch.WordTrace]
  refine ⟨24742277734874158010446481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65979407292997754694523949 24742277734874158010446481)
  ·
    refine ⟨18556708301155618507834861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24742277734874158010446481 18556708301155618507834861)
    ·
      refine ⟨6958765612933356940438073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18556708301155618507834861 6958765612933356940438073)
      ·
        refine ⟨5219074209700017705328555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6958765612933356940438073 5219074209700017705328555)
        ·
          refine ⟨7828611314550026557992833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5219074209700017705328555 7828611314550026557992833)
          ·
            refine ⟨5871458485912519918494625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7828611314550026557992833 5871458485912519918494625)
            ·
              refine ⟨4403593864434389938870969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5871458485912519918494625 4403593864434389938870969)
              ·
                refine ⟨3302695398325792454153227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4403593864434389938870969 3302695398325792454153227)
                ·
                  refine ⟨4954043097488688681229841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3302695398325792454153227 4954043097488688681229841)
                  ·
                    refine ⟨3715532323116516510922381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4954043097488688681229841 3715532323116516510922381)
                    ·
                      refine ⟨1393324621168693691595893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3715532323116516510922381 1393324621168693691595893)
                      ·
                        rfl

theorem cell23_2713490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 2, 2, 1, 2, 3].length) (baseStart_2713490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2713490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2713490 prefixEnd_2713490 := by exact prefixLift 2713490
  have htrace : WordTrace (prefixWord ++ tailWord_2713490) baseStart_2713490 baseEnd_2713490 := by
    simpa [prefixWord, tailWord_2713490, baseEnd_2713490] using wordTrace_append hprefix tailTrace_2713490
  have hstable : (prefixWord ++ tailWord_2713490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2713490).length < 2 ^ (prefixWord ++ tailWord_2713490).sum := by decide
  have hdescent : baseEnd_2713490 < baseStart_2713490 := by decide
  rcases family_descends (prefixWord ++ tailWord_2713490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2713529 : List Nat := [1, 2, 1, 4, 2, 1, 1, 2, 1, 3, 5]
def baseStart_2713529 : Nat := 118140960795 + 2713529 * 2 ^ 59
def prefixEnd_2713529 : Nat := 4983230072969 + 3 ^ 40 * 2713529 * 2
def baseEnd_2713529 : Nat := 1393344646914219039008213

theorem tailTrace_2713529 : CollatzResearch.WordTrace tailWord_2713529 prefixEnd_2713529 1393344646914219039008213 := by
  unfold tailWord_2713529
  simp only [CollatzResearch.WordTrace]
  refine ⟨98970533386355341702455641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65980355590903561134970427 98970533386355341702455641)
  ·
    refine ⟨74227900039766506276841731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98970533386355341702455641 74227900039766506276841731)
    ·
      refine ⟨111341850059649759415262597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74227900039766506276841731 111341850059649759415262597)
      ·
        refine ⟨20876596886184329890361737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 111341850059649759415262597 20876596886184329890361737)
        ·
          refine ⟨15657447664638247417771303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20876596886184329890361737 15657447664638247417771303)
          ·
            refine ⟨23486171496957371126656955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15657447664638247417771303 23486171496957371126656955)
            ·
              refine ⟨35229257245436056689985433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23486171496957371126656955 35229257245436056689985433)
              ·
                refine ⟨26421942934077042517489075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35229257245436056689985433 26421942934077042517489075)
                ·
                  refine ⟨39632914401115563776233613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26421942934077042517489075 39632914401115563776233613)
                  ·
                    refine ⟨14862342900418336416087605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39632914401115563776233613 14862342900418336416087605)
                    ·
                      refine ⟨1393344646914219039008213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14862342900418336416087605 1393344646914219039008213)
                      ·
                        rfl

theorem cell23_2713529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 2, 1, 3, 5].length) (baseStart_2713529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2713529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2713529 prefixEnd_2713529 := by exact prefixLift 2713529
  have htrace : WordTrace (prefixWord ++ tailWord_2713529) baseStart_2713529 baseEnd_2713529 := by
    simpa [prefixWord, tailWord_2713529, baseEnd_2713529] using wordTrace_append hprefix tailTrace_2713529
  have hstable : (prefixWord ++ tailWord_2713529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2713529).length < 2 ^ (prefixWord ++ tailWord_2713529).sum := by decide
  have hdescent : baseEnd_2713529 < baseStart_2713529 := by decide
  rcases family_descends (prefixWord ++ tailWord_2713529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2713576 : List Nat := [2, 1, 4, 1, 1, 1, 1, 4, 2, 3, 3]
def baseStart_2713576 : Nat := 118140960795 + 2713576 * 2 ^ 59
def prefixEnd_2713576 : Nat := 4983230072969 + 3 ^ 40 * 2713576 * 2
def baseEnd_2713576 : Nat := 1393368780504980355120497

theorem tailTrace_2713576 : CollatzResearch.WordTrace tailWord_2713576 prefixEnd_2713576 1393368780504980355120497 := by
  unfold tailWord_2713576
  simp only [CollatzResearch.WordTrace]
  refine ⟨49486123808592534364708291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65981498411456712486277721 49486123808592534364708291)
  ·
    refine ⟨74229185712888801547062437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49486123808592534364708291 74229185712888801547062437)
    ·
      refine ⟨13917972321166650290074207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 74229185712888801547062437 13917972321166650290074207)
      ·
        refine ⟨20876958481749975435111311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13917972321166650290074207 20876958481749975435111311)
        ·
          refine ⟨31315437722624963152666967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20876958481749975435111311 31315437722624963152666967)
          ·
            refine ⟨46973156583937444729000451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31315437722624963152666967 46973156583937444729000451)
            ·
              refine ⟨70459734875906167093500677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46973156583937444729000451 70459734875906167093500677)
              ·
                refine ⟨13211200289232406330031377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 70459734875906167093500677 13211200289232406330031377)
                ·
                  refine ⟨9908400216924304747523533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13211200289232406330031377 9908400216924304747523533)
                  ·
                    refine ⟨3715650081346614280321325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9908400216924304747523533 3715650081346614280321325)
                    ·
                      refine ⟨1393368780504980355120497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3715650081346614280321325 1393368780504980355120497)
                      ·
                        rfl

theorem cell23_2713576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 4, 2, 3, 3].length) (baseStart_2713576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2713576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2713576 prefixEnd_2713576 := by exact prefixLift 2713576
  have htrace : WordTrace (prefixWord ++ tailWord_2713576) baseStart_2713576 baseEnd_2713576 := by
    simpa [prefixWord, tailWord_2713576, baseEnd_2713576] using wordTrace_append hprefix tailTrace_2713576
  have hstable : (prefixWord ++ tailWord_2713576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2713576).length < 2 ^ (prefixWord ++ tailWord_2713576).sum := by decide
  have hdescent : baseEnd_2713576 < baseStart_2713576 := by decide
  rcases family_descends (prefixWord ++ tailWord_2713576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2713670 : List Nat := [6, 1, 1, 1, 1, 1, 1, 3, 1, 4, 3]
def baseStart_2713670 : Nat := 118140960795 + 2713670 * 2 ^ 59
def prefixEnd_2713670 : Nat := 4983230072969 + 3 ^ 40 * 2713670 * 2
def baseEnd_2713670 : Nat := 1393417047686502987345065

theorem tailTrace_2713670 : CollatzResearch.WordTrace tailWord_2713670 prefixEnd_2713670 1393417047686502987345065 := by
  unfold tailWord_2713670
  simp only [CollatzResearch.WordTrace]
  refine ⟨3092989877463891336979327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 65983784052563015188892309 3092989877463891336979327)
  ·
    refine ⟨4639484816195837005468991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3092989877463891336979327 4639484816195837005468991)
    ·
      refine ⟨6959227224293755508203487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4639484816195837005468991 6959227224293755508203487)
      ·
        refine ⟨10438840836440633262305231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6959227224293755508203487 10438840836440633262305231)
        ·
          refine ⟨15658261254660949893457847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10438840836440633262305231 15658261254660949893457847)
          ·
            refine ⟨23487391881991424840186771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15658261254660949893457847 23487391881991424840186771)
            ·
              refine ⟨35231087822987137260280157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23487391881991424840186771 35231087822987137260280157)
              ·
                refine ⟨13211657933620176472605059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35231087822987137260280157 13211657933620176472605059)
                ·
                  refine ⟨19817486900430264708907589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13211657933620176472605059 19817486900430264708907589)
                  ·
                    refine ⟨3715778793830674632920173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19817486900430264708907589 3715778793830674632920173)
                    ·
                      refine ⟨1393417047686502987345065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3715778793830674632920173 1393417047686502987345065)
                      ·
                        rfl

theorem cell23_2713670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 3, 1, 4, 3].length) (baseStart_2713670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2713670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2713670 prefixEnd_2713670 := by exact prefixLift 2713670
  have htrace : WordTrace (prefixWord ++ tailWord_2713670) baseStart_2713670 baseEnd_2713670 := by
    simpa [prefixWord, tailWord_2713670, baseEnd_2713670] using wordTrace_append hprefix tailTrace_2713670
  have hstable : (prefixWord ++ tailWord_2713670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2713670).length < 2 ^ (prefixWord ++ tailWord_2713670).sum := by decide
  have hdescent : baseEnd_2713670 < baseStart_2713670 := by decide
  rcases family_descends (prefixWord ++ tailWord_2713670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2713700 : List Nat := [2, 3, 1, 1, 2, 1, 5, 1, 3, 1, 3]
def baseStart_2713700 : Nat := 118140960795 + 2713700 * 2 ^ 59
def prefixEnd_2713700 : Nat := 4983230072969 + 3 ^ 40 * 2713700 * 2
def baseEnd_2713700 : Nat := 1393432452106137869969927

theorem tailTrace_2713700 : CollatzResearch.WordTrace tailWord_2713700 prefixEnd_2713700 1393432452106137869969927 := by
  unfold tailWord_2713700
  simp only [CollatzResearch.WordTrace]
  refine ⟨49488385134367918953465277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65984513512490558604620369 49488385134367918953465277)
  ·
    refine ⟨18558144425387969607549479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49488385134367918953465277 18558144425387969607549479)
    ·
      refine ⟨27837216638081954411324219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18558144425387969607549479 27837216638081954411324219)
      ·
        refine ⟨41755824957122931616986329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27837216638081954411324219 41755824957122931616986329)
        ·
          refine ⟨31316868717842198712739747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41755824957122931616986329 31316868717842198712739747)
          ·
            refine ⟨46975303076763298069109621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31316868717842198712739747 46975303076763298069109621)
            ·
              refine ⟨4403934663446559193979027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 46975303076763298069109621 4403934663446559193979027)
              ·
                refine ⟨6605901995169838790968541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4403934663446559193979027 6605901995169838790968541)
                ·
                  refine ⟨2477213248188689546613203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6605901995169838790968541 2477213248188689546613203)
                  ·
                    refine ⟨3715819872283034319919805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2477213248188689546613203 3715819872283034319919805)
                    ·
                      refine ⟨1393432452106137869969927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3715819872283034319919805 1393432452106137869969927)
                      ·
                        rfl

theorem cell23_2713700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 5, 1, 3, 1, 3].length) (baseStart_2713700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2713700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2713700 prefixEnd_2713700 := by exact prefixLift 2713700
  have htrace : WordTrace (prefixWord ++ tailWord_2713700) baseStart_2713700 baseEnd_2713700 := by
    simpa [prefixWord, tailWord_2713700, baseEnd_2713700] using wordTrace_append hprefix tailTrace_2713700
  have hstable : (prefixWord ++ tailWord_2713700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2713700).length < 2 ^ (prefixWord ++ tailWord_2713700).sum := by decide
  have hdescent : baseEnd_2713700 < baseStart_2713700 := by decide
  rcases family_descends (prefixWord ++ tailWord_2713700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2713710 : List Nat := [4, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2]
def baseStart_2713710 : Nat := 118140960795 + 2713710 * 2 ^ 59
def prefixEnd_2713710 : Nat := 4983230072969 + 3 ^ 40 * 2713710 * 2
def baseEnd_2713710 : Nat := 1393437586912682830844881

theorem tailTrace_2713710 : CollatzResearch.WordTrace tailWord_2713710 prefixEnd_2713710 1393437586912682830844881 := by
  unfold tailWord_2713710
  simp only [CollatzResearch.WordTrace]
  refine ⟨12372141874837451201849323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65984756665799739743196389 12372141874837451201849323)
  ·
    refine ⟨18558212812256176802773985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12372141874837451201849323 18558212812256176802773985)
    ·
      refine ⟨13918659609192132602080489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18558212812256176802773985 13918659609192132602080489)
      ·
        refine ⟨10438994706894099451560367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13918659609192132602080489 10438994706894099451560367)
        ·
          refine ⟨15658492060341149177340551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10438994706894099451560367 15658492060341149177340551)
          ·
            refine ⟨23487738090511723766010827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15658492060341149177340551 23487738090511723766010827)
            ·
              refine ⟨35231607135767585649016241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23487738090511723766010827 35231607135767585649016241)
              ·
                refine ⟨26423705351825689236762181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35231607135767585649016241 26423705351825689236762181)
                ·
                  refine ⟨4954444753467316731892909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26423705351825689236762181 4954444753467316731892909)
                  ·
                    refine ⟨1857916782550243774459841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4954444753467316731892909 1857916782550243774459841)
                    ·
                      refine ⟨1393437586912682830844881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1857916782550243774459841 1393437586912682830844881)
                      ·
                        rfl

theorem cell23_2713710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2].length) (baseStart_2713710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2713710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2713710 prefixEnd_2713710 := by exact prefixLift 2713710
  have htrace : WordTrace (prefixWord ++ tailWord_2713710) baseStart_2713710 baseEnd_2713710 := by
    simpa [prefixWord, tailWord_2713710, baseEnd_2713710] using wordTrace_append hprefix tailTrace_2713710
  have hstable : (prefixWord ++ tailWord_2713710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2713710).length < 2 ^ (prefixWord ++ tailWord_2713710).sum := by decide
  have hdescent : baseEnd_2713710 < baseStart_2713710 := by decide
  rcases family_descends (prefixWord ++ tailWord_2713710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2713733 : List Nat := [1, 3, 1, 1, 5, 2, 1, 2, 1, 6]
def baseStart_2713733 : Nat := 118140960795 + 2713733 * 2 ^ 59
def prefixEnd_2713733 : Nat := 4983230072969 + 3 ^ 40 * 2713733 * 2
def baseEnd_2713733 : Nat := 464483132322578746952425

theorem tailTrace_2713733 : CollatzResearch.WordTrace tailWord_2713733 prefixEnd_2713733 464483132322578746952425 := by
  unfold tailWord_2713733
  simp only [CollatzResearch.WordTrace]
  refine ⟨98977973877616284542881853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65985315918410856361921235 98977973877616284542881853)
  ·
    refine ⟨37116740204106106703580695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98977973877616284542881853 37116740204106106703580695)
    ·
      refine ⟨55675110306159160055371043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37116740204106106703580695 55675110306159160055371043)
      ·
        refine ⟨83512665459238740083056565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55675110306159160055371043 83512665459238740083056565)
        ·
          refine ⟨7829312386803631882786553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 83512665459238740083056565 7829312386803631882786553)
          ·
            refine ⟨5871984290102723912089915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7829312386803631882786553 5871984290102723912089915)
            ·
              refine ⟨8807976435154085868134873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5871984290102723912089915 8807976435154085868134873)
              ·
                refine ⟨6605982326365564401101155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8807976435154085868134873 6605982326365564401101155)
                ·
                  refine ⟨9908973489548346601651733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6605982326365564401101155 9908973489548346601651733)
                  ·
                    refine ⟨464483132322578746952425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9908973489548346601651733 464483132322578746952425)
                    ·
                      rfl

theorem cell23_2713733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 2, 1, 6].length) (baseStart_2713733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2713733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2713733 prefixEnd_2713733 := by exact prefixLift 2713733
  have htrace : WordTrace (prefixWord ++ tailWord_2713733) baseStart_2713733 baseEnd_2713733 := by
    simpa [prefixWord, tailWord_2713733, baseEnd_2713733] using wordTrace_append hprefix tailTrace_2713733
  have hstable : (prefixWord ++ tailWord_2713733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2713733).length < 2 ^ (prefixWord ++ tailWord_2713733).sum := by decide
  have hdescent : baseEnd_2713733 < baseStart_2713733 := by decide
  rcases family_descends (prefixWord ++ tailWord_2713733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2713751 : List Nat := [1, 1, 3, 3, 4, 2, 2, 2, 1, 1, 3]
def baseStart_2713751 : Nat := 118140960795 + 2713751 * 2 ^ 59
def prefixEnd_2713751 : Nat := 4983230072969 + 3 ^ 40 * 2713751 * 2
def baseEnd_2713751 : Nat := 1393458639619517170432193

theorem tailTrace_2713751 : CollatzResearch.WordTrace tailWord_2713751 prefixEnd_2713751 1393458639619517170432193 := by
  unfold tailWord_2713751
  simp only [CollatzResearch.WordTrace]
  refine ⟨98978630391551073617037107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65985753594367382411358071 98978630391551073617037107)
  ·
    refine ⟨148467945587326610425555661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98978630391551073617037107 148467945587326610425555661)
    ·
      refine ⟨55675479595247478909583373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 148467945587326610425555661 55675479595247478909583373)
      ·
        refine ⟨20878304848217804591093765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55675479595247478909583373 20878304848217804591093765)
        ·
          refine ⟨3914682159040838360830081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20878304848217804591093765 3914682159040838360830081)
          ·
            refine ⟨2936011619280628770622561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3914682159040838360830081 2936011619280628770622561)
            ·
              refine ⟨2202008714460471577966921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2936011619280628770622561 2202008714460471577966921)
              ·
                refine ⟨1651506535845353683475191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2202008714460471577966921 1651506535845353683475191)
                ·
                  refine ⟨2477259803768030525212787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1651506535845353683475191 2477259803768030525212787)
                  ·
                    refine ⟨3715889705652045787819181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2477259803768030525212787 3715889705652045787819181)
                    ·
                      refine ⟨1393458639619517170432193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3715889705652045787819181 1393458639619517170432193)
                      ·
                        rfl

theorem cell23_2713751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 2, 2, 1, 1, 3].length) (baseStart_2713751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2713751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2713751 prefixEnd_2713751 := by exact prefixLift 2713751
  have htrace : WordTrace (prefixWord ++ tailWord_2713751) baseStart_2713751 baseEnd_2713751 := by
    simpa [prefixWord, tailWord_2713751, baseEnd_2713751] using wordTrace_append hprefix tailTrace_2713751
  have hstable : (prefixWord ++ tailWord_2713751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2713751).length < 2 ^ (prefixWord ++ tailWord_2713751).sum := by decide
  have hdescent : baseEnd_2713751 < baseStart_2713751 := by decide
  rcases family_descends (prefixWord ++ tailWord_2713751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2713903 : List Nat := [1, 1, 2, 1, 2, 1, 4, 3, 1, 3, 4]
def baseStart_2713903 : Nat := 118140960795 + 2713903 * 2 ^ 59
def prefixEnd_2713903 : Nat := 4983230072969 + 3 ^ 40 * 2713903 * 2
def baseEnd_2713903 : Nat := 1393536688679000575731493

theorem tailTrace_2713903 : CollatzResearch.WordTrace tailWord_2713903 prefixEnd_2713903 1393536688679000575731493 := by
  unfold tailWord_2713903
  simp only [CollatzResearch.WordTrace]
  refine ⟨98984174287000403576570363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65989449524666935717713575 98984174287000403576570363)
  ·
    refine ⟨148476261430500605364855545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98984174287000403576570363 148476261430500605364855545)
    ·
      refine ⟨111357196072875454023641659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148476261430500605364855545 111357196072875454023641659)
      ·
        refine ⟨167035794109313181035462489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111357196072875454023641659 167035794109313181035462489)
        ·
          refine ⟨125276845581984885776596867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 167035794109313181035462489 125276845581984885776596867)
          ·
            refine ⟨187915268372977328664895301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125276845581984885776596867 187915268372977328664895301)
            ·
              refine ⟨35234112819933249124667869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 187915268372977328664895301 35234112819933249124667869)
              ·
                refine ⟨13212792307474968421750451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35234112819933249124667869 13212792307474968421750451)
                ·
                  refine ⟨19819188461212452632625677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13212792307474968421750451 19819188461212452632625677)
                  ·
                    refine ⟨7432195672954669737234629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19819188461212452632625677 7432195672954669737234629)
                    ·
                      refine ⟨1393536688679000575731493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7432195672954669737234629 1393536688679000575731493)
                      ·
                        rfl

theorem cell23_2713903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 3, 1, 3, 4].length) (baseStart_2713903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2713903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2713903 prefixEnd_2713903 := by exact prefixLift 2713903
  have htrace : WordTrace (prefixWord ++ tailWord_2713903) baseStart_2713903 baseEnd_2713903 := by
    simpa [prefixWord, tailWord_2713903, baseEnd_2713903] using wordTrace_append hprefix tailTrace_2713903
  have hstable : (prefixWord ++ tailWord_2713903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2713903).length < 2 ^ (prefixWord ++ tailWord_2713903).sum := by decide
  have hdescent : baseEnd_2713903 < baseStart_2713903 := by decide
  rcases family_descends (prefixWord ++ tailWord_2713903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2713921 : List Nat := [1, 2, 5, 2, 2, 2, 2, 2, 5]
def baseStart_2713921 : Nat := 118140960795 + 2713921 * 2 ^ 59
def prefixEnd_2713921 : Nat := 4983230072969 + 3 ^ 40 * 2713921 * 2
def baseEnd_2713921 : Nat := 154838436814531278367379

theorem tailTrace_2713921 : CollatzResearch.WordTrace tailWord_2713921 prefixEnd_2713921 154838436814531278367379 := by
  unfold tailWord_2713921
  simp only [CollatzResearch.WordTrace]
  refine ⟨98984830800935192650725617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65989887200623461767150411 98984830800935192650725617)
  ·
    refine ⟨74238623100701394488044213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98984830800935192650725617 74238623100701394488044213)
    ·
      refine ⟨6959870915690755733254145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 74238623100701394488044213 6959870915690755733254145)
      ·
        refine ⟨5219903186768066799940609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6959870915690755733254145 5219903186768066799940609)
        ·
          refine ⟨3914927390076050099955457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5219903186768066799940609 3914927390076050099955457)
          ·
            refine ⟨2936195542557037574966593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3914927390076050099955457 2936195542557037574966593)
            ·
              refine ⟨2202146656917778181224945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2936195542557037574966593 2202146656917778181224945)
              ·
                refine ⟨1651609992688333635918709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2202146656917778181224945 1651609992688333635918709)
                ·
                  refine ⟨154838436814531278367379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1651609992688333635918709 154838436814531278367379)
                  ·
                    rfl

theorem cell23_2713921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 2, 2, 5].length) (baseStart_2713921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2713921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2713921 prefixEnd_2713921 := by exact prefixLift 2713921
  have htrace : WordTrace (prefixWord ++ tailWord_2713921) baseStart_2713921 baseEnd_2713921 := by
    simpa [prefixWord, tailWord_2713921, baseEnd_2713921] using wordTrace_append hprefix tailTrace_2713921
  have hstable : (prefixWord ++ tailWord_2713921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2713921).length < 2 ^ (prefixWord ++ tailWord_2713921).sum := by decide
  have hdescent : baseEnd_2713921 < baseStart_2713921 := by decide
  rcases family_descends (prefixWord ++ tailWord_2713921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2713937 : List Nat := [1, 2, 2, 1, 4, 3, 1, 1, 2, 4, 2]
def baseStart_2713937 : Nat := 118140960795 + 2713937 * 2 ^ 59
def prefixEnd_2713937 : Nat := 4983230072969 + 3 ^ 40 * 2713937 * 2
def baseEnd_2713937 : Nat := 1393554147021253442706337

theorem tailTrace_2713937 : CollatzResearch.WordTrace tailWord_2713937 prefixEnd_2713937 1393554147021253442706337 := by
  unfold tailWord_2713937
  simp only [CollatzResearch.WordTrace]
  refine ⟨98985414368877227383308065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65990276245918151588872043 98985414368877227383308065)
  ·
    refine ⟨74239060776657920537481049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98985414368877227383308065 74239060776657920537481049)
    ·
      refine ⟨55679295582493440403110787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74239060776657920537481049 55679295582493440403110787)
      ·
        refine ⟨83518943373740160604666181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55679295582493440403110787 83518943373740160604666181)
        ·
          refine ⟨15659801882576280113374909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 83518943373740160604666181 15659801882576280113374909)
          ·
            refine ⟨5872425705966105042515591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15659801882576280113374909 5872425705966105042515591)
            ·
              refine ⟨8808638558949157563773387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5872425705966105042515591 8808638558949157563773387)
              ·
                refine ⟨13212957838423736345660081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8808638558949157563773387 13212957838423736345660081)
                ·
                  refine ⟨9909718378817802259245061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13212957838423736345660081 9909718378817802259245061)
                  ·
                    refine ⟨1858072196028337923608449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9909718378817802259245061 1858072196028337923608449)
                    ·
                      refine ⟨1393554147021253442706337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1858072196028337923608449 1393554147021253442706337)
                      ·
                        rfl

theorem cell23_2713937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 1, 2, 4, 2].length) (baseStart_2713937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2713937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2713937 prefixEnd_2713937 := by exact prefixLift 2713937
  have htrace : WordTrace (prefixWord ++ tailWord_2713937) baseStart_2713937 baseEnd_2713937 := by
    simpa [prefixWord, tailWord_2713937, baseEnd_2713937] using wordTrace_append hprefix tailTrace_2713937
  have hstable : (prefixWord ++ tailWord_2713937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2713937).length < 2 ^ (prefixWord ++ tailWord_2713937).sum := by decide
  have hdescent : baseEnd_2713937 < baseStart_2713937 := by decide
  rcases family_descends (prefixWord ++ tailWord_2713937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2713954 : List Nat := [3, 3, 2, 1, 1, 4, 1, 1, 2, 1, 4]
def baseStart_2713954 : Nat := 118140960795 + 2713954 * 2 ^ 59
def prefixEnd_2713954 : Nat := 4983230072969 + 3 ^ 40 * 2713954 * 2
def baseEnd_2713954 : Nat := 1393562876192379876193759

theorem tailTrace_2713954 : CollatzResearch.WordTrace tailWord_2713954 prefixEnd_2713954 1393562876192379876193759 := by
  unfold tailWord_2713954
  simp only [CollatzResearch.WordTrace]
  refine ⟨24746508602453909821669229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65990689606543759524451277 24746508602453909821669229)
  ·
    refine ⟨9279940725920216183125961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24746508602453909821669229 9279940725920216183125961)
    ·
      refine ⟨6959955544440162137344471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9279940725920216183125961 6959955544440162137344471)
      ·
        refine ⟨10439933316660243206016707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6959955544440162137344471 10439933316660243206016707)
        ·
          refine ⟨15659899974990364809025061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10439933316660243206016707 15659899974990364809025061)
          ·
            refine ⟨2936231245310693401692199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15659899974990364809025061 2936231245310693401692199)
            ·
              refine ⟨4404346867966040102538299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2936231245310693401692199 4404346867966040102538299)
              ·
                refine ⟨6606520301949060153807449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4404346867966040102538299 6606520301949060153807449)
                ·
                  refine ⟨4954890226461795115355587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6606520301949060153807449 4954890226461795115355587)
                  ·
                    refine ⟨7432335339692692673033381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4954890226461795115355587 7432335339692692673033381)
                    ·
                      refine ⟨1393562876192379876193759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7432335339692692673033381 1393562876192379876193759)
                      ·
                        rfl

theorem cell23_2713954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 1, 1, 2, 1, 4].length) (baseStart_2713954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2713954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2713954 prefixEnd_2713954 := by exact prefixLift 2713954
  have htrace : WordTrace (prefixWord ++ tailWord_2713954) baseStart_2713954 baseEnd_2713954 := by
    simpa [prefixWord, tailWord_2713954, baseEnd_2713954] using wordTrace_append hprefix tailTrace_2713954
  have hstable : (prefixWord ++ tailWord_2713954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2713954).length < 2 ^ (prefixWord ++ tailWord_2713954).sum := by decide
  have hdescent : baseEnd_2713954 < baseStart_2713954 := by decide
  rcases family_descends (prefixWord ++ tailWord_2713954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2713957 : List Nat := [1, 3, 1, 3, 1, 3, 3, 1, 2, 2, 3]
def baseStart_2713957 : Nat := 118140960795 + 2713957 * 2 ^ 59
def prefixEnd_2713957 : Nat := 4983230072969 + 3 ^ 40 * 2713957 * 2
def baseEnd_2713957 : Nat := 1393564416634343364456245

theorem tailTrace_2713957 : CollatzResearch.WordTrace tailWord_2713957 prefixEnd_2713957 1393564416634343364456245 := by
  unfold tailWord_2713957
  simp only [CollatzResearch.WordTrace]
  refine ⟨98986143828804770799036125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65990762552536513866024083 98986143828804770799036125)
  ·
    refine ⟨37119803935801789049638547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98986143828804770799036125 37119803935801789049638547)
    ·
      refine ⟨55679705903702683574457821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37119803935801789049638547 55679705903702683574457821)
      ·
        refine ⟨20879889713888506340421683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55679705903702683574457821 20879889713888506340421683)
        ·
          refine ⟨31319834570832759510632525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20879889713888506340421683 31319834570832759510632525)
          ·
            refine ⟨11744937964062284816487197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31319834570832759510632525 11744937964062284816487197)
            ·
              refine ⟨4404351736523356806182699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11744937964062284816487197 4404351736523356806182699)
              ·
                refine ⟨6606527604785035209274049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4404351736523356806182699 6606527604785035209274049)
                ·
                  refine ⟨4954895703588776406955537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6606527604785035209274049 4954895703588776406955537)
                  ·
                    refine ⟨3716171777691582305216653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4954895703588776406955537 3716171777691582305216653)
                    ·
                      refine ⟨1393564416634343364456245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3716171777691582305216653 1393564416634343364456245)
                      ·
                        rfl

theorem cell23_2713957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 3, 1, 2, 2, 3].length) (baseStart_2713957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2713957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2713957 prefixEnd_2713957 := by exact prefixLift 2713957
  have htrace : WordTrace (prefixWord ++ tailWord_2713957) baseStart_2713957 baseEnd_2713957 := by
    simpa [prefixWord, tailWord_2713957, baseEnd_2713957] using wordTrace_append hprefix tailTrace_2713957
  have hstable : (prefixWord ++ tailWord_2713957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2713957).length < 2 ^ (prefixWord ++ tailWord_2713957).sum := by decide
  have hdescent : baseEnd_2713957 < baseStart_2713957 := by decide
  rcases family_descends (prefixWord ++ tailWord_2713957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2713983 : List Nat := [1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 5]
def baseStart_2713983 : Nat := 118140960795 + 2713983 * 2 ^ 59
def prefixEnd_2713983 : Nat := 4983230072969 + 3 ^ 40 * 2713983 * 2
def baseEnd_2713983 : Nat := 1393577767131360262731125

theorem tailTrace_2713983 : CollatzResearch.WordTrace tailWord_2713983 prefixEnd_2713983 1393577767131360262731125 := by
  unfold tailWord_2713983
  simp only [CollatzResearch.WordTrace]
  refine ⟨98987092126710577239482603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65991394751140384826321735 98987092126710577239482603)
  ·
    refine ⟨148480638190065865859223905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98987092126710577239482603 148480638190065865859223905)
    ·
      refine ⟨111360478642549399394417929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148480638190065865859223905 111360478642549399394417929)
      ·
        refine ⟨83520358981912049545813447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111360478642549399394417929 83520358981912049545813447)
        ·
          refine ⟨125280538472868074318720171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83520358981912049545813447 125280538472868074318720171)
          ·
            refine ⟨187920807709302111478080257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125280538472868074318720171 187920807709302111478080257)
            ·
              refine ⟨140940605781976583608560193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 187920807709302111478080257 140940605781976583608560193)
              ·
                refine ⟨105705454336482437706420145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 140940605781976583608560193 105705454336482437706420145)
                ·
                  refine ⟨79279090752361828279815109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 105705454336482437706420145 79279090752361828279815109)
                  ·
                    refine ⟨14864829516067842802465333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 79279090752361828279815109 14864829516067842802465333)
                    ·
                      refine ⟨1393577767131360262731125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14864829516067842802465333 1393577767131360262731125)
                      ·
                        rfl

theorem cell23_2713983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 5].length) (baseStart_2713983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2713983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2713983 prefixEnd_2713983 := by exact prefixLift 2713983
  have htrace : WordTrace (prefixWord ++ tailWord_2713983) baseStart_2713983 baseEnd_2713983 := by
    simpa [prefixWord, tailWord_2713983, baseEnd_2713983] using wordTrace_append hprefix tailTrace_2713983
  have hstable : (prefixWord ++ tailWord_2713983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2713983).length < 2 ^ (prefixWord ++ tailWord_2713983).sum := by decide
  have hdescent : baseEnd_2713983 < baseStart_2713983 := by decide
  rcases family_descends (prefixWord ++ tailWord_2713983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2714020 : List Nat := [2, 3, 1, 2, 1, 1, 2, 4, 1, 6]
def baseStart_2714020 : Nat := 118140960795 + 2714020 * 2 ^ 59
def prefixEnd_2714020 : Nat := 4983230072969 + 3 ^ 40 * 2714020 * 2
def baseEnd_2714020 : Nat := 464532255305192205989485

theorem tailTrace_2714020 : CollatzResearch.WordTrace tailWord_2714020 prefixEnd_2714020 464532255305192205989485 := by
  unfold tailWord_2714020
  simp only [CollatzResearch.WordTrace]
  refine ⟨49494220813788266279289757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65992294418384355039053009 49494220813788266279289757)
  ·
    refine ⟨18560332805170599854733659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49494220813788266279289757 18560332805170599854733659)
    ·
      refine ⟨27840499207755899782100489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18560332805170599854733659 27840499207755899782100489)
      ·
        refine ⟨20880374405816924836575367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27840499207755899782100489 20880374405816924836575367)
        ·
          refine ⟨31320561608725387254863051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20880374405816924836575367 31320561608725387254863051)
          ·
            refine ⟨46980842413088080882294577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31320561608725387254863051 46980842413088080882294577)
            ·
              refine ⟨35235631809816060661720933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46980842413088080882294577 35235631809816060661720933)
              ·
                refine ⟨6606680964340511374072675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35235631809816060661720933 6606680964340511374072675)
                ·
                  refine ⟨9910021446510767061109013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6606680964340511374072675 9910021446510767061109013)
                  ·
                    refine ⟨464532255305192205989485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9910021446510767061109013 464532255305192205989485)
                    ·
                      rfl

theorem cell23_2714020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 4, 1, 6].length) (baseStart_2714020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2714020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2714020 prefixEnd_2714020 := by exact prefixLift 2714020
  have htrace : WordTrace (prefixWord ++ tailWord_2714020) baseStart_2714020 baseEnd_2714020 := by
    simpa [prefixWord, tailWord_2714020, baseEnd_2714020] using wordTrace_append hprefix tailTrace_2714020
  have hstable : (prefixWord ++ tailWord_2714020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2714020).length < 2 ^ (prefixWord ++ tailWord_2714020).sum := by decide
  have hdescent : baseEnd_2714020 < baseStart_2714020 := by decide
  rcases family_descends (prefixWord ++ tailWord_2714020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2714024 : List Nat := [2, 1, 6, 1, 1, 1, 2, 3, 1, 5]
def baseStart_2714024 : Nat := 118140960795 + 2714024 * 2 ^ 59
def prefixEnd_2714024 : Nat := 4983230072969 + 3 ^ 40 * 2714024 * 2
def baseEnd_2714024 : Nat := 464532939946064867439479

theorem tailTrace_2714024 : CollatzResearch.WordTrace tailWord_2714024 prefixEnd_2714024 464532939946064867439479 := by
  unfold tailWord_2714024
  simp only [CollatzResearch.WordTrace]
  refine ⟨49494293759781020620862563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65992391679708027494483417 49494293759781020620862563)
  ·
    refine ⟨74241440639671530931293845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49494293759781020620862563 74241440639671530931293845)
    ·
      refine ⟨3480067529984603012404399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 74241440639671530931293845 3480067529984603012404399)
      ·
        refine ⟨5220101294976904518606599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3480067529984603012404399 5220101294976904518606599)
        ·
          refine ⟨7830151942465356777909899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5220101294976904518606599 7830151942465356777909899)
          ·
            refine ⟨11745227913698035166864849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7830151942465356777909899 11745227913698035166864849)
            ·
              refine ⟨8808920935273526375148637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11745227913698035166864849 8808920935273526375148637)
              ·
                refine ⟨3303345350727572390680739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8808920935273526375148637 3303345350727572390680739)
                ·
                  refine ⟨4955018026091358586021109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3303345350727572390680739 4955018026091358586021109)
                  ·
                    refine ⟨464532939946064867439479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4955018026091358586021109 464532939946064867439479)
                    ·
                      rfl

theorem cell23_2714024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 3, 1, 5].length) (baseStart_2714024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2714024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2714024 prefixEnd_2714024 := by exact prefixLift 2714024
  have htrace : WordTrace (prefixWord ++ tailWord_2714024) baseStart_2714024 baseEnd_2714024 := by
    simpa [prefixWord, tailWord_2714024, baseEnd_2714024] using wordTrace_append hprefix tailTrace_2714024
  have hstable : (prefixWord ++ tailWord_2714024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2714024).length < 2 ^ (prefixWord ++ tailWord_2714024).sum := by decide
  have hdescent : baseEnd_2714024 < baseStart_2714024 := by decide
  rcases family_descends (prefixWord ++ tailWord_2714024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2714101 : List Nat := [1, 3, 5, 1, 3, 1, 1, 8]
def baseStart_2714101 : Nat := 118140960795 + 2714101 * 2 ^ 59
def prefixEnd_2714101 : Nat := 4983230072969 + 3 ^ 40 * 2714101 * 2
def baseEnd_2714101 : Nat := 51616235475873733372429

theorem tailTrace_2714101 : CollatzResearch.WordTrace tailWord_2714101 prefixEnd_2714101 51616235475873733372429 := by
  unfold tailWord_2714101
  simp only [CollatzResearch.WordTrace]
  refine ⟨98991395940283083392278157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65994263960188722261518771 98991395940283083392278157)
  ·
    refine ⟨37121773477606156272104309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98991395940283083392278157 37121773477606156272104309)
    ·
      refine ⟨3480166263525577150509779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 37121773477606156272104309 3480166263525577150509779)
      ·
        refine ⟨5220249395288365725764669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3480166263525577150509779 5220249395288365725764669)
        ·
          refine ⟨1957593523233137147161751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5220249395288365725764669 1957593523233137147161751)
          ·
            refine ⟨2936390284849705720742627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1957593523233137147161751 2936390284849705720742627)
            ·
              refine ⟨4404585427274558581113941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2936390284849705720742627 4404585427274558581113941)
              ·
                refine ⟨51616235475873733372429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4404585427274558581113941 51616235475873733372429)
                ·
                  rfl

theorem cell23_2714101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 1, 8].length) (baseStart_2714101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2714101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2714101 prefixEnd_2714101 := by exact prefixLift 2714101
  have htrace : WordTrace (prefixWord ++ tailWord_2714101) baseStart_2714101 baseEnd_2714101 := by
    simpa [prefixWord, tailWord_2714101, baseEnd_2714101] using wordTrace_append hprefix tailTrace_2714101
  have hstable : (prefixWord ++ tailWord_2714101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2714101).length < 2 ^ (prefixWord ++ tailWord_2714101).sum := by decide
  have hdescent : baseEnd_2714101 < baseStart_2714101 := by decide
  rcases family_descends (prefixWord ++ tailWord_2714101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2714118 : List Nat := [6, 2, 1, 1, 1, 2, 3, 7]
def baseStart_2714118 : Nat := 118140960795 + 2714118 * 2 ^ 59
def prefixEnd_2714118 : Nat := 4983230072969 + 3 ^ 40 * 2714118 * 2
def baseEnd_2714118 : Nat := 51616558778508045723815

theorem tailTrace_2714118 : CollatzResearch.WordTrace tailWord_2714118 prefixEnd_2714118 51616558778508045723815 := by
  unfold tailWord_2714118
  simp only [CollatzResearch.WordTrace]
  refine ⟨3093500499413171727988969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 65994677320814330197098005 3093500499413171727988969)
  ·
    refine ⟨2320125374559878795991727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3093500499413171727988969 2320125374559878795991727)
    ·
      refine ⟨3480188061839818193987591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2320125374559878795991727 3480188061839818193987591)
      ·
        refine ⟨5220282092759727290981387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3480188061839818193987591 5220282092759727290981387)
        ·
          refine ⟨7830423139139590936472081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5220282092759727290981387 7830423139139590936472081)
          ·
            refine ⟨5872817354354693202354061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7830423139139590936472081 5872817354354693202354061)
            ·
              refine ⟨2202306507883009950882773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5872817354354693202354061 2202306507883009950882773)
              ·
                refine ⟨51616558778508045723815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2202306507883009950882773 51616558778508045723815)
                ·
                  rfl

theorem cell23_2714118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 3, 7].length) (baseStart_2714118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2714118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2714118 prefixEnd_2714118 := by exact prefixLift 2714118
  have htrace : WordTrace (prefixWord ++ tailWord_2714118) baseStart_2714118 baseEnd_2714118 := by
    simpa [prefixWord, tailWord_2714118, baseEnd_2714118] using wordTrace_append hprefix tailTrace_2714118
  have hstable : (prefixWord ++ tailWord_2714118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2714118).length < 2 ^ (prefixWord ++ tailWord_2714118).sum := by decide
  have hdescent : baseEnd_2714118 < baseStart_2714118 := by decide
  rcases family_descends (prefixWord ++ tailWord_2714118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2714147 : List Nat := [1, 1, 1, 4, 4, 1, 1, 2, 2, 2, 4]
def baseStart_2714147 : Nat := 118140960795 + 2714147 * 2 ^ 59
def prefixEnd_2714147 : Nat := 4983230072969 + 3 ^ 40 * 2714147 * 2
def baseEnd_2714147 : Nat := 1393661977958697621080371

theorem tailTrace_2714147 : CollatzResearch.WordTrace tailWord_2714147 prefixEnd_2714147 1393661977958697621080371 := by
  unfold tailWord_2714147
  simp only [CollatzResearch.WordTrace]
  refine ⟨98993073698116433248452695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65995382465410955498968463 98993073698116433248452695)
  ·
    refine ⟨148489610547174649872679043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98993073698116433248452695 148489610547174649872679043)
    ·
      refine ⟨222734415820761974809018565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148489610547174649872679043 222734415820761974809018565)
      ·
        refine ⟨41762702966392870276690981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 222734415820761974809018565 41762702966392870276690981)
        ·
          refine ⟨7830506806198663176879559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41762702966392870276690981 7830506806198663176879559)
          ·
            refine ⟨11745760209297994765319339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7830506806198663176879559 11745760209297994765319339)
            ·
              refine ⟨17618640313946992147979009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11745760209297994765319339 17618640313946992147979009)
              ·
                refine ⟨13213980235460244110984257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17618640313946992147979009 13213980235460244110984257)
                ·
                  refine ⟨9910485176595183083238193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13213980235460244110984257 9910485176595183083238193)
                  ·
                    refine ⟨7432863882446387312428645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9910485176595183083238193 7432863882446387312428645)
                    ·
                      refine ⟨1393661977958697621080371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7432863882446387312428645 1393661977958697621080371)
                      ·
                        rfl

theorem cell23_2714147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 2, 2, 2, 4].length) (baseStart_2714147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2714147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2714147 prefixEnd_2714147 := by exact prefixLift 2714147
  have htrace : WordTrace (prefixWord ++ tailWord_2714147) baseStart_2714147 baseEnd_2714147 := by
    simpa [prefixWord, tailWord_2714147, baseEnd_2714147] using wordTrace_append hprefix tailTrace_2714147
  have hstable : (prefixWord ++ tailWord_2714147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2714147).length < 2 ^ (prefixWord ++ tailWord_2714147).sum := by decide
  have hdescent : baseEnd_2714147 < baseStart_2714147 := by decide
  rcases family_descends (prefixWord ++ tailWord_2714147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2714167 : List Nat := [1, 1, 3, 1, 2, 3, 1, 3, 2, 3, 3]
def baseStart_2714167 : Nat := 118140960795 + 2714167 * 2 ^ 59
def prefixEnd_2714167 : Nat := 4983230072969 + 3 ^ 40 * 2714167 * 2
def baseEnd_2714167 : Nat := 1393672247571787542830279

theorem tailTrace_2714167 : CollatzResearch.WordTrace tailWord_2714167 prefixEnd_2714167 1393672247571787542830279 := by
  unfold tailWord_2714167
  simp only [CollatzResearch.WordTrace]
  refine ⟨98993803158043976664180755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65995868772029317776120503 98993803158043976664180755)
  ·
    refine ⟨148490704737065964996271133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98993803158043976664180755 148490704737065964996271133)
    ·
      refine ⟨55684014276399736873601675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 148490704737065964996271133 55684014276399736873601675)
      ·
        refine ⟨83526021414599605310402513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55684014276399736873601675 83526021414599605310402513)
        ·
          refine ⟨62644516060949703982801885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83526021414599605310402513 62644516060949703982801885)
          ·
            refine ⟨23491693522856138993550707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62644516060949703982801885 23491693522856138993550707)
            ·
              refine ⟨35237540284284208490326061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23491693522856138993550707 35237540284284208490326061)
              ·
                refine ⟨13214077606606578183872273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35237540284284208490326061 13214077606606578183872273)
                ·
                  refine ⟨9910558204954933637904205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13214077606606578183872273 9910558204954933637904205)
                  ·
                    refine ⟨3716459326858100114214077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9910558204954933637904205 3716459326858100114214077)
                    ·
                      refine ⟨1393672247571787542830279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3716459326858100114214077 1393672247571787542830279)
                      ·
                        rfl

theorem cell23_2714167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 3, 2, 3, 3].length) (baseStart_2714167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2714167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2714167 prefixEnd_2714167 := by exact prefixLift 2714167
  have htrace : WordTrace (prefixWord ++ tailWord_2714167) baseStart_2714167 baseEnd_2714167 := by
    simpa [prefixWord, tailWord_2714167, baseEnd_2714167] using wordTrace_append hprefix tailTrace_2714167
  have hstable : (prefixWord ++ tailWord_2714167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2714167).length < 2 ^ (prefixWord ++ tailWord_2714167).sum := by decide
  have hdescent : baseEnd_2714167 < baseStart_2714167 := by decide
  rcases family_descends (prefixWord ++ tailWord_2714167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2714168 : List Nat := [2, 1, 2, 1, 4, 1, 5, 1, 2, 2, 2]
def baseStart_2714168 : Nat := 118140960795 + 2714168 * 2 ^ 59
def prefixEnd_2714168 : Nat := 4983230072969 + 3 ^ 40 * 2714168 * 2
def baseEnd_2714168 : Nat := 1393672761052442038917775

theorem tailTrace_2714168 : CollatzResearch.WordTrace tailWord_2714168 prefixEnd_2714168 1393672761052442038917775 := by
  unfold tailWord_2714168
  simp only [CollatzResearch.WordTrace]
  refine ⟨49496919815520176917483579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65995893087360235889978105 49496919815520176917483579)
  ·
    refine ⟨74245379723280265376225369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49496919815520176917483579 74245379723280265376225369)
    ·
      refine ⟨55684034792460199032169027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74245379723280265376225369 55684034792460199032169027)
      ·
        refine ⟨83526052188690298548253541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55684034792460199032169027 83526052188690298548253541)
        ·
          refine ⟨15661134785379430977797539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 83526052188690298548253541 15661134785379430977797539)
          ·
            refine ⟨23491702178069146466696309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15661134785379430977797539 23491702178069146466696309)
            ·
              refine ⟨2202347079193982481252779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23491702178069146466696309 2202347079193982481252779)
              ·
                refine ⟨3303520618790973721879169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2202347079193982481252779 3303520618790973721879169)
                ·
                  refine ⟨2477640464093230291409377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3303520618790973721879169 2477640464093230291409377)
                  ·
                    refine ⟨1858230348069922718557033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2477640464093230291409377 1858230348069922718557033)
                    ·
                      refine ⟨1393672761052442038917775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1858230348069922718557033 1393672761052442038917775)
                      ·
                        rfl

theorem cell23_2714168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 5, 1, 2, 2, 2].length) (baseStart_2714168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2714168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2714168 prefixEnd_2714168 := by exact prefixLift 2714168
  have htrace : WordTrace (prefixWord ++ tailWord_2714168) baseStart_2714168 baseEnd_2714168 := by
    simpa [prefixWord, tailWord_2714168, baseEnd_2714168] using wordTrace_append hprefix tailTrace_2714168
  have hstable : (prefixWord ++ tailWord_2714168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2714168).length < 2 ^ (prefixWord ++ tailWord_2714168).sum := by decide
  have hdescent : baseEnd_2714168 < baseStart_2714168 := by decide
  rcases family_descends (prefixWord ++ tailWord_2714168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2714227 : List Nat := [1, 1, 1, 2, 2, 1, 1, 6, 1, 4, 3]
def baseStart_2714227 : Nat := 118140960795 + 2714227 * 2 ^ 59
def prefixEnd_2714227 : Nat := 4983230072969 + 3 ^ 40 * 2714227 * 2
def baseEnd_2714227 : Nat := 1393703056411057308080003

theorem tailTrace_2714227 : CollatzResearch.WordTrace tailWord_2714227 prefixEnd_2714227 1393703056411057308080003 := by
  unfold tailWord_2714227
  simp only [CollatzResearch.WordTrace]
  refine ⟨98995991537826606911364935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65997327691884404607576623 98995991537826606911364935)
  ·
    refine ⟨148493987306739910367047403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98995991537826606911364935 148493987306739910367047403)
    ·
      refine ⟨222740980960109865550571105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148493987306739910367047403 222740980960109865550571105)
      ·
        refine ⟨167055735720082399162928329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 222740980960109865550571105 167055735720082399162928329)
        ·
          refine ⟨125291801790061799372196247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 167055735720082399162928329 125291801790061799372196247)
          ·
            refine ⟨187937702685092699058294371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125291801790061799372196247 187937702685092699058294371)
            ·
              refine ⟨281906554027639048587441557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 187937702685092699058294371 281906554027639048587441557)
              ·
                refine ⟨13214369720045580402536323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 281906554027639048587441557 13214369720045580402536323)
                ·
                  refine ⟨19821554580068370603804485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13214369720045580402536323 19821554580068370603804485)
                  ·
                    refine ⟨3716541483762819488213341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19821554580068370603804485 3716541483762819488213341)
                    ·
                      refine ⟨1393703056411057308080003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3716541483762819488213341 1393703056411057308080003)
                      ·
                        rfl

theorem cell23_2714227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 6, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 6, 1, 4, 3].length) (baseStart_2714227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2714227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2714227 prefixEnd_2714227 := by exact prefixLift 2714227
  have htrace : WordTrace (prefixWord ++ tailWord_2714227) baseStart_2714227 baseEnd_2714227 := by
    simpa [prefixWord, tailWord_2714227, baseEnd_2714227] using wordTrace_append hprefix tailTrace_2714227
  have hstable : (prefixWord ++ tailWord_2714227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2714227).length < 2 ^ (prefixWord ++ tailWord_2714227).sum := by decide
  have hdescent : baseEnd_2714227 < baseStart_2714227 := by decide
  rcases family_descends (prefixWord ++ tailWord_2714227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2714257 : List Nat := [1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 3]
def baseStart_2714257 : Nat := 118140960795 + 2714257 * 2 ^ 59
def prefixEnd_2714257 : Nat := 4983230072969 + 3 ^ 40 * 2714257 * 2
def baseEnd_2714257 : Nat := 1393718460830692190704865

theorem tailTrace_2714257 : CollatzResearch.WordTrace tailWord_2714257 prefixEnd_2714257 1393718460830692190704865 := by
  unfold tailWord_2714257
  simp only [CollatzResearch.WordTrace]
  refine ⟨98997085727717922034957025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65998057151811948023304683 98997085727717922034957025)
  ·
    refine ⟨74247814295788441526217769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98997085727717922034957025 74247814295788441526217769)
    ·
      refine ⟨55685860721841331144663327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74247814295788441526217769 55685860721841331144663327)
      ·
        refine ⟨83528791082761996716994991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55685860721841331144663327 83528791082761996716994991)
        ·
          refine ⟨125293186624142995075492487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83528791082761996716994991 125293186624142995075492487)
          ·
            refine ⟨187939779936214492613238731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125293186624142995075492487 187939779936214492613238731)
            ·
              refine ⟨281909669904321738919858097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 187939779936214492613238731 281909669904321738919858097)
              ·
                refine ⟨211432252428241304189893573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 281909669904321738919858097 211432252428241304189893573)
                ·
                  refine ⟨39643547330295244535605045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 211432252428241304189893573 39643547330295244535605045)
                  ·
                    refine ⟨3716582562215179175212973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39643547330295244535605045 3716582562215179175212973)
                    ·
                      refine ⟨1393718460830692190704865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3716582562215179175212973 1393718460830692190704865)
                      ·
                        rfl

theorem cell23_2714257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 3].length) (baseStart_2714257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2714257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2714257 prefixEnd_2714257 := by exact prefixLift 2714257
  have htrace : WordTrace (prefixWord ++ tailWord_2714257) baseStart_2714257 baseEnd_2714257 := by
    simpa [prefixWord, tailWord_2714257, baseEnd_2714257] using wordTrace_append hprefix tailTrace_2714257
  have hstable : (prefixWord ++ tailWord_2714257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2714257).length < 2 ^ (prefixWord ++ tailWord_2714257).sum := by decide
  have hdescent : baseEnd_2714257 < baseStart_2714257 := by decide
  rcases family_descends (prefixWord ++ tailWord_2714257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2714264 : List Nat := [2, 1, 2, 4, 1, 1, 4, 2, 6]
def baseStart_2714264 : Nat := 118140960795 + 2714264 * 2 ^ 59
def prefixEnd_2714264 : Nat := 4983230072969 + 3 ^ 40 * 2714264 * 2
def baseEnd_2714264 : Nat := 154858006132808184813037

theorem tailTrace_2714264 : CollatzResearch.WordTrace tailWord_2714264 prefixEnd_2714264 154858006132808184813037 := by
  unfold tailWord_2714264
  simp only [CollatzResearch.WordTrace]
  refine ⟨49498670519346281115230923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65998227359128374820307897 49498670519346281115230923)
  ·
    refine ⟨74248005779019421672846385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49498670519346281115230923 74248005779019421672846385)
    ·
      refine ⟨55686004334264566254634789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74248005779019421672846385 55686004334264566254634789)
      ·
        refine ⟨10441125812674606172744023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55686004334264566254634789 10441125812674606172744023)
        ·
          refine ⟨15661688719011909259116035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10441125812674606172744023 15661688719011909259116035)
          ·
            refine ⟨23492533078517863888674053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15661688719011909259116035 23492533078517863888674053)
            ·
              refine ⟨4404849952222099479126385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23492533078517863888674053 4404849952222099479126385)
              ·
                refine ⟨3303637464166574609344789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4404849952222099479126385 3303637464166574609344789)
                ·
                  refine ⟨154858006132808184813037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3303637464166574609344789 154858006132808184813037)
                  ·
                    rfl

theorem cell23_2714264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 4, 2, 6].length) (baseStart_2714264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2714264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2714264 prefixEnd_2714264 := by exact prefixLift 2714264
  have htrace : WordTrace (prefixWord ++ tailWord_2714264) baseStart_2714264 baseEnd_2714264 := by
    simpa [prefixWord, tailWord_2714264, baseEnd_2714264] using wordTrace_append hprefix tailTrace_2714264
  have hstable : (prefixWord ++ tailWord_2714264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2714264).length < 2 ^ (prefixWord ++ tailWord_2714264).sum := by decide
  have hdescent : baseEnd_2714264 < baseStart_2714264 := by decide
  rcases family_descends (prefixWord ++ tailWord_2714264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2714268 : List Nat := [2, 2, 3, 2, 2, 2, 1, 4, 1, 4]
def baseStart_2714268 : Nat := 118140960795 + 2714268 * 2 ^ 59
def prefixEnd_2714268 : Nat := 4983230072969 + 3 ^ 40 * 2714268 * 2
def baseEnd_2714268 : Nat := 464574703039297215889105

theorem tailTrace_2714268 : CollatzResearch.WordTrace tailWord_2714268 prefixEnd_2714268 464574703039297215889105 := by
  unfold tailWord_2714268
  simp only [CollatzResearch.WordTrace]
  refine ⟨49498743465339035456803729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65998324620452047275738305 49498743465339035456803729)
  ·
    refine ⟨37124057599004276592602797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49498743465339035456803729 37124057599004276592602797)
    ·
      refine ⟨13921521599626603722226049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37124057599004276592602797 13921521599626603722226049)
      ·
        refine ⟨10441141199719952791669537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13921521599626603722226049 10441141199719952791669537)
        ·
          refine ⟨7830855899789964593752153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10441141199719952791669537 7830855899789964593752153)
          ·
            refine ⟨5873141924842473445314115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7830855899789964593752153 5873141924842473445314115)
            ·
              refine ⟨8809712887263710167971173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5873141924842473445314115 8809712887263710167971173)
              ·
                refine ⟨1651821166361945656494595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8809712887263710167971173 1651821166361945656494595)
                ·
                  refine ⟨2477731749542918484741893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1651821166361945656494595 2477731749542918484741893)
                  ·
                    refine ⟨464574703039297215889105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2477731749542918484741893 464574703039297215889105)
                    ·
                      rfl

theorem cell23_2714268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 4, 1, 4].length) (baseStart_2714268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2714268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2714268 prefixEnd_2714268 := by exact prefixLift 2714268
  have htrace : WordTrace (prefixWord ++ tailWord_2714268) baseStart_2714268 baseEnd_2714268 := by
    simpa [prefixWord, tailWord_2714268, baseEnd_2714268] using wordTrace_append hprefix tailTrace_2714268
  have hstable : (prefixWord ++ tailWord_2714268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2714268).length < 2 ^ (prefixWord ++ tailWord_2714268).sum := by decide
  have hdescent : baseEnd_2714268 < baseStart_2714268 := by decide
  rcases family_descends (prefixWord ++ tailWord_2714268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2714291 : List Nat := [1, 1, 1, 2, 3, 5, 1, 2, 3, 1, 3]
def baseStart_2714291 : Nat := 118140960795 + 2714291 * 2 ^ 59
def prefixEnd_2714291 : Nat := 4983230072969 + 3 ^ 40 * 2714291 * 2
def baseEnd_2714291 : Nat := 1393735919172945057679709

theorem tailTrace_2714291 : CollatzResearch.WordTrace tailWord_2714291 prefixEnd_2714291 1393735919172945057679709 := by
  unfold tailWord_2714291
  simp only [CollatzResearch.WordTrace]
  refine ⟨98998325809594745841694727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65998883873063163894463151 98998325809594745841694727)
  ·
    refine ⟨148497488714392118762542091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98998325809594745841694727 148497488714392118762542091)
    ·
      refine ⟨222746233071588178143813137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148497488714392118762542091 222746233071588178143813137)
      ·
        refine ⟨167059674803691133607859853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 222746233071588178143813137 167059674803691133607859853)
        ·
          refine ⟨62647378051384175102947445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 167059674803691133607859853 62647378051384175102947445)
          ·
            refine ⟨5873191692317266415901323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 62647378051384175102947445 5873191692317266415901323)
            ·
              refine ⟨8809787538475899623851985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5873191692317266415901323 8809787538475899623851985)
              ·
                refine ⟨6607340653856924717888989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8809787538475899623851985 6607340653856924717888989)
                ·
                  refine ⟨2477752745196346769208371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6607340653856924717888989 2477752745196346769208371)
                  ·
                    refine ⟨3716629117794520153812557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2477752745196346769208371 3716629117794520153812557)
                    ·
                      refine ⟨1393735919172945057679709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3716629117794520153812557 1393735919172945057679709)
                      ·
                        rfl

theorem cell23_2714291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 2, 3, 1, 3].length) (baseStart_2714291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2714291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2714291 prefixEnd_2714291 := by exact prefixLift 2714291
  have htrace : WordTrace (prefixWord ++ tailWord_2714291) baseStart_2714291 baseEnd_2714291 := by
    simpa [prefixWord, tailWord_2714291, baseEnd_2714291] using wordTrace_append hprefix tailTrace_2714291
  have hstable : (prefixWord ++ tailWord_2714291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2714291).length < 2 ^ (prefixWord ++ tailWord_2714291).sum := by decide
  have hdescent : baseEnd_2714291 < baseStart_2714291 := by decide
  rcases family_descends (prefixWord ++ tailWord_2714291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2714301 : List Nat := [1, 4, 1, 2, 1, 4, 1, 1, 1, 5, 2]
def baseStart_2714301 : Nat := 118140960795 + 2714301 * 2 ^ 59
def prefixEnd_2714301 : Nat := 4983230072969 + 3 ^ 40 * 2714301 * 2
def baseEnd_2714301 : Nat := 1393741053979490018554663

theorem tailTrace_2714301 : CollatzResearch.WordTrace tailWord_2714301 prefixEnd_2714301 1393741053979490018554663 := by
  unfold tailWord_2714301
  simp only [CollatzResearch.WordTrace]
  refine ⟨98998690539558517549558757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65999127026372345033039171 98998690539558517549558757)
  ·
    refine ⟨18562254476167222040542267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 98998690539558517549558757 18562254476167222040542267)
    ·
      refine ⟨27843381714250833060813401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18562254476167222040542267 27843381714250833060813401)
      ·
        refine ⟨20882536285688124795610051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27843381714250833060813401 20882536285688124795610051)
        ·
          refine ⟨31323804428532187193415077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20882536285688124795610051 31323804428532187193415077)
          ·
            refine ⟨5873213330349785098765327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31323804428532187193415077 5873213330349785098765327)
            ·
              refine ⟨8809819995524677648147991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5873213330349785098765327 8809819995524677648147991)
              ·
                refine ⟨13214729993287016472221987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8809819995524677648147991 13214729993287016472221987)
                ·
                  refine ⟨19822094989930524708332981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13214729993287016472221987 19822094989930524708332981)
                  ·
                    refine ⟨1858321405305986691406217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 19822094989930524708332981 1858321405305986691406217)
                    ·
                      refine ⟨1393741053979490018554663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1858321405305986691406217 1393741053979490018554663)
                      ·
                        rfl

theorem cell23_2714301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 1, 1, 5, 2].length) (baseStart_2714301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2714301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2714301 prefixEnd_2714301 := by exact prefixLift 2714301
  have htrace : WordTrace (prefixWord ++ tailWord_2714301) baseStart_2714301 baseEnd_2714301 := by
    simpa [prefixWord, tailWord_2714301, baseEnd_2714301] using wordTrace_append hprefix tailTrace_2714301
  have hstable : (prefixWord ++ tailWord_2714301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2714301).length < 2 ^ (prefixWord ++ tailWord_2714301).sum := by decide
  have hdescent : baseEnd_2714301 < baseStart_2714301 := by decide
  rcases family_descends (prefixWord ++ tailWord_2714301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2714325 : List Nat := [1, 3, 2, 5, 1, 1, 2, 1, 3, 1, 3]
def baseStart_2714325 : Nat := 118140960795 + 2714325 * 2 ^ 59
def prefixEnd_2714325 : Nat := 4983230072969 + 3 ^ 40 * 2714325 * 2
def baseEnd_2714325 : Nat := 1393753377515197924654553

theorem tailTrace_2714325 : CollatzResearch.WordTrace tailWord_2714325 prefixEnd_2714325 1393753377515197924654553 := by
  unfold tailWord_2714325
  simp only [CollatzResearch.WordTrace]
  refine ⟨98999565891471569648432429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65999710594314379765621619 98999565891471569648432429)
  ·
    refine ⟨37124837209301838618162161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98999565891471569648432429 37124837209301838618162161)
    ·
      refine ⟨27843627906976378963621621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37124837209301838618162161 27843627906976378963621621)
      ·
        refine ⟨2610340116279035527839527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 27843627906976378963621621 2610340116279035527839527)
        ·
          refine ⟨3915510174418553291759291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2610340116279035527839527 3915510174418553291759291)
          ·
            refine ⟨5873265261627829937638937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3915510174418553291759291 5873265261627829937638937)
            ·
              refine ⟨4404948946220872453229203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5873265261627829937638937 4404948946220872453229203)
              ·
                refine ⟨6607423419331308679843805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4404948946220872453229203 6607423419331308679843805)
                ·
                  refine ⟨2477783782249240754941427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6607423419331308679843805 2477783782249240754941427)
                  ·
                    refine ⟨3716675673373861132412141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2477783782249240754941427 3716675673373861132412141)
                    ·
                      refine ⟨1393753377515197924654553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3716675673373861132412141 1393753377515197924654553)
                      ·
                        rfl

theorem cell23_2714325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_2714325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2714325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2714325 prefixEnd_2714325 := by exact prefixLift 2714325
  have htrace : WordTrace (prefixWord ++ tailWord_2714325) baseStart_2714325 baseEnd_2714325 := by
    simpa [prefixWord, tailWord_2714325, baseEnd_2714325] using wordTrace_append hprefix tailTrace_2714325
  have hstable : (prefixWord ++ tailWord_2714325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2714325).length < 2 ^ (prefixWord ++ tailWord_2714325).sum := by decide
  have hdescent : baseEnd_2714325 < baseStart_2714325 := by decide
  rcases family_descends (prefixWord ++ tailWord_2714325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2714341 : List Nat := [1, 3, 1, 4, 1, 4, 1, 1, 1, 6]
def baseStart_2714341 : Nat := 118140960795 + 2714341 * 2 ^ 59
def prefixEnd_2714341 : Nat := 4983230072969 + 3 ^ 40 * 2714341 * 2
def baseEnd_2714341 : Nat := 464587197735223287351493

theorem tailTrace_2714341 : CollatzResearch.WordTrace tailWord_2714341 prefixEnd_2714341 464587197735223287351493 := by
  unfold tailWord_2714341
  simp only [CollatzResearch.WordTrace]
  refine ⟨99000149459413604381014877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66000099639609069587343251 99000149459413604381014877)
  ·
    refine ⟨37125056047280101642880579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99000149459413604381014877 37125056047280101642880579)
    ·
      refine ⟨55687584070920152464320869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37125056047280101642880579 55687584070920152464320869)
      ·
        refine ⟨10441422013297528587060163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55687584070920152464320869 10441422013297528587060163)
        ·
          refine ⟨15662133019946292880590245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10441422013297528587060163 15662133019946292880590245)
          ·
            refine ⟨2936649941239929915110671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15662133019946292880590245 2936649941239929915110671)
            ·
              refine ⟨4404974911859894872666007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2936649941239929915110671 4404974911859894872666007)
              ·
                refine ⟨6607462367789842308999011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4404974911859894872666007 6607462367789842308999011)
                ·
                  refine ⟨9911193551684763463498517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6607462367789842308999011 9911193551684763463498517)
                  ·
                    refine ⟨464587197735223287351493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9911193551684763463498517 464587197735223287351493)
                    ·
                      rfl

theorem cell23_2714341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 1, 1, 1, 6].length) (baseStart_2714341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2714341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2714341 prefixEnd_2714341 := by exact prefixLift 2714341
  have htrace : WordTrace (prefixWord ++ tailWord_2714341) baseStart_2714341 baseEnd_2714341 := by
    simpa [prefixWord, tailWord_2714341, baseEnd_2714341] using wordTrace_append hprefix tailTrace_2714341
  have hstable : (prefixWord ++ tailWord_2714341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2714341).length < 2 ^ (prefixWord ++ tailWord_2714341).sum := by decide
  have hdescent : baseEnd_2714341 < baseStart_2714341 := by decide
  rcases family_descends (prefixWord ++ tailWord_2714341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2714351 : List Nat := [1, 1, 2, 1, 5, 2, 1, 4, 1, 2, 3]
def baseStart_2714351 : Nat := 118140960795 + 2714351 * 2 ^ 59
def prefixEnd_2714351 : Nat := 4983230072969 + 3 ^ 40 * 2714351 * 2
def baseEnd_2714351 : Nat := 1393766728012214822929433

theorem tailTrace_2714351 : CollatzResearch.WordTrace tailWord_2714351 prefixEnd_2714351 1393766728012214822929433 := by
  unfold tailWord_2714351
  simp only [CollatzResearch.WordTrace]
  refine ⟨99000514189377376088878907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66000342792918250725919271 99000514189377376088878907)
  ·
    refine ⟨148500771284066064133318361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99000514189377376088878907 148500771284066064133318361)
    ·
      refine ⟨111375578463049548099988771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148500771284066064133318361 111375578463049548099988771)
      ·
        refine ⟨167063367694574322149983157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111375578463049548099988771 167063367694574322149983157)
        ·
          refine ⟨15662190721366342701560921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 167063367694574322149983157 15662190721366342701560921)
          ·
            refine ⟨11746643041024757026170691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15662190721366342701560921 11746643041024757026170691)
            ·
              refine ⟨17619964561537135539256037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11746643041024757026170691 17619964561537135539256037)
              ·
                refine ⟨3303743355288212913610507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17619964561537135539256037 3303743355288212913610507)
                ·
                  refine ⟨4955615032932319370415761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3303743355288212913610507 4955615032932319370415761)
                  ·
                    refine ⟨3716711274699239527811821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4955615032932319370415761 3716711274699239527811821)
                    ·
                      refine ⟨1393766728012214822929433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3716711274699239527811821 1393766728012214822929433)
                      ·
                        rfl

theorem cell23_2714351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 4, 1, 2, 3].length) (baseStart_2714351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2714351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2714351 prefixEnd_2714351 := by exact prefixLift 2714351
  have htrace : WordTrace (prefixWord ++ tailWord_2714351) baseStart_2714351 baseEnd_2714351 := by
    simpa [prefixWord, tailWord_2714351, baseEnd_2714351] using wordTrace_append hprefix tailTrace_2714351
  have hstable : (prefixWord ++ tailWord_2714351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2714351).length < 2 ^ (prefixWord ++ tailWord_2714351).sum := by decide
  have hdescent : baseEnd_2714351 < baseStart_2714351 := by decide
  rcases family_descends (prefixWord ++ tailWord_2714351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2714354 : List Nat := [3, 2, 1, 3, 1, 3, 1, 9]
def baseStart_2714354 : Nat := 118140960795 + 2714354 * 2 ^ 59
def prefixEnd_2714354 : Nat := 4983230072969 + 3 ^ 40 * 2714354 * 2
def baseEnd_2714354 : Nat := 51621046979784381895997

theorem tailTrace_2714354 : CollatzResearch.WordTrace tailWord_2714354 prefixEnd_2714354 51621046979784381895997 := by
  unfold tailWord_2714354
  simp only [CollatzResearch.WordTrace]
  refine ⟨24750155902091626900309529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66000415738911005067492077 24750155902091626900309529)
  ·
    refine ⟨18562616926568720175232147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24750155902091626900309529 18562616926568720175232147)
    ·
      refine ⟨27843925389853080262848221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18562616926568720175232147 27843925389853080262848221)
      ·
        refine ⟨10441472021194905098568083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27843925389853080262848221 10441472021194905098568083)
        ·
          refine ⟨15662208031792357647852125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10441472021194905098568083 15662208031792357647852125)
          ·
            refine ⟨5873328011922134117944547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15662208031792357647852125 5873328011922134117944547)
            ·
              refine ⟨8809992017883201176916821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5873328011922134117944547 8809992017883201176916821)
              ·
                refine ⟨51621046979784381895997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8809992017883201176916821 51621046979784381895997)
                ·
                  rfl

theorem cell23_2714354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 9].length) (baseStart_2714354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2714354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2714354 prefixEnd_2714354 := by exact prefixLift 2714354
  have htrace : WordTrace (prefixWord ++ tailWord_2714354) baseStart_2714354 baseEnd_2714354 := by
    simpa [prefixWord, tailWord_2714354, baseEnd_2714354] using wordTrace_append hprefix tailTrace_2714354
  have hstable : (prefixWord ++ tailWord_2714354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2714354).length < 2 ^ (prefixWord ++ tailWord_2714354).sum := by decide
  have hdescent : baseEnd_2714354 < baseStart_2714354 := by decide
  rcases family_descends (prefixWord ++ tailWord_2714354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2714367 : List Nat := [1, 1, 2, 2, 1, 3, 1, 2, 1, 9]
def baseStart_2714367 : Nat := 118140960795 + 2714367 * 2 ^ 59
def prefixEnd_2714367 : Nat := 4983230072969 + 3 ^ 40 * 2714367 * 2
def baseEnd_2714367 : Nat := 464591647900895586776453

theorem tailTrace_2714367 : CollatzResearch.WordTrace tailWord_2714367 prefixEnd_2714367 464591647900895586776453 := by
  unfold tailWord_2714367
  simp only [CollatzResearch.WordTrace]
  refine ⟨99001097757319410821461355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66000731838212940547640903 99001097757319410821461355)
  ·
    refine ⟨148501646635979116232192033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99001097757319410821461355 148501646635979116232192033)
    ·
      refine ⟨111376234976984337174144025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148501646635979116232192033 111376234976984337174144025)
      ·
        refine ⟨83532176232738252880608019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111376234976984337174144025 83532176232738252880608019)
        ·
          refine ⟨125298264349107379320912029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83532176232738252880608019 125298264349107379320912029)
          ·
            refine ⟨46986849130915267245342011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 125298264349107379320912029 46986849130915267245342011)
            ·
              refine ⟨70480273696372900868013017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46986849130915267245342011 70480273696372900868013017)
              ·
                refine ⟨52860205272279675651009763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70480273696372900868013017 52860205272279675651009763)
                ·
                  refine ⟨79290307908419513476514645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52860205272279675651009763 79290307908419513476514645)
                  ·
                    refine ⟨464591647900895586776453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 79290307908419513476514645 464591647900895586776453)
                    ·
                      rfl

theorem cell23_2714367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 2, 1, 9].length) (baseStart_2714367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2714367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2714367 prefixEnd_2714367 := by exact prefixLift 2714367
  have htrace : WordTrace (prefixWord ++ tailWord_2714367) baseStart_2714367 baseEnd_2714367 := by
    simpa [prefixWord, tailWord_2714367, baseEnd_2714367] using wordTrace_append hprefix tailTrace_2714367
  have hstable : (prefixWord ++ tailWord_2714367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2714367).length < 2 ^ (prefixWord ++ tailWord_2714367).sum := by decide
  have hdescent : baseEnd_2714367 < baseStart_2714367 := by decide
  rcases family_descends (prefixWord ++ tailWord_2714367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2714408 : List Nat := [2, 1, 5, 1, 1, 1, 3, 1, 3, 3, 2]
def baseStart_2714408 : Nat := 118140960795 + 2714408 * 2 ^ 59
def prefixEnd_2714408 : Nat := 4983230072969 + 3 ^ 40 * 2714408 * 2
def baseEnd_2714408 : Nat := 1393795996409521099916671

theorem tailTrace_2714408 : CollatzResearch.WordTrace tailWord_2714408 prefixEnd_2714408 1393795996409521099916671 := by
  unfold tailWord_2714408
  simp only [CollatzResearch.WordTrace]
  refine ⟨49501296575085437411851939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66001728766780583215802585 49501296575085437411851939)
  ·
    refine ⟨74251944862628156117777909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49501296575085437411851939 74251944862628156117777909)
    ·
      refine ⟨6961119830871389636041679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 74251944862628156117777909 6961119830871389636041679)
      ·
        refine ⟨10441679746307084454062519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6961119830871389636041679 10441679746307084454062519)
        ·
          refine ⟨15662519619460626681093779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10441679746307084454062519 15662519619460626681093779)
          ·
            refine ⟨23493779429190940021640669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15662519619460626681093779 23493779429190940021640669)
            ·
              refine ⟨8810167285946602508115251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23493779429190940021640669 8810167285946602508115251)
              ·
                refine ⟨13215250928919903762172877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8810167285946602508115251 13215250928919903762172877)
                ·
                  refine ⟨4955719098344963910814829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13215250928919903762172877 4955719098344963910814829)
                  ·
                    refine ⟨1858394661879361466555561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4955719098344963910814829 1858394661879361466555561)
                    ·
                      refine ⟨1393795996409521099916671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1858394661879361466555561 1393795996409521099916671)
                      ·
                        rfl

theorem cell23_2714408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 1, 3, 3, 2].length) (baseStart_2714408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2714408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2714408 prefixEnd_2714408 := by exact prefixLift 2714408
  have htrace : WordTrace (prefixWord ++ tailWord_2714408) baseStart_2714408 baseEnd_2714408 := by
    simpa [prefixWord, tailWord_2714408, baseEnd_2714408] using wordTrace_append hprefix tailTrace_2714408
  have hstable : (prefixWord ++ tailWord_2714408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2714408).length < 2 ^ (prefixWord ++ tailWord_2714408).sum := by decide
  have hdescent : baseEnd_2714408 < baseStart_2714408 := by decide
  rcases family_descends (prefixWord ++ tailWord_2714408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2714424 : List Nat := [2, 1, 2, 1, 3, 2, 1, 3, 2, 1, 5]
def baseStart_2714424 : Nat := 118140960795 + 2714424 * 2 ^ 59
def prefixEnd_2714424 : Nat := 4983230072969 + 3 ^ 40 * 2714424 * 2
def baseEnd_2714424 : Nat := 1393804212099993037316597

theorem tailTrace_2714424 : CollatzResearch.WordTrace tailWord_2714424 prefixEnd_2714424 1393804212099993037316597 := by
  unfold tailWord_2714424
  simp only [CollatzResearch.WordTrace]
  refine ⟨49501588359056454778143163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66002117812075273037524217 49501588359056454778143163)
  ·
    refine ⟨74252382538584682167214745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49501588359056454778143163 74252382538584682167214745)
    ·
      refine ⟨55689286903938511625411059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74252382538584682167214745 55689286903938511625411059)
      ·
        refine ⟨83533930355907767438116589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55689286903938511625411059 83533930355907767438116589)
        ·
          refine ⟨31325223883465412789293721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83533930355907767438116589 31325223883465412789293721)
          ·
            refine ⟨23493917912599059591970291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31325223883465412789293721 23493917912599059591970291)
            ·
              refine ⟨35240876868898589387955437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23493917912599059591970291 35240876868898589387955437)
              ·
                refine ⟨13215328825836971020483289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35240876868898589387955437 13215328825836971020483289)
                ·
                  refine ⟨9911496619377728265362467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13215328825836971020483289 9911496619377728265362467)
                  ·
                    refine ⟨14867244929066592398043701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9911496619377728265362467 14867244929066592398043701)
                    ·
                      refine ⟨1393804212099993037316597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14867244929066592398043701 1393804212099993037316597)
                      ·
                        rfl

theorem cell23_2714424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 3, 2, 1, 5].length) (baseStart_2714424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2714424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2714424 prefixEnd_2714424 := by exact prefixLift 2714424
  have htrace : WordTrace (prefixWord ++ tailWord_2714424) baseStart_2714424 baseEnd_2714424 := by
    simpa [prefixWord, tailWord_2714424, baseEnd_2714424] using wordTrace_append hprefix tailTrace_2714424
  have hstable : (prefixWord ++ tailWord_2714424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2714424).length < 2 ^ (prefixWord ++ tailWord_2714424).sum := by decide
  have hdescent : baseEnd_2714424 < baseStart_2714424 := by decide
  rcases family_descends (prefixWord ++ tailWord_2714424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2714433 : List Nat := [1, 2, 5, 3, 2, 1, 2, 2, 1, 2, 2]
def baseStart_2714433 : Nat := 118140960795 + 2714433 * 2 ^ 59
def prefixEnd_2714433 : Nat := 4983230072969 + 3 ^ 40 * 2714433 * 2
def baseEnd_2714433 : Nat := 1393808833425883502104057

theorem tailTrace_2714433 : CollatzResearch.WordTrace tailWord_2714433 prefixEnd_2714433 1393808833425883502104057 := by
  unfold tailWord_2714433
  simp only [CollatzResearch.WordTrace]
  refine ⟨99003504975080304093363953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66002336650053536062242635 99003504975080304093363953)
  ·
    refine ⟨74252628731310228070022965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99003504975080304093363953 74252628731310228070022965)
    ·
      refine ⟨6961183943560333881564653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 74252628731310228070022965 6961183943560333881564653)
      ·
        refine ⟨2610443978835125205586745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6961183943560333881564653 2610443978835125205586745)
        ·
          refine ⟨1957832984126343904190059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2610443978835125205586745 1957832984126343904190059)
          ·
            refine ⟨2936749476189515856285089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1957832984126343904190059 2936749476189515856285089)
            ·
              refine ⟨2202562107142136892213817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2936749476189515856285089 2202562107142136892213817)
              ·
                refine ⟨1651921580356602669160363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2202562107142136892213817 1651921580356602669160363)
                ·
                  refine ⟨2477882370534904003740545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1651921580356602669160363 2477882370534904003740545)
                  ·
                    refine ⟨1858411777901178002805409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2477882370534904003740545 1858411777901178002805409)
                    ·
                      refine ⟨1393808833425883502104057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1858411777901178002805409 1393808833425883502104057)
                      ·
                        rfl

theorem cell23_2714433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 2, 2, 1, 2, 2].length) (baseStart_2714433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2714433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2714433 prefixEnd_2714433 := by exact prefixLift 2714433
  have htrace : WordTrace (prefixWord ++ tailWord_2714433) baseStart_2714433 baseEnd_2714433 := by
    simpa [prefixWord, tailWord_2714433, baseEnd_2714433] using wordTrace_append hprefix tailTrace_2714433
  have hstable : (prefixWord ++ tailWord_2714433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2714433).length < 2 ^ (prefixWord ++ tailWord_2714433).sum := by decide
  have hdescent : baseEnd_2714433 < baseStart_2714433 := by decide
  rcases family_descends (prefixWord ++ tailWord_2714433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2714455 : List Nat := [1, 1, 3, 2, 4, 1, 2, 3, 2, 2, 2]
def baseStart_2714455 : Nat := 118140960795 + 2714455 * 2 ^ 59
def prefixEnd_2714455 : Nat := 4983230072969 + 3 ^ 40 * 2714455 * 2
def baseEnd_2714455 : Nat := 1393820130000282416028955

theorem tailTrace_2714455 : CollatzResearch.WordTrace tailWord_2714455 prefixEnd_2714455 1393820130000282416028955 := by
  unfold tailWord_2714455
  simp only [CollatzResearch.WordTrace]
  refine ⟨99004307381000601850664819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66002871587333734567109879 99004307381000601850664819)
  ·
    refine ⟨148506461071500902775997229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99004307381000601850664819 148506461071500902775997229)
    ·
      refine ⟨55689922901812838540998961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 148506461071500902775997229 55689922901812838540998961)
      ·
        refine ⟨41767442176359628905749221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55689922901812838540998961 41767442176359628905749221)
        ·
          refine ⟨7831395408067430419827979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41767442176359628905749221 7831395408067430419827979)
          ·
            refine ⟨11747093112101145629741969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7831395408067430419827979 11747093112101145629741969)
            ·
              refine ⟨8810319834075859222306477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11747093112101145629741969 8810319834075859222306477)
              ·
                refine ⟨3303869937778447208364929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8810319834075859222306477 3303869937778447208364929)
                ·
                  refine ⟨2477902453333835406273697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3303869937778447208364929 2477902453333835406273697)
                  ·
                    refine ⟨1858426840000376554705273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2477902453333835406273697 1858426840000376554705273)
                    ·
                      refine ⟨1393820130000282416028955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1858426840000376554705273 1393820130000282416028955)
                      ·
                        rfl

theorem cell23_2714455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 3, 2, 2, 2].length) (baseStart_2714455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2714455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2714455 prefixEnd_2714455 := by exact prefixLift 2714455
  have htrace : WordTrace (prefixWord ++ tailWord_2714455) baseStart_2714455 baseEnd_2714455 := by
    simpa [prefixWord, tailWord_2714455, baseEnd_2714455] using wordTrace_append hprefix tailTrace_2714455
  have hstable : (prefixWord ++ tailWord_2714455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2714455).length < 2 ^ (prefixWord ++ tailWord_2714455).sum := by decide
  have hdescent : baseEnd_2714455 < baseStart_2714455 := by decide
  rcases family_descends (prefixWord ++ tailWord_2714455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2714531 : List Nat := [1, 1, 1, 4, 1, 2, 4, 1, 1, 4, 3]
def baseStart_2714531 : Nat := 118140960795 + 2714531 * 2 ^ 59
def prefixEnd_2714531 : Nat := 4983230072969 + 3 ^ 40 * 2714531 * 2
def baseEnd_2714531 : Nat := 1393859154530024118678605

theorem tailTrace_2714531 : CollatzResearch.WordTrace tailWord_2714531 prefixEnd_2714531 1393859154530024118678605 := by
  unfold tailWord_2714531
  simp only [CollatzResearch.WordTrace]
  refine ⟨99007079328725266830431447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66004719552483511220287631 99007079328725266830431447)
  ·
    refine ⟨148510618993087900245647171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99007079328725266830431447 148510618993087900245647171)
    ·
      refine ⟨222765928489631850368470757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148510618993087900245647171 222765928489631850368470757)
      ·
        refine ⟨41768611591805971944088267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 222765928489631850368470757 41768611591805971944088267)
        ·
          refine ⟨62652917387708957916132401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41768611591805971944088267 62652917387708957916132401)
          ·
            refine ⟨46989688040781718437099301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62652917387708957916132401 46989688040781718437099301)
            ·
              refine ⟨8810566507646572206956119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46989688040781718437099301 8810566507646572206956119)
              ·
                refine ⟨13215849761469858310434179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8810566507646572206956119 13215849761469858310434179)
                ·
                  refine ⟨19823774642204787465651269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13215849761469858310434179 19823774642204787465651269)
                  ·
                    refine ⟨3716957745413397649809613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19823774642204787465651269 3716957745413397649809613)
                    ·
                      refine ⟨1393859154530024118678605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3716957745413397649809613 1393859154530024118678605)
                      ·
                        rfl

theorem cell23_2714531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 1, 1, 4, 3].length) (baseStart_2714531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2714531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2714531 prefixEnd_2714531 := by exact prefixLift 2714531
  have htrace : WordTrace (prefixWord ++ tailWord_2714531) baseStart_2714531 baseEnd_2714531 := by
    simpa [prefixWord, tailWord_2714531, baseEnd_2714531] using wordTrace_append hprefix tailTrace_2714531
  have hstable : (prefixWord ++ tailWord_2714531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2714531).length < 2 ^ (prefixWord ++ tailWord_2714531).sum := by decide
  have hdescent : baseEnd_2714531 < baseStart_2714531 := by decide
  rcases family_descends (prefixWord ++ tailWord_2714531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2714568 : List Nat := [2, 1, 3, 1, 5, 1, 1, 3, 6]
def baseStart_2714568 : Nat := 118140960795 + 2714568 * 2 ^ 59
def prefixEnd_2714568 : Nat := 4983230072969 + 3 ^ 40 * 2714568 * 2
def baseEnd_2714568 : Nat := 154875350368248941546215

theorem tailTrace_2714568 : CollatzResearch.WordTrace tailWord_2714568 prefixEnd_2714568 154875350368248941546215 := by
  unfold tailWord_2714568
  simp only [CollatzResearch.WordTrace]
  refine ⟨49504214414795611074764179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66005619219727481433018905 49504214414795611074764179)
  ·
    refine ⟨74256321622193416612146269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49504214414795611074764179 74256321622193416612146269)
    ·
      refine ⟨27846120608322531229554851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74256321622193416612146269 27846120608322531229554851)
      ·
        refine ⟨41769180912483796844332277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27846120608322531229554851 41769180912483796844332277)
        ·
          refine ⟨3915860710545355954156151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 41769180912483796844332277 3915860710545355954156151)
          ·
            refine ⟨5873791065818033931234227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3915860710545355954156151 5873791065818033931234227)
            ·
              refine ⟨8810686598727050896851341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5873791065818033931234227 8810686598727050896851341)
              ·
                refine ⟨3304007474522644086319253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8810686598727050896851341 3304007474522644086319253)
                ·
                  refine ⟨154875350368248941546215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3304007474522644086319253 154875350368248941546215)
                  ·
                    rfl

theorem cell23_2714568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 3, 6].length) (baseStart_2714568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2714568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2714568 prefixEnd_2714568 := by exact prefixLift 2714568
  have htrace : WordTrace (prefixWord ++ tailWord_2714568) baseStart_2714568 baseEnd_2714568 := by
    simpa [prefixWord, tailWord_2714568, baseEnd_2714568] using wordTrace_append hprefix tailTrace_2714568
  have hstable : (prefixWord ++ tailWord_2714568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2714568).length < 2 ^ (prefixWord ++ tailWord_2714568).sum := by decide
  have hdescent : baseEnd_2714568 < baseStart_2714568 := by decide
  rcases family_descends (prefixWord ++ tailWord_2714568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2714582 : List Nat := [5, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3]
def baseStart_2714582 : Nat := 118140960795 + 2714582 * 2 ^ 59
def prefixEnd_2714582 : Nat := 4983230072969 + 3 ^ 40 * 2714582 * 2
def baseEnd_2714582 : Nat := 1393885342043403419140871

theorem tailTrace_2714582 : CollatzResearch.WordTrace tailWord_2714582 prefixEnd_2714582 1393885342043403419140871 := by
  unfold tailWord_2714582
  simp only [CollatzResearch.WordTrace]
  refine ⟨6188058715721281408783625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 66005959634360335027025333 6188058715721281408783625)
  ·
    refine ⟨4641044036790961056587719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6188058715721281408783625 4641044036790961056587719)
    ·
      refine ⟨6961566055186441584881579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4641044036790961056587719 6961566055186441584881579)
      ·
        refine ⟨10442349082779662377322369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6961566055186441584881579 10442349082779662377322369)
        ·
          refine ⟨7831761812084746782991777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10442349082779662377322369 7831761812084746782991777)
          ·
            refine ⟨5873821359063560087243833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7831761812084746782991777 5873821359063560087243833)
            ·
              refine ⟨4405366019297670065432875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5873821359063560087243833 4405366019297670065432875)
              ·
                refine ⟨6608049028946505098149313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4405366019297670065432875 6608049028946505098149313)
                ·
                  refine ⟨4956036771709878823611985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6608049028946505098149313 4956036771709878823611985)
                  ·
                    refine ⟨3717027578782409117708989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4956036771709878823611985 3717027578782409117708989)
                    ·
                      refine ⟨1393885342043403419140871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3717027578782409117708989 1393885342043403419140871)
                      ·
                        rfl

theorem cell23_2714582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3].length) (baseStart_2714582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2714582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2714582 prefixEnd_2714582 := by exact prefixLift 2714582
  have htrace : WordTrace (prefixWord ++ tailWord_2714582) baseStart_2714582 baseEnd_2714582 := by
    simpa [prefixWord, tailWord_2714582, baseEnd_2714582] using wordTrace_append hprefix tailTrace_2714582
  have hstable : (prefixWord ++ tailWord_2714582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2714582).length < 2 ^ (prefixWord ++ tailWord_2714582).sum := by decide
  have hdescent : baseEnd_2714582 < baseStart_2714582 := by decide
  rcases family_descends (prefixWord ++ tailWord_2714582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2714606 : List Nat := [4, 1, 2, 1, 5, 1, 2, 2, 1, 4]
def baseStart_2714606 : Nat := 118140960795 + 2714606 * 2 ^ 59
def prefixEnd_2714606 : Nat := 4983230072969 + 3 ^ 40 * 2714606 * 2
def baseEnd_2714606 : Nat := 464632555193037108413587

theorem tailTrace_2714606 : CollatzResearch.WordTrace tailWord_2714606 prefixEnd_2714606 464632555193037108413587 := by
  unfold tailWord_2714606
  simp only [CollatzResearch.WordTrace]
  refine ⟨12376226850431694329926459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66006543202302369759607781 12376226850431694329926459)
  ·
    refine ⟨18564340275647541494889689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12376226850431694329926459 18564340275647541494889689)
    ·
      refine ⟨13923255206735656121167267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18564340275647541494889689 13923255206735656121167267)
      ·
        refine ⟨20884882810103484181750901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13923255206735656121167267 20884882810103484181750901)
        ·
          refine ⟨1957957763447201642039147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 20884882810103484181750901 1957957763447201642039147)
          ·
            refine ⟨2936936645170802463058721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1957957763447201642039147 2936936645170802463058721)
            ·
              refine ⟨2202702483878101847294041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2936936645170802463058721 2202702483878101847294041)
              ·
                refine ⟨1652026862908576385470531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2202702483878101847294041 1652026862908576385470531)
                ·
                  refine ⟨2478040294362864578205797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1652026862908576385470531 2478040294362864578205797)
                  ·
                    refine ⟨464632555193037108413587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2478040294362864578205797 464632555193037108413587)
                    ·
                      rfl

theorem cell23_2714606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 2, 2, 1, 4].length) (baseStart_2714606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2714606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2714606 prefixEnd_2714606 := by exact prefixLift 2714606
  have htrace : WordTrace (prefixWord ++ tailWord_2714606) baseStart_2714606 baseEnd_2714606 := by
    simpa [prefixWord, tailWord_2714606, baseEnd_2714606] using wordTrace_append hprefix tailTrace_2714606
  have hstable : (prefixWord ++ tailWord_2714606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2714606).length < 2 ^ (prefixWord ++ tailWord_2714606).sum := by decide
  have hdescent : baseEnd_2714606 < baseStart_2714606 := by decide
  rcases family_descends (prefixWord ++ tailWord_2714606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2714621 : List Nat := [1, 4, 1, 1, 1, 2, 1, 3, 3, 1, 5]
def baseStart_2714621 : Nat := 118140960795 + 2714621 * 2 ^ 59
def prefixEnd_2714621 : Nat := 4983230072969 + 3 ^ 40 * 2714621 * 2
def baseEnd_2714621 : Nat := 1393905367788928766553191

theorem tailTrace_2714621 : CollatzResearch.WordTrace tailWord_2714621 prefixEnd_2714621 1393905367788928766553191 := by
  unfold tailWord_2714621
  simp only [CollatzResearch.WordTrace]
  refine ⟨99010361898399212201207717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66006907932266141467471811 99010361898399212201207717)
  ·
    refine ⟨18564442855949852287726447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 99010361898399212201207717 18564442855949852287726447)
    ·
      refine ⟨27846664283924778431589671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18564442855949852287726447 27846664283924778431589671)
      ·
        refine ⟨41769996425887167647384507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27846664283924778431589671 41769996425887167647384507)
        ·
          refine ⟨62654994638830751471076761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41769996425887167647384507 62654994638830751471076761)
          ·
            refine ⟨46991245979123063603307571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62654994638830751471076761 46991245979123063603307571)
            ·
              refine ⟨70486868968684595404961357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46991245979123063603307571 70486868968684595404961357)
              ·
                refine ⟨26432575863256723276860509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 70486868968684595404961357 26432575863256723276860509)
                ·
                  refine ⟨9912215948721271228822691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26432575863256723276860509 9912215948721271228822691)
                  ·
                    refine ⟨14868323923081906843234037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9912215948721271228822691 14868323923081906843234037)
                    ·
                      refine ⟨1393905367788928766553191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14868323923081906843234037 1393905367788928766553191)
                      ·
                        rfl

theorem cell23_2714621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 3, 3, 1, 5].length) (baseStart_2714621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2714621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2714621 prefixEnd_2714621 := by exact prefixLift 2714621
  have htrace : WordTrace (prefixWord ++ tailWord_2714621) baseStart_2714621 baseEnd_2714621 := by
    simpa [prefixWord, tailWord_2714621, baseEnd_2714621] using wordTrace_append hprefix tailTrace_2714621
  have hstable : (prefixWord ++ tailWord_2714621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2714621).length < 2 ^ (prefixWord ++ tailWord_2714621).sum := by decide
  have hdescent : baseEnd_2714621 < baseStart_2714621 := by decide
  rcases family_descends (prefixWord ++ tailWord_2714621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2714635 : List Nat := [1, 1, 1, 1, 6, 2, 1, 1, 5, 2, 2]
def baseStart_2714635 : Nat := 118140960795 + 2714635 * 2 ^ 59
def prefixEnd_2714635 : Nat := 4983230072969 + 3 ^ 40 * 2714635 * 2
def baseEnd_2714635 : Nat := 1393912556518091711778127

theorem tailTrace_2714635 : CollatzResearch.WordTrace tailWord_2714635 prefixEnd_2714635 1393912556518091711778127 := by
  unfold tailWord_2714635
  simp only [CollatzResearch.WordTrace]
  refine ⟨99010872520348492592217359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66007248346898995061478239 99010872520348492592217359)
  ·
    refine ⟨148516308780522738888326039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99010872520348492592217359 148516308780522738888326039)
    ·
      refine ⟨222774463170784108332489059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148516308780522738888326039 222774463170784108332489059)
      ·
        refine ⟨334161694756176162498733589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222774463170784108332489059 334161694756176162498733589)
        ·
          refine ⟨15663829441695757617128137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 334161694756176162498733589 15663829441695757617128137)
          ·
            refine ⟨11747872081271818212846103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15663829441695757617128137 11747872081271818212846103)
            ·
              refine ⟨17621808121907727319269155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11747872081271818212846103 17621808121907727319269155)
              ·
                refine ⟨26432712182861590978903733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17621808121907727319269155 26432712182861590978903733)
                ·
                  refine ⟨2478066767143274154272225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26432712182861590978903733 2478066767143274154272225)
                  ·
                    refine ⟨1858550075357455615704169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2478066767143274154272225 1858550075357455615704169)
                    ·
                      refine ⟨1393912556518091711778127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1858550075357455615704169 1393912556518091711778127)
                      ·
                        rfl

theorem cell23_2714635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 1, 5, 2, 2].length) (baseStart_2714635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2714635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2714635 prefixEnd_2714635 := by exact prefixLift 2714635
  have htrace : WordTrace (prefixWord ++ tailWord_2714635) baseStart_2714635 baseEnd_2714635 := by
    simpa [prefixWord, tailWord_2714635, baseEnd_2714635] using wordTrace_append hprefix tailTrace_2714635
  have hstable : (prefixWord ++ tailWord_2714635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2714635).length < 2 ^ (prefixWord ++ tailWord_2714635).sum := by decide
  have hdescent : baseEnd_2714635 < baseStart_2714635 := by decide
  rcases family_descends (prefixWord ++ tailWord_2714635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2714648 : List Nat := [2, 1, 2, 3, 2, 2, 2, 2, 1, 2, 4]
def baseStart_2714648 : Nat := 118140960795 + 2714648 * 2 ^ 59
def prefixEnd_2714648 : Nat := 4983230072969 + 3 ^ 40 * 2714648 * 2
def baseEnd_2714648 : Nat := 1393919231766600160915567

theorem tailTrace_2714648 : CollatzResearch.WordTrace tailWord_2714648 prefixEnd_2714648 1393919231766600160915567 := by
  unfold tailWord_2714648
  simp only [CollatzResearch.WordTrace]
  refine ⟨49505673334650697906220299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66007564446200930541627065 49505673334650697906220299)
  ·
    refine ⟨74258510001976046859330449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49505673334650697906220299 74258510001976046859330449)
    ·
      refine ⟨55693882501482035144497837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74258510001976046859330449 55693882501482035144497837)
      ·
        refine ⟨20885205938055763179186689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55693882501482035144497837 20885205938055763179186689)
        ·
          refine ⟨15663904453541822384390017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20885205938055763179186689 15663904453541822384390017)
          ·
            refine ⟨11747928340156366788292513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15663904453541822384390017 11747928340156366788292513)
            ·
              refine ⟨8810946255117275091219385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11747928340156366788292513 8810946255117275091219385)
              ·
                refine ⟨6608209691337956318414539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8810946255117275091219385 6608209691337956318414539)
                ·
                  refine ⟨9912314537006934477621809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6608209691337956318414539 9912314537006934477621809)
                  ·
                    refine ⟨7434235902755200858216357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9912314537006934477621809 7434235902755200858216357)
                    ·
                      refine ⟨1393919231766600160915567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7434235902755200858216357 1393919231766600160915567)
                      ·
                        rfl

theorem cell23_2714648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 2, 1, 2, 4].length) (baseStart_2714648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2714648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2714648 prefixEnd_2714648 := by exact prefixLift 2714648
  have htrace : WordTrace (prefixWord ++ tailWord_2714648) baseStart_2714648 baseEnd_2714648 := by
    simpa [prefixWord, tailWord_2714648, baseEnd_2714648] using wordTrace_append hprefix tailTrace_2714648
  have hstable : (prefixWord ++ tailWord_2714648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2714648).length < 2 ^ (prefixWord ++ tailWord_2714648).sum := by decide
  have hdescent : baseEnd_2714648 < baseStart_2714648 := by decide
  rcases family_descends (prefixWord ++ tailWord_2714648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2714651 : List Nat := [1, 1, 1, 1, 1, 1, 3, 2, 2, 7, 3]
def baseStart_2714651 : Nat := 118140960795 + 2714651 * 2 ^ 59
def prefixEnd_2714651 : Nat := 4983230072969 + 3 ^ 40 * 2714651 * 2
def baseEnd_2714651 : Nat := 1393920772208563649178053

theorem tailTrace_2714651 : CollatzResearch.WordTrace tailWord_2714651 prefixEnd_2714651 1393920772208563649178053 := by
  unfold tailWord_2714651
  simp only [CollatzResearch.WordTrace]
  refine ⟨99011456088290527324799807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66007637392193684883199871 99011456088290527324799807)
  ·
    refine ⟨148517184132435790987199711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99011456088290527324799807 148517184132435790987199711)
    ·
      refine ⟨222775776198653686480799567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148517184132435790987199711 222775776198653686480799567)
      ·
        refine ⟨334163664297980529721199351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222775776198653686480799567 334163664297980529721199351)
        ·
          refine ⟨501245496446970794581799027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 334163664297980529721199351 501245496446970794581799027)
          ·
            refine ⟨751868244670456191872698541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 501245496446970794581799027 751868244670456191872698541)
            ·
              refine ⟨281950591751421071952261953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 751868244670456191872698541 281950591751421071952261953)
              ·
                refine ⟨211462943813565803964196465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 281950591751421071952261953 211462943813565803964196465)
                ·
                  refine ⟨158597207860174352973147349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 211462943813565803964196465 158597207860174352973147349)
                  ·
                    refine ⟨3717122059222836397808141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 158597207860174352973147349 3717122059222836397808141)
                    ·
                      refine ⟨1393920772208563649178053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3717122059222836397808141 1393920772208563649178053)
                      ·
                        rfl

theorem cell23_2714651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 2, 7, 3].length) (baseStart_2714651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2714651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2714651 prefixEnd_2714651 := by exact prefixLift 2714651
  have htrace : WordTrace (prefixWord ++ tailWord_2714651) baseStart_2714651 baseEnd_2714651 := by
    simpa [prefixWord, tailWord_2714651, baseEnd_2714651] using wordTrace_append hprefix tailTrace_2714651
  have hstable : (prefixWord ++ tailWord_2714651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2714651).length < 2 ^ (prefixWord ++ tailWord_2714651).sum := by decide
  have hdescent : baseEnd_2714651 < baseStart_2714651 := by decide
  rcases family_descends (prefixWord ++ tailWord_2714651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2714655 : List Nat := [1, 1, 2, 4, 1, 4, 1, 3, 1, 2, 3]
def baseStart_2714655 : Nat := 118140960795 + 2714655 * 2 ^ 59
def prefixEnd_2714655 : Nat := 4983230072969 + 3 ^ 40 * 2714655 * 2
def baseEnd_2714655 : Nat := 1393922826131181633528035

theorem tailTrace_2714655 : CollatzResearch.WordTrace tailWord_2714655 prefixEnd_2714655 1393922826131181633528035 := by
  unfold tailWord_2714655
  simp only [CollatzResearch.WordTrace]
  refine ⟨99011601980276036007945419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66007734653517357338630279 99011601980276036007945419)
  ·
    refine ⟨148517402970414054011918129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99011601980276036007945419 148517402970414054011918129)
    ·
      refine ⟨111388052227810540508938597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148517402970414054011918129 111388052227810540508938597)
      ·
        refine ⟨20885259792714476345425987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 111388052227810540508938597 20885259792714476345425987)
        ·
          refine ⟨31327889689071714518138981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20885259792714476345425987 31327889689071714518138981)
          ·
            refine ⟨5873979316700946472151059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31327889689071714518138981 5873979316700946472151059)
            ·
              refine ⟨8810968975051419708226589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5873979316700946472151059 8810968975051419708226589)
              ·
                refine ⟨3304113365644282390584971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8810968975051419708226589 3304113365644282390584971)
                ·
                  refine ⟨4956170048466423585877457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3304113365644282390584971 4956170048466423585877457)
                  ·
                    refine ⟨3717127536349817689408093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4956170048466423585877457 3717127536349817689408093)
                    ·
                      refine ⟨1393922826131181633528035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3717127536349817689408093 1393922826131181633528035)
                      ·
                        rfl

theorem cell23_2714655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 3, 1, 2, 3].length) (baseStart_2714655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2714655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2714655 prefixEnd_2714655 := by exact prefixLift 2714655
  have htrace : WordTrace (prefixWord ++ tailWord_2714655) baseStart_2714655 baseEnd_2714655 := by
    simpa [prefixWord, tailWord_2714655, baseEnd_2714655] using wordTrace_append hprefix tailTrace_2714655
  have hstable : (prefixWord ++ tailWord_2714655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2714655).length < 2 ^ (prefixWord ++ tailWord_2714655).sum := by decide
  have hdescent : baseEnd_2714655 < baseStart_2714655 := by decide
  rcases family_descends (prefixWord ++ tailWord_2714655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2714685 : List Nat := [1, 4, 1, 3, 1, 2, 3, 1, 1, 3, 3]
def baseStart_2714685 : Nat := 118140960795 + 2714685 * 2 ^ 59
def prefixEnd_2714685 : Nat := 4983230072969 + 3 ^ 40 * 2714685 * 2
def baseEnd_2714685 : Nat := 1393938230550816516152897

theorem tailTrace_2714685 : CollatzResearch.WordTrace tailWord_2714685 prefixEnd_2714685 1393938230550816516152897 := by
  unfold tailWord_2714685
  simp only [CollatzResearch.WordTrace]
  refine ⟨99012696170167351131537509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66008464113444900754358339 99012696170167351131537509)
  ·
    refine ⟨18564880531906378337163283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 99012696170167351131537509 18564880531906378337163283)
    ·
      refine ⟨27847320797859567505744925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18564880531906378337163283 27847320797859567505744925)
      ·
        refine ⟨10442745299197337814654347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27847320797859567505744925 10442745299197337814654347)
        ·
          refine ⟨15664117948796006721981521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10442745299197337814654347 15664117948796006721981521)
          ·
            refine ⟨11748088461597005041486141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15664117948796006721981521 11748088461597005041486141)
            ·
              refine ⟨4405533173098876890557303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11748088461597005041486141 4405533173098876890557303)
              ·
                refine ⟨6608299759648315335835955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4405533173098876890557303 6608299759648315335835955)
                ·
                  refine ⟨9912449639472473003753933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6608299759648315335835955 9912449639472473003753933)
                  ·
                    refine ⟨3717168614802177376407725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9912449639472473003753933 3717168614802177376407725)
                    ·
                      refine ⟨1393938230550816516152897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3717168614802177376407725 1393938230550816516152897)
                      ·
                        rfl

theorem cell23_2714685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 3, 1, 1, 3, 3].length) (baseStart_2714685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2714685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2714685 prefixEnd_2714685 := by exact prefixLift 2714685
  have htrace : WordTrace (prefixWord ++ tailWord_2714685) baseStart_2714685 baseEnd_2714685 := by
    simpa [prefixWord, tailWord_2714685, baseEnd_2714685] using wordTrace_append hprefix tailTrace_2714685
  have hstable : (prefixWord ++ tailWord_2714685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2714685).length < 2 ^ (prefixWord ++ tailWord_2714685).sum := by decide
  have hdescent : baseEnd_2714685 < baseStart_2714685 := by decide
  rcases family_descends (prefixWord ++ tailWord_2714685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2714738 : List Nat := [3, 2, 1, 2, 2, 1, 2, 1, 1, 4, 4]
def baseStart_2714738 : Nat := 118140960795 + 2714738 * 2 ^ 59
def prefixEnd_2714738 : Nat := 4983230072969 + 3 ^ 40 * 2714738 * 2
def baseEnd_2714738 : Nat := 1393965445025504808790153

theorem tailTrace_2714738 : CollatzResearch.WordTrace tailWord_2714738 prefixEnd_2714738 1393965445025504808790153 := by
  unfold tailWord_2714738
  simp only [CollatzResearch.WordTrace]
  refine ⟨24753657309743835295804217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66009752825983560788811245 24753657309743835295804217)
  ·
    refine ⟨18565242982307876471853163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24753657309743835295804217 18565242982307876471853163)
    ·
      refine ⟨27847864473461814707779745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18565242982307876471853163 27847864473461814707779745)
      ·
        refine ⟨20885898355096361030834809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27847864473461814707779745 20885898355096361030834809)
        ·
          refine ⟨15664423766322270773126107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20885898355096361030834809 15664423766322270773126107)
          ·
            refine ⟨23496635649483406159689161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15664423766322270773126107 23496635649483406159689161)
            ·
              refine ⟨17622476737112554619766871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23496635649483406159689161 17622476737112554619766871)
              ·
                refine ⟨26433715105668831929650307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17622476737112554619766871 26433715105668831929650307)
                ·
                  refine ⟨39650572658503247894475461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26433715105668831929650307 39650572658503247894475461)
                  ·
                    refine ⟨7434482373469358980214149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39650572658503247894475461 7434482373469358980214149)
                    ·
                      refine ⟨1393965445025504808790153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7434482373469358980214149 1393965445025504808790153)
                      ·
                        rfl

theorem cell23_2714738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 1, 1, 4, 4].length) (baseStart_2714738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2714738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2714738 prefixEnd_2714738 := by exact prefixLift 2714738
  have htrace : WordTrace (prefixWord ++ tailWord_2714738) baseStart_2714738 baseEnd_2714738 := by
    simpa [prefixWord, tailWord_2714738, baseEnd_2714738] using wordTrace_append hprefix tailTrace_2714738
  have hstable : (prefixWord ++ tailWord_2714738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2714738).length < 2 ^ (prefixWord ++ tailWord_2714738).sum := by decide
  have hdescent : baseEnd_2714738 < baseStart_2714738 := by decide
  rcases family_descends (prefixWord ++ tailWord_2714738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2714742 : List Nat := [5, 1, 1, 2, 1, 1, 2, 3, 1, 4, 2]
def baseStart_2714742 : Nat := 118140960795 + 2714742 * 2 ^ 59
def prefixEnd_2714742 : Nat := 4983230072969 + 3 ^ 40 * 2714742 * 2
def baseEnd_2714742 : Nat := 1393967498948122793140135

theorem tailTrace_2714742 : CollatzResearch.WordTrace tailWord_2714742 prefixEnd_2714742 1393967498948122793140135 := by
  unfold tailWord_2714742
  simp only [CollatzResearch.WordTrace]
  refine ⟨6188423445685053116647655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 66009850087307233244241653 6188423445685053116647655)
  ·
    refine ⟨9282635168527579674971483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6188423445685053116647655 9282635168527579674971483)
    ·
      refine ⟨13923952752791369512457225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9282635168527579674971483 13923952752791369512457225)
      ·
        refine ⟨10442964564593527134342919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13923952752791369512457225 10442964564593527134342919)
        ·
          refine ⟨15664446846890290701514379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10442964564593527134342919 15664446846890290701514379)
          ·
            refine ⟨23496670270335436052271569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15664446846890290701514379 23496670270335436052271569)
            ·
              refine ⟨17622502702751577039203677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23496670270335436052271569 17622502702751577039203677)
              ·
                refine ⟨6608438513531841389701379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17622502702751577039203677 6608438513531841389701379)
                ·
                  refine ⟨9912657770297762084552069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6608438513531841389701379 9912657770297762084552069)
                  ·
                    refine ⟨1858623331930830390853513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9912657770297762084552069 1858623331930830390853513)
                    ·
                      refine ⟨1393967498948122793140135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1858623331930830390853513 1393967498948122793140135)
                      ·
                        rfl

theorem cell23_2714742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 3, 1, 4, 2].length) (baseStart_2714742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2714742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2714742 prefixEnd_2714742 := by exact prefixLift 2714742
  have htrace : WordTrace (prefixWord ++ tailWord_2714742) baseStart_2714742 baseEnd_2714742 := by
    simpa [prefixWord, tailWord_2714742, baseEnd_2714742] using wordTrace_append hprefix tailTrace_2714742
  have hstable : (prefixWord ++ tailWord_2714742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2714742).length < 2 ^ (prefixWord ++ tailWord_2714742).sum := by decide
  have hdescent : baseEnd_2714742 < baseStart_2714742 := by decide
  rcases family_descends (prefixWord ++ tailWord_2714742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2714751 : List Nat := [1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 8]
def baseStart_2714751 : Nat := 118140960795 + 2714751 * 2 ^ 59
def prefixEnd_2714751 : Nat := 4983230072969 + 3 ^ 40 * 2714751 * 2
def baseEnd_2714751 : Nat := 1393972120274013257927593

theorem tailTrace_2714751 : CollatzResearch.WordTrace tailWord_2714751 prefixEnd_2714751 1393972120274013257927593 := by
  unfold tailWord_2714751
  simp only [CollatzResearch.WordTrace]
  refine ⟨99015103387928244403440107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66010068925285496268960071 99015103387928244403440107)
  ·
    refine ⟨148522655081892366605160161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99015103387928244403440107 148522655081892366605160161)
    ·
      refine ⟨111391991311419274953870121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148522655081892366605160161 111391991311419274953870121)
      ·
        refine ⟨83543993483564456215402591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111391991311419274953870121 83543993483564456215402591)
        ·
          refine ⟨125315990225346684323103887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83543993483564456215402591 125315990225346684323103887)
          ·
            refine ⟨187973985338020026484655831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125315990225346684323103887 187973985338020026484655831)
            ·
              refine ⟨281960978007030039726983747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 187973985338020026484655831 281960978007030039726983747)
              ·
                refine ⟨422941467010545059590475621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 281960978007030039726983747 422941467010545059590475621)
                ·
                  refine ⟨79301525064477198673214179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 422941467010545059590475621 79301525064477198673214179)
                  ·
                    refine ⟨118952287596715798009821269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 79301525064477198673214179 118952287596715798009821269)
                    ·
                      refine ⟨1393972120274013257927593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 118952287596715798009821269 1393972120274013257927593)
                      ·
                        rfl

theorem cell23_2714751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 8].length) (baseStart_2714751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2714751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2714751 prefixEnd_2714751 := by exact prefixLift 2714751
  have htrace : WordTrace (prefixWord ++ tailWord_2714751) baseStart_2714751 baseEnd_2714751 := by
    simpa [prefixWord, tailWord_2714751, baseEnd_2714751] using wordTrace_append hprefix tailTrace_2714751
  have hstable : (prefixWord ++ tailWord_2714751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2714751).length < 2 ^ (prefixWord ++ tailWord_2714751).sum := by decide
  have hdescent : baseEnd_2714751 < baseStart_2714751 := by decide
  rcases family_descends (prefixWord ++ tailWord_2714751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2714785 : List Nat := [1, 2, 3, 3, 1, 1, 1, 1, 1, 7, 2]
def baseStart_2714785 : Nat := 118140960795 + 2714785 * 2 ^ 59
def prefixEnd_2714785 : Nat := 4983230072969 + 3 ^ 40 * 2714785 * 2
def baseEnd_2714785 : Nat := 1393989578616266124902437

theorem tailTrace_2714785 : CollatzResearch.WordTrace tailWord_2714785 prefixEnd_2714785 1393989578616266124902437 := by
  unfold tailWord_2714785
  simp only [CollatzResearch.WordTrace]
  refine ⟨99016343469805068210177809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66010895646536712140118539 99016343469805068210177809)
  ·
    refine ⟨74262257602353801157633357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99016343469805068210177809 74262257602353801157633357)
    ·
      refine ⟨27848346600882675434112509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74262257602353801157633357 27848346600882675434112509)
      ·
        refine ⟨10443129975331003287792191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27848346600882675434112509 10443129975331003287792191)
        ·
          refine ⟨15664694962996504931688287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10443129975331003287792191 15664694962996504931688287)
          ·
            refine ⟨23497042444494757397532431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15664694962996504931688287 23497042444494757397532431)
            ·
              refine ⟨35245563666742136096298647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23497042444494757397532431 35245563666742136096298647)
              ·
                refine ⟨52868345500113204144447971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35245563666742136096298647 52868345500113204144447971)
                ·
                  refine ⟨79302518250169806216671957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52868345500113204144447971 79302518250169806216671957)
                  ·
                    refine ⟨1858652771488354833203249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 79302518250169806216671957 1858652771488354833203249)
                    ·
                      refine ⟨1393989578616266124902437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1858652771488354833203249 1393989578616266124902437)
                      ·
                        rfl

theorem cell23_2714785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 1, 1, 7, 2].length) (baseStart_2714785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2714785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2714785 prefixEnd_2714785 := by exact prefixLift 2714785
  have htrace : WordTrace (prefixWord ++ tailWord_2714785) baseStart_2714785 baseEnd_2714785 := by
    simpa [prefixWord, tailWord_2714785, baseEnd_2714785] using wordTrace_append hprefix tailTrace_2714785
  have hstable : (prefixWord ++ tailWord_2714785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2714785).length < 2 ^ (prefixWord ++ tailWord_2714785).sum := by decide
  have hdescent : baseEnd_2714785 < baseStart_2714785 := by decide
  rcases family_descends (prefixWord ++ tailWord_2714785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2714812 : List Nat := [2, 2, 2, 3, 2, 3, 1, 1, 2, 5]
def baseStart_2714812 : Nat := 118140960795 + 2714812 * 2 ^ 59
def prefixEnd_2714812 : Nat := 4983230072969 + 3 ^ 40 * 2714812 * 2
def baseEnd_2714812 : Nat := 464667814197979173088271

theorem tailTrace_2714812 : CollatzResearch.WordTrace tailWord_2714812 prefixEnd_2714812 464667814197979173088271 := by
  unfold tailWord_2714812
  simp only [CollatzResearch.WordTrace]
  refine ⟨49508664120353625910705345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66011552160471501214273793 49508664120353625910705345)
  ·
    refine ⟨37131498090265219433029009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49508664120353625910705345 37131498090265219433029009)
    ·
      refine ⟨27848623567698914574771757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37131498090265219433029009 27848623567698914574771757)
      ·
        refine ⟨10443233837887092965539409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27848623567698914574771757 10443233837887092965539409)
        ·
          refine ⟨7832425378415319724154557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10443233837887092965539409 7832425378415319724154557)
          ·
            refine ⟨2937159516905744896557959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7832425378415319724154557 2937159516905744896557959)
            ·
              refine ⟨4405739275358617344836939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2937159516905744896557959 4405739275358617344836939)
              ·
                refine ⟨6608608913037926017255409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4405739275358617344836939 6608608913037926017255409)
                ·
                  refine ⟨4956456684778444512941557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6608608913037926017255409 4956456684778444512941557)
                  ·
                    refine ⟨464667814197979173088271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4956456684778444512941557 464667814197979173088271)
                    ·
                      rfl

theorem cell23_2714812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 1, 1, 2, 5].length) (baseStart_2714812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2714812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2714812 prefixEnd_2714812 := by exact prefixLift 2714812
  have htrace : WordTrace (prefixWord ++ tailWord_2714812) baseStart_2714812 baseEnd_2714812 := by
    simpa [prefixWord, tailWord_2714812, baseEnd_2714812] using wordTrace_append hprefix tailTrace_2714812
  have hstable : (prefixWord ++ tailWord_2714812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2714812).length < 2 ^ (prefixWord ++ tailWord_2714812).sum := by decide
  have hdescent : baseEnd_2714812 < baseStart_2714812 := by decide
  rcases family_descends (prefixWord ++ tailWord_2714812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2714815 : List Nat := [1, 1, 2, 2, 2, 2, 5, 1, 2, 1, 4]
def baseStart_2714815 : Nat := 118140960795 + 2714815 * 2 ^ 59
def prefixEnd_2714815 : Nat := 4983230072969 + 3 ^ 40 * 2714815 * 2
def baseEnd_2714815 : Nat := 1394004983035901007527299

theorem tailTrace_2714815 : CollatzResearch.WordTrace tailWord_2714815 prefixEnd_2714815 1394004983035901007527299 := by
  unfold tailWord_2714815
  simp only [CollatzResearch.WordTrace]
  refine ⟨99017437659696383333769899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66011625106464255555846599 99017437659696383333769899)
  ·
    refine ⟨148526156489544575000654849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99017437659696383333769899 148526156489544575000654849)
    ·
      refine ⟨111394617367158431250491137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148526156489544575000654849 111394617367158431250491137)
      ·
        refine ⟨83545963025368823437868353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111394617367158431250491137 83545963025368823437868353)
        ·
          refine ⟨62659472269026617578401265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83545963025368823437868353 62659472269026617578401265)
          ·
            refine ⟨46994604201769963183800949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62659472269026617578401265 46994604201769963183800949)
            ·
              refine ⟨4405744143915934048481339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 46994604201769963183800949 4405744143915934048481339)
              ·
                refine ⟨6608616215873901072722009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4405744143915934048481339 6608616215873901072722009)
                ·
                  refine ⟨4956462161905425804541507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6608616215873901072722009 4956462161905425804541507)
                  ·
                    refine ⟨7434693242858138706812261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4956462161905425804541507 7434693242858138706812261)
                    ·
                      refine ⟨1394004983035901007527299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7434693242858138706812261 1394004983035901007527299)
                      ·
                        rfl

theorem cell23_2714815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 5, 1, 2, 1, 4].length) (baseStart_2714815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2714815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2714815 prefixEnd_2714815 := by exact prefixLift 2714815
  have htrace : WordTrace (prefixWord ++ tailWord_2714815) baseStart_2714815 baseEnd_2714815 := by
    simpa [prefixWord, tailWord_2714815, baseEnd_2714815] using wordTrace_append hprefix tailTrace_2714815
  have hstable : (prefixWord ++ tailWord_2714815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2714815).length < 2 ^ (prefixWord ++ tailWord_2714815).sum := by decide
  have hdescent : baseEnd_2714815 < baseStart_2714815 := by decide
  rcases family_descends (prefixWord ++ tailWord_2714815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2714876 : List Nat := [2, 2, 2, 1, 5, 2, 1, 3, 1, 4]
def baseStart_2714876 : Nat := 118140960795 + 2714876 * 2 ^ 59
def prefixEnd_2714876 : Nat := 4983230072969 + 3 ^ 40 * 2714876 * 2
def baseEnd_2714876 : Nat := 464678768451941756288173

theorem tailTrace_2714876 : CollatzResearch.WordTrace tailWord_2714876 prefixEnd_2714876 464678768451941756288173 := by
  unfold tailWord_2714876
  simp only [CollatzResearch.WordTrace]
  refine ⟨49509831256237695375870241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66013108341650260501160321 49509831256237695375870241)
  ·
    refine ⟨37132373442178271531902681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49509831256237695375870241 37132373442178271531902681)
    ·
      refine ⟨27849280081633703648927011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37132373442178271531902681 27849280081633703648927011)
      ·
        refine ⟨41773920122450555473390517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27849280081633703648927011 41773920122450555473390517)
        ·
          refine ⟨3916305011479739575630361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 41773920122450555473390517 3916305011479739575630361)
          ·
            refine ⟨2937228758609804681722771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3916305011479739575630361 2937228758609804681722771)
            ·
              refine ⟨4405843137914707022584157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2937228758609804681722771 4405843137914707022584157)
              ·
                refine ⟨1652191176718015133469059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4405843137914707022584157 1652191176718015133469059)
                ·
                  refine ⟨2478286765077022700203589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1652191176718015133469059 2478286765077022700203589)
                  ·
                    refine ⟨464678768451941756288173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2478286765077022700203589 464678768451941756288173)
                    ·
                      rfl

theorem cell23_2714876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 1, 3, 1, 4].length) (baseStart_2714876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2714876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2714876 prefixEnd_2714876 := by exact prefixLift 2714876
  have htrace : WordTrace (prefixWord ++ tailWord_2714876) baseStart_2714876 baseEnd_2714876 := by
    simpa [prefixWord, tailWord_2714876, baseEnd_2714876] using wordTrace_append hprefix tailTrace_2714876
  have hstable : (prefixWord ++ tailWord_2714876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2714876).length < 2 ^ (prefixWord ++ tailWord_2714876).sum := by decide
  have hdescent : baseEnd_2714876 < baseStart_2714876 := by decide
  rcases family_descends (prefixWord ++ tailWord_2714876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2714885 : List Nat := [1, 3, 1, 1, 2, 1, 3, 5, 1, 5]
def baseStart_2714885 : Nat := 118140960795 + 2714885 * 2 ^ 59
def prefixEnd_2714885 : Nat := 4983230072969 + 3 ^ 40 * 2714885 * 2
def baseEnd_2714885 : Nat := 464680308893905244550659

theorem tailTrace_2714885 : CollatzResearch.WordTrace tailWord_2714885 prefixEnd_2714885 464680308893905244550659 := by
  unfold tailWord_2714885
  simp only [CollatzResearch.WordTrace]
  refine ⟨99019990769442785288818109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66013327179628523525878739 99019990769442785288818109)
  ·
    refine ⟨37132496538541044483306791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99019990769442785288818109 37132496538541044483306791)
    ·
      refine ⟨55698744807811566724960187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37132496538541044483306791 55698744807811566724960187)
      ·
        refine ⟨83548117211717350087440281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55698744807811566724960187 83548117211717350087440281)
        ·
          refine ⟨62661087908788012565580211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83548117211717350087440281 62661087908788012565580211)
          ·
            refine ⟨93991631863182018848370317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62661087908788012565580211 93991631863182018848370317)
            ·
              refine ⟨35246861948693257068138869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 93991631863182018848370317 35246861948693257068138869)
              ·
                refine ⟨3304393307689992850138019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35246861948693257068138869 3304393307689992850138019)
                ·
                  refine ⟨4956589961534989275207029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3304393307689992850138019 4956589961534989275207029)
                  ·
                    refine ⟨464680308893905244550659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4956589961534989275207029 464680308893905244550659)
                    ·
                      rfl

theorem cell23_2714885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 5, 1, 5].length) (baseStart_2714885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2714885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2714885 prefixEnd_2714885 := by exact prefixLift 2714885
  have htrace : WordTrace (prefixWord ++ tailWord_2714885) baseStart_2714885 baseEnd_2714885 := by
    simpa [prefixWord, tailWord_2714885, baseEnd_2714885] using wordTrace_append hprefix tailTrace_2714885
  have hstable : (prefixWord ++ tailWord_2714885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2714885).length < 2 ^ (prefixWord ++ tailWord_2714885).sum := by decide
  have hdescent : baseEnd_2714885 < baseStart_2714885 := by decide
  rcases family_descends (prefixWord ++ tailWord_2714885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2714892 : List Nat := [2, 2, 1, 2, 2, 3, 1, 1, 4, 3, 2]
def baseStart_2714892 : Nat := 118140960795 + 2714892 * 2 ^ 59
def prefixEnd_2714892 : Nat := 4983230072969 + 3 ^ 40 * 2714892 * 2
def baseEnd_2714892 : Nat := 1394044521046297206264445

theorem tailTrace_2714892 : CollatzResearch.WordTrace tailWord_2714892 prefixEnd_2714892 1394044521046297206264445 := by
  unfold tailWord_2714892
  simp only [CollatzResearch.WordTrace]
  refine ⟨49510123040208712742161465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66013497386944950322881953 49510123040208712742161465)
  ·
    refine ⟨37132592280156534556621099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49510123040208712742161465 37132592280156534556621099)
    ·
      refine ⟨55698888420234801834931649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37132592280156534556621099 55698888420234801834931649)
      ·
        refine ⟨41774166315176101376198737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55698888420234801834931649 41774166315176101376198737)
        ·
          refine ⟨31330624736382076032149053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41774166315176101376198737 31330624736382076032149053)
          ·
            refine ⟨11748984276143278512055895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31330624736382076032149053 11748984276143278512055895)
            ·
              refine ⟨17623476414214917768083843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11748984276143278512055895 17623476414214917768083843)
              ·
                refine ⟨26435214621322376652125765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17623476414214917768083843 26435214621322376652125765)
                ·
                  refine ⟨4956602741497945622273581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26435214621322376652125765 4956602741497945622273581)
                  ·
                    refine ⟨1858726028061729608352593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4956602741497945622273581 1858726028061729608352593)
                    ·
                      refine ⟨1394044521046297206264445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1858726028061729608352593 1394044521046297206264445)
                      ·
                        rfl

theorem cell23_2714892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 1, 4, 3, 2].length) (baseStart_2714892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2714892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2714892 prefixEnd_2714892 := by exact prefixLift 2714892
  have htrace : WordTrace (prefixWord ++ tailWord_2714892) baseStart_2714892 baseEnd_2714892 := by
    simpa [prefixWord, tailWord_2714892, baseEnd_2714892] using wordTrace_append hprefix tailTrace_2714892
  have hstable : (prefixWord ++ tailWord_2714892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2714892).length < 2 ^ (prefixWord ++ tailWord_2714892).sum := by decide
  have hdescent : baseEnd_2714892 < baseStart_2714892 := by decide
  rcases family_descends (prefixWord ++ tailWord_2714892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2714928 : List Nat := [2, 1, 1, 1, 2, 2, 3, 11]
def baseStart_2714928 : Nat := 118140960795 + 2714928 * 2 ^ 59
def prefixEnd_2714928 : Nat := 4983230072969 + 3 ^ 40 * 2714928 * 2
def baseEnd_2714928 : Nat := 51631963198142928348677

theorem tailTrace_2714928 : CollatzResearch.WordTrace tailWord_2714928 prefixEnd_2714928 51631963198142928348677 := by
  unfold tailWord_2714928
  simp only [CollatzResearch.WordTrace]
  refine ⟨49510779554143501816316719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66014372738858002421755625 49510779554143501816316719)
  ·
    refine ⟨74266169331215252724475079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49510779554143501816316719 74266169331215252724475079)
    ·
      refine ⟨111399253996822879086712619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74266169331215252724475079 111399253996822879086712619)
      ·
        refine ⟨167098880995234318630068929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111399253996822879086712619 167098880995234318630068929)
        ·
          refine ⟨125324160746425738972551697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 167098880995234318630068929 125324160746425738972551697)
          ·
            refine ⟨93993120559819304229413773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 125324160746425738972551697 93993120559819304229413773)
            ·
              refine ⟨35247420209932239086030165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 93993120559819304229413773 35247420209932239086030165)
              ·
                refine ⟨51631963198142928348677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 35247420209932239086030165 51631963198142928348677)
                ·
                  rfl

theorem cell23_2714928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 11].length) (baseStart_2714928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2714928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2714928 prefixEnd_2714928 := by exact prefixLift 2714928
  have htrace : WordTrace (prefixWord ++ tailWord_2714928) baseStart_2714928 baseEnd_2714928 := by
    simpa [prefixWord, tailWord_2714928, baseEnd_2714928] using wordTrace_append hprefix tailTrace_2714928
  have hstable : (prefixWord ++ tailWord_2714928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2714928).length < 2 ^ (prefixWord ++ tailWord_2714928).sum := by decide
  have hdescent : baseEnd_2714928 < baseStart_2714928 := by decide
  rcases family_descends (prefixWord ++ tailWord_2714928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2714932 : List Nat := [2, 5, 1, 1, 1, 1, 3, 2, 1, 6]
def baseStart_2714932 : Nat := 118140960795 + 2714932 * 2 ^ 59
def prefixEnd_2714932 : Nat := 4983230072969 + 3 ^ 40 * 2714932 * 2
def baseEnd_2714932 : Nat := 464688353424159016588087

theorem tailTrace_2714932 : CollatzResearch.WordTrace tailWord_2714932 prefixEnd_2714932 464688353424159016588087 := by
  unfold tailWord_2714932
  simp only [CollatzResearch.WordTrace]
  refine ⟨49510852500136256157889525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66014470000181674877186033 49510852500136256157889525)
  ·
    refine ⟨4641642421887774014802143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 49510852500136256157889525 4641642421887774014802143)
    ·
      refine ⟨6962463632831661022203215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4641642421887774014802143 6962463632831661022203215)
      ·
        refine ⟨10443695449247491533304823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6962463632831661022203215 10443695449247491533304823)
        ·
          refine ⟨15665543173871237299957235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10443695449247491533304823 15665543173871237299957235)
          ·
            refine ⟨23498314760806855949935853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15665543173871237299957235 23498314760806855949935853)
            ·
              refine ⟨8811868035302570981225945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23498314760806855949935853 8811868035302570981225945)
              ·
                refine ⟨6608901026476928235919459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8811868035302570981225945 6608901026476928235919459)
                ·
                  refine ⟨9913351539715392353879189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6608901026476928235919459 9913351539715392353879189)
                  ·
                    refine ⟨464688353424159016588087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9913351539715392353879189 464688353424159016588087)
                    ·
                      rfl

theorem cell23_2714932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 2, 1, 6].length) (baseStart_2714932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2714932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2714932 prefixEnd_2714932 := by exact prefixLift 2714932
  have htrace : WordTrace (prefixWord ++ tailWord_2714932) baseStart_2714932 baseEnd_2714932 := by
    simpa [prefixWord, tailWord_2714932, baseEnd_2714932] using wordTrace_append hprefix tailTrace_2714932
  have hstable : (prefixWord ++ tailWord_2714932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2714932).length < 2 ^ (prefixWord ++ tailWord_2714932).sum := by decide
  have hdescent : baseEnd_2714932 < baseStart_2714932 := by decide
  rcases family_descends (prefixWord ++ tailWord_2714932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2714945 : List Nat := [1, 2, 5, 2, 1, 12]
def baseStart_2714945 : Nat := 118140960795 + 2714945 * 2 ^ 59
def prefixEnd_2714945 : Nat := 4983230072969 + 3 ^ 40 * 2714945 * 2
def baseEnd_2714945 : Nat := 5736920722308582300007

theorem tailTrace_2714945 : CollatzResearch.WordTrace tailWord_2714945 prefixEnd_2714945 5736920722308582300007 := by
  unfold tailWord_2714945
  simp only [CollatzResearch.WordTrace]
  refine ⟨99022179149225415536002289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66014786099483610357334859 99022179149225415536002289)
  ·
    refine ⟨74266634361919061652001717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99022179149225415536002289 74266634361919061652001717)
    ·
      refine ⟨6962496971429912029875161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 74266634361919061652001717 6962496971429912029875161)
      ·
        refine ⟨5221872728572434022406371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6962496971429912029875161 5221872728572434022406371)
        ·
          refine ⟨7832809092858651033609557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5221872728572434022406371 7832809092858651033609557)
          ·
            refine ⟨5736920722308582300007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 7832809092858651033609557 5736920722308582300007)
            ·
              rfl

theorem cell23_2714945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 12].length) (baseStart_2714945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2714945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2714945 prefixEnd_2714945 := by exact prefixLift 2714945
  have htrace : WordTrace (prefixWord ++ tailWord_2714945) baseStart_2714945 baseEnd_2714945 := by
    simpa [prefixWord, tailWord_2714945, baseEnd_2714945] using wordTrace_append hprefix tailTrace_2714945
  have hstable : (prefixWord ++ tailWord_2714945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2714945).length < 2 ^ (prefixWord ++ tailWord_2714945).sum := by decide
  have hdescent : baseEnd_2714945 < baseStart_2714945 := by decide
  rcases family_descends (prefixWord ++ tailWord_2714945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2714990 : List Nat := [4, 1, 2, 4, 2, 1, 2, 1, 1, 1, 4]
def baseStart_2714990 : Nat := 118140960795 + 2714990 * 2 ^ 59
def prefixEnd_2714990 : Nat := 4983230072969 + 3 ^ 40 * 2714990 * 2
def baseEnd_2714990 : Nat := 1394094842150437822838995

theorem tailTrace_2714990 : CollatzResearch.WordTrace tailWord_2714990 prefixEnd_2714990 1394094842150437822838995 := by
  unfold tailWord_2714990
  simp only [CollatzResearch.WordTrace]
  refine ⟨12377977554257798527673803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66015880289374925480926949 12377977554257798527673803)
  ·
    refine ⟨18566966331386697791510705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12377977554257798527673803 18566966331386697791510705)
    ·
      refine ⟨13925224748540023343633029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18566966331386697791510705 13925224748540023343633029)
      ·
        refine ⟨2610979640351254376931193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13925224748540023343633029 2610979640351254376931193)
        ·
          refine ⟨1958234730263440782698395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2610979640351254376931193 1958234730263440782698395)
          ·
            refine ⟨2937352095395161174047593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1958234730263440782698395 2937352095395161174047593)
            ·
              refine ⟨2203014071546370880535695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2937352095395161174047593 2203014071546370880535695)
              ·
                refine ⟨3304521107319556320803543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2203014071546370880535695 3304521107319556320803543)
                ·
                  refine ⟨4956781660979334481205315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3304521107319556320803543 4956781660979334481205315)
                  ·
                    refine ⟨7435172491469001721807973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4956781660979334481205315 7435172491469001721807973)
                    ·
                      refine ⟨1394094842150437822838995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7435172491469001721807973 1394094842150437822838995)
                      ·
                        rfl

theorem cell23_2714990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 2, 1, 1, 1, 4].length) (baseStart_2714990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2714990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2714990 prefixEnd_2714990 := by exact prefixLift 2714990
  have htrace : WordTrace (prefixWord ++ tailWord_2714990) baseStart_2714990 baseEnd_2714990 := by
    simpa [prefixWord, tailWord_2714990, baseEnd_2714990] using wordTrace_append hprefix tailTrace_2714990
  have hstable : (prefixWord ++ tailWord_2714990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2714990).length < 2 ^ (prefixWord ++ tailWord_2714990).sum := by decide
  have hdescent : baseEnd_2714990 < baseStart_2714990 := by decide
  rcases family_descends (prefixWord ++ tailWord_2714990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2714999 : List Nat := [1, 1, 3, 1, 1, 2, 5, 3, 1, 3, 2]
def baseStart_2714999 : Nat := 118140960795 + 2714999 * 2 ^ 59
def prefixEnd_2714999 : Nat := 4983230072969 + 3 ^ 40 * 2714999 * 2
def baseEnd_2714999 : Nat := 1394099463476328287626453

theorem tailTrace_2714999 : CollatzResearch.WordTrace tailWord_2714999 prefixEnd_2714999 1394099463476328287626453 := by
  unfold tailWord_2714999
  simp only [CollatzResearch.WordTrace]
  refine ⟨99024148691029782758468051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66016099127353188505645367 99024148691029782758468051)
  ·
    refine ⟨148536223036544674137702077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99024148691029782758468051 148536223036544674137702077)
    ·
      refine ⟨55701083638704252801638279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 148536223036544674137702077 55701083638704252801638279)
      ·
        refine ⟨83551625458056379202457419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55701083638704252801638279 83551625458056379202457419)
        ·
          refine ⟨125327438187084568803686129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83551625458056379202457419 125327438187084568803686129)
          ·
            refine ⟨93995578640313426602764597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 125327438187084568803686129 93995578640313426602764597)
            ·
              refine ⟨8812085497529383744009181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 93995578640313426602764597 8812085497529383744009181)
              ·
                refine ⟨3304532061573518904003443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8812085497529383744009181 3304532061573518904003443)
                ·
                  refine ⟨4956798092360278356005165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3304532061573518904003443 4956798092360278356005165)
                  ·
                    refine ⟨1858799284635104383501937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4956798092360278356005165 1858799284635104383501937)
                    ·
                      refine ⟨1394099463476328287626453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1858799284635104383501937 1394099463476328287626453)
                      ·
                        rfl

theorem cell23_2714999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 3, 1, 3, 2].length) (baseStart_2714999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2714999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2714999 prefixEnd_2714999 := by exact prefixLift 2714999
  have htrace : WordTrace (prefixWord ++ tailWord_2714999) baseStart_2714999 baseEnd_2714999 := by
    simpa [prefixWord, tailWord_2714999, baseEnd_2714999] using wordTrace_append hprefix tailTrace_2714999
  have hstable : (prefixWord ++ tailWord_2714999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2714999).length < 2 ^ (prefixWord ++ tailWord_2714999).sum := by decide
  have hdescent : baseEnd_2714999 < baseStart_2714999 := by decide
  rcases family_descends (prefixWord ++ tailWord_2714999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2715005 : List Nat := [1, 4, 1, 1, 2, 2, 1, 1, 4, 6]
def baseStart_2715005 : Nat := 118140960795 + 2715005 * 2 ^ 59
def prefixEnd_2715005 : Nat := 4983230072969 + 3 ^ 40 * 2715005 * 2
def baseEnd_2715005 : Nat := 464700848120085088050475

theorem tailTrace_2715005 : CollatzResearch.WordTrace tailWord_2715005 prefixEnd_2715005 464700848120085088050475 := by
  unfold tailWord_2715005
  simp only [CollatzResearch.WordTrace]
  refine ⟨99024367529008045783186469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66016245019338697188790979 99024367529008045783186469)
  ·
    refine ⟨18567068911689008584347463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 99024367529008045783186469 18567068911689008584347463)
    ·
      refine ⟨27850603367533512876521195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18567068911689008584347463 27850603367533512876521195)
      ·
        refine ⟨41775905051300269314781793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27850603367533512876521195 41775905051300269314781793)
        ·
          refine ⟨31331928788475201986086345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41775905051300269314781793 31331928788475201986086345)
          ·
            refine ⟨23498946591356401489564759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31331928788475201986086345 23498946591356401489564759)
            ·
              refine ⟨35248419887034602234347139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23498946591356401489564759 35248419887034602234347139)
              ·
                refine ⟨52872629830551903351520709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35248419887034602234347139 52872629830551903351520709)
                ·
                  refine ⟨9913618093228481878410133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 52872629830551903351520709 9913618093228481878410133)
                  ·
                    refine ⟨464700848120085088050475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9913618093228481878410133 464700848120085088050475)
                    ·
                      rfl

theorem cell23_2715005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 1, 4, 6].length) (baseStart_2715005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2715005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2715005 prefixEnd_2715005 := by exact prefixLift 2715005
  have htrace : WordTrace (prefixWord ++ tailWord_2715005) baseStart_2715005 baseEnd_2715005 := by
    simpa [prefixWord, tailWord_2715005, baseEnd_2715005] using wordTrace_append hprefix tailTrace_2715005
  have hstable : (prefixWord ++ tailWord_2715005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2715005).length < 2 ^ (prefixWord ++ tailWord_2715005).sum := by decide
  have hdescent : baseEnd_2715005 < baseStart_2715005 := by decide
  rcases family_descends (prefixWord ++ tailWord_2715005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2715029 : List Nat := [1, 3, 2, 1, 1, 2, 5, 1, 1, 4, 2]
def baseStart_2715029 : Nat := 118140960795 + 2715029 * 2 ^ 59
def prefixEnd_2715029 : Nat := 4983230072969 + 3 ^ 40 * 2715029 * 2
def baseEnd_2715029 : Nat := 1394114867895963170251315

theorem tailTrace_2715029 : CollatzResearch.WordTrace tailWord_2715029 prefixEnd_2715029 1394114867895963170251315 := by
  unfold tailWord_2715029
  simp only [CollatzResearch.WordTrace]
  refine ⟨99025242880921097882060141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66016828587280731921373427 99025242880921097882060141)
  ·
    refine ⟨37134466080345411705772553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99025242880921097882060141 37134466080345411705772553)
    ·
      refine ⟨27850849560259058779329415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37134466080345411705772553 27850849560259058779329415)
      ·
        refine ⟨41776274340388588168994123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27850849560259058779329415 41776274340388588168994123)
        ·
          refine ⟨62664411510582882253491185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41776274340388588168994123 62664411510582882253491185)
          ·
            refine ⟨46998308632937161690118389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62664411510582882253491185 46998308632937161690118389)
            ·
              refine ⟨4406091434337858908448599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 46998308632937161690118389 4406091434337858908448599)
              ·
                refine ⟨6609137151506788362672899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4406091434337858908448599 6609137151506788362672899)
                ·
                  refine ⟨9913705727260182544009349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6609137151506788362672899 9913705727260182544009349)
                  ·
                    refine ⟨1858819823861284227001753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9913705727260182544009349 1858819823861284227001753)
                    ·
                      refine ⟨1394114867895963170251315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1858819823861284227001753 1394114867895963170251315)
                      ·
                        rfl

theorem cell23_2715029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 5, 1, 1, 4, 2].length) (baseStart_2715029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2715029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2715029 prefixEnd_2715029 := by exact prefixLift 2715029
  have htrace : WordTrace (prefixWord ++ tailWord_2715029) baseStart_2715029 baseEnd_2715029 := by
    simpa [prefixWord, tailWord_2715029, baseEnd_2715029] using wordTrace_append hprefix tailTrace_2715029
  have hstable : (prefixWord ++ tailWord_2715029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2715029).length < 2 ^ (prefixWord ++ tailWord_2715029).sum := by decide
  have hdescent : baseEnd_2715029 < baseStart_2715029 := by decide
  rcases family_descends (prefixWord ++ tailWord_2715029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2715075 : List Nat := [1, 1, 1, 3, 1, 1, 5, 1, 1, 1, 7]
def baseStart_2715075 : Nat := 118140960795 + 2715075 * 2 ^ 59
def prefixEnd_2715075 : Nat := 4983230072969 + 3 ^ 40 * 2715075 * 2
def baseEnd_2715075 : Nat := 1394138488006069990276103

theorem tailTrace_2715075 : CollatzResearch.WordTrace tailWord_2715075 prefixEnd_2715075 1394138488006069990276103 := by
  unfold tailWord_2715075
  simp only [CollatzResearch.WordTrace]
  refine ⟨99026920638754447738234679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66017947092502965158823119 99026920638754447738234679)
  ·
    refine ⟨148540380958131671607352019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99026920638754447738234679 148540380958131671607352019)
    ·
      refine ⟨222810571437197507411028029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148540380958131671607352019 222810571437197507411028029)
      ·
        refine ⟨83553964288949065279135511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 222810571437197507411028029 83553964288949065279135511)
        ·
          refine ⟨125330946433423597918703267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83553964288949065279135511 125330946433423597918703267)
          ·
            refine ⟨187996419650135396878054901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125330946433423597918703267 187996419650135396878054901)
            ·
              refine ⟨17624664342200193457317647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 187996419650135396878054901 17624664342200193457317647)
              ·
                refine ⟨26436996513300290185976471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17624664342200193457317647 26436996513300290185976471)
                ·
                  refine ⟨39655494769950435278964707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26436996513300290185976471 39655494769950435278964707)
                  ·
                    refine ⟨59483242154925652918447061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39655494769950435278964707 59483242154925652918447061)
                    ·
                      refine ⟨1394138488006069990276103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 59483242154925652918447061 1394138488006069990276103)
                      ·
                        rfl

theorem cell23_2715075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 1, 1, 1, 7].length) (baseStart_2715075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2715075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2715075 prefixEnd_2715075 := by exact prefixLift 2715075
  have htrace : WordTrace (prefixWord ++ tailWord_2715075) baseStart_2715075 baseEnd_2715075 := by
    simpa [prefixWord, tailWord_2715075, baseEnd_2715075] using wordTrace_append hprefix tailTrace_2715075
  have hstable : (prefixWord ++ tailWord_2715075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2715075).length < 2 ^ (prefixWord ++ tailWord_2715075).sum := by decide
  have hdescent : baseEnd_2715075 < baseStart_2715075 := by decide
  rcases family_descends (prefixWord ++ tailWord_2715075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2715095 : List Nat := [1, 1, 3, 2, 1, 1, 1, 3, 2, 8]
def baseStart_2715095 : Nat := 118140960795 + 2715095 * 2 ^ 59
def prefixEnd_2715095 : Nat := 4983230072969 + 3 ^ 40 * 2715095 * 2
def baseEnd_2715095 : Nat := 464716252539719970675337

theorem tailTrace_2715095 : CollatzResearch.WordTrace tailWord_2715095 prefixEnd_2715095 464716252539719970675337 := by
  unfold tailWord_2715095
  simp only [CollatzResearch.WordTrace]
  refine ⟨99027650098681991153962739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66018433399121327435975159 99027650098681991153962739)
  ·
    refine ⟨148541475148022986730944109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99027650098681991153962739 148541475148022986730944109)
    ·
      refine ⟨55703053180508620024104041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 148541475148022986730944109 55703053180508620024104041)
      ·
        refine ⟨41777289885381465018078031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55703053180508620024104041 41777289885381465018078031)
        ·
          refine ⟨62665934828072197527117047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41777289885381465018078031 62665934828072197527117047)
          ·
            refine ⟨93998902242108296290675571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62665934828072197527117047 93998902242108296290675571)
            ·
              refine ⟨140998353363162444436013357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93998902242108296290675571 140998353363162444436013357)
              ·
                refine ⟨52874382511185916663505009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 140998353363162444436013357 52874382511185916663505009)
                ·
                  refine ⟨39655786883389437497628757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52874382511185916663505009 39655786883389437497628757)
                  ·
                    refine ⟨464716252539719970675337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 39655786883389437497628757 464716252539719970675337)
                    ·
                      rfl

theorem cell23_2715095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 3, 2, 8].length) (baseStart_2715095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2715095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2715095 prefixEnd_2715095 := by exact prefixLift 2715095
  have htrace : WordTrace (prefixWord ++ tailWord_2715095) baseStart_2715095 baseEnd_2715095 := by
    simpa [prefixWord, tailWord_2715095, baseEnd_2715095] using wordTrace_append hprefix tailTrace_2715095
  have hstable : (prefixWord ++ tailWord_2715095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2715095).length < 2 ^ (prefixWord ++ tailWord_2715095).sum := by decide
  have hdescent : baseEnd_2715095 < baseStart_2715095 := by decide
  rcases family_descends (prefixWord ++ tailWord_2715095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2715226 : List Nat := [3, 1, 1, 2, 1, 1, 1, 4, 5, 2, 2]
def baseStart_2715226 : Nat := 118140960795 + 2715226 * 2 ^ 59
def prefixEnd_2715226 : Nat := 4983230072969 + 3 ^ 40 * 2715226 * 2
def baseEnd_2715226 : Nat := 1394216023584898899487909

theorem tailTrace_2715226 : CollatzResearch.WordTrace tailWord_2715226 prefixEnd_2715226 1394216023584898899487909 := by
  unfold tailWord_2715226
  simp only [CollatzResearch.WordTrace]
  refine ⟨24758107015301850131745383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66021618707471600351321021 24758107015301850131745383)
  ·
    refine ⟨37137160522952775197618075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24758107015301850131745383 37137160522952775197618075)
    ·
      refine ⟨55705740784429162796427113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37137160522952775197618075 55705740784429162796427113)
      ·
        refine ⟨41779305588321872097320335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55705740784429162796427113 41779305588321872097320335)
        ·
          refine ⟨62668958382482808145980503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41779305588321872097320335 62668958382482808145980503)
          ·
            refine ⟨94003437573724212218970755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62668958382482808145980503 94003437573724212218970755)
            ·
              refine ⟨141005156360586318328456133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94003437573724212218970755 141005156360586318328456133)
              ·
                refine ⟨26438466817609934686585525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 141005156360586318328456133 26438466817609934686585525)
                ·
                  refine ⟨2478606264150931376867393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26438466817609934686585525 2478606264150931376867393)
                  ·
                    refine ⟨1858954698113198532650545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2478606264150931376867393 1858954698113198532650545)
                    ·
                      refine ⟨1394216023584898899487909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1858954698113198532650545 1394216023584898899487909)
                      ·
                        rfl

theorem cell23_2715226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 4, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 4, 5, 2, 2].length) (baseStart_2715226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2715226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2715226 prefixEnd_2715226 := by exact prefixLift 2715226
  have htrace : WordTrace (prefixWord ++ tailWord_2715226) baseStart_2715226 baseEnd_2715226 := by
    simpa [prefixWord, tailWord_2715226, baseEnd_2715226] using wordTrace_append hprefix tailTrace_2715226
  have hstable : (prefixWord ++ tailWord_2715226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2715226).length < 2 ^ (prefixWord ++ tailWord_2715226).sum := by decide
  have hdescent : baseEnd_2715226 < baseStart_2715226 := by decide
  rcases family_descends (prefixWord ++ tailWord_2715226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2715253 : List Nat := [1, 3, 4, 2, 1, 2, 1, 3, 2, 4]
def baseStart_2715253 : Nat := 118140960795 + 2715253 * 2 ^ 59
def prefixEnd_2715253 : Nat := 4983230072969 + 3 ^ 40 * 2715253 * 2
def baseEnd_2715253 : Nat := 464743295854190097950095

theorem tailTrace_2715253 : CollatzResearch.WordTrace tailWord_2715253 prefixEnd_2715253 464743295854190097950095 := by
  unfold tailWord_2715253
  simp only [CollatzResearch.WordTrace]
  refine ⟨99033412832109584138214413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66022275221406389425476275 99033412832109584138214413)
  ·
    refine ⟨37137529812041094051830405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99033412832109584138214413 37137529812041094051830405)
    ·
      refine ⟨6963286839757705134718201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37137529812041094051830405 6963286839757705134718201)
      ·
        refine ⟨5222465129818278851038651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6963286839757705134718201 5222465129818278851038651)
        ·
          refine ⟨7833697694727418276557977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5222465129818278851038651 7833697694727418276557977)
          ·
            refine ⟨5875273271045563707418483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7833697694727418276557977 5875273271045563707418483)
            ·
              refine ⟨8812909906568345561127725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5875273271045563707418483 8812909906568345561127725)
              ·
                refine ⟨3304841214963129585422897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8812909906568345561127725 3304841214963129585422897)
                ·
                  refine ⟨2478630911222347189067173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3304841214963129585422897 2478630911222347189067173)
                  ·
                    refine ⟨464743295854190097950095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2478630911222347189067173 464743295854190097950095)
                    ·
                      rfl

theorem cell23_2715253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 3, 2, 4].length) (baseStart_2715253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2715253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2715253 prefixEnd_2715253 := by exact prefixLift 2715253
  have htrace : WordTrace (prefixWord ++ tailWord_2715253) baseStart_2715253 baseEnd_2715253 := by
    simpa [prefixWord, tailWord_2715253, baseEnd_2715253] using wordTrace_append hprefix tailTrace_2715253
  have hstable : (prefixWord ++ tailWord_2715253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2715253).length < 2 ^ (prefixWord ++ tailWord_2715253).sum := by decide
  have hdescent : baseEnd_2715253 < baseStart_2715253 := by decide
  rcases family_descends (prefixWord ++ tailWord_2715253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2715259 : List Nat := [1, 1, 1, 1, 1, 4, 4, 3, 1, 3, 3]
def baseStart_2715259 : Nat := 118140960795 + 2715259 * 2 ^ 59
def prefixEnd_2715259 : Nat := 4983230072969 + 3 ^ 40 * 2715259 * 2
def baseEnd_2715259 : Nat := 1394232968446497270375257

theorem tailTrace_2715259 : CollatzResearch.WordTrace tailWord_2715259 prefixEnd_2715259 1394232968446497270375257 := by
  unfold tailWord_2715259
  simp only [CollatzResearch.WordTrace]
  refine ⟨99033631670087847162932831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66022421113391898108621887 99033631670087847162932831)
  ·
    refine ⟨148550447505131770744399247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99033631670087847162932831 148550447505131770744399247)
    ·
      refine ⟨222825671257697656116598871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148550447505131770744399247 222825671257697656116598871)
      ·
        refine ⟨334238506886546484174898307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222825671257697656116598871 334238506886546484174898307)
        ·
          refine ⟨501357760329819726262347461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 334238506886546484174898307 501357760329819726262347461)
          ·
            refine ⟨94004580061841198674190149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 501357760329819726262347461 94004580061841198674190149)
            ·
              refine ⟨17625858761595224751410653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 94004580061841198674190149 17625858761595224751410653)
              ·
                refine ⟨6609697035598209281778995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17625858761595224751410653 6609697035598209281778995)
                ·
                  refine ⟨9914545553397313922668493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6609697035598209281778995 9914545553397313922668493)
                  ·
                    refine ⟨3717954582523992721000685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9914545553397313922668493 3717954582523992721000685)
                    ·
                      refine ⟨1394232968446497270375257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3717954582523992721000685 1394232968446497270375257)
                      ·
                        rfl

theorem cell23_2715259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 3, 1, 3, 3].length) (baseStart_2715259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2715259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2715259 prefixEnd_2715259 := by exact prefixLift 2715259
  have htrace : WordTrace (prefixWord ++ tailWord_2715259) baseStart_2715259 baseEnd_2715259 := by
    simpa [prefixWord, tailWord_2715259, baseEnd_2715259] using wordTrace_append hprefix tailTrace_2715259
  have hstable : (prefixWord ++ tailWord_2715259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2715259).length < 2 ^ (prefixWord ++ tailWord_2715259).sum := by decide
  have hdescent : baseEnd_2715259 < baseStart_2715259 := by decide
  rcases family_descends (prefixWord ++ tailWord_2715259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2715294 : List Nat := [4, 3, 1, 1, 1, 2, 4, 2, 1, 2, 2]
def baseStart_2715294 : Nat := 118140960795 + 2715294 * 2 ^ 59
def prefixEnd_2715294 : Nat := 4983230072969 + 3 ^ 40 * 2715294 * 2
def baseEnd_2715294 : Nat := 1394250940269404633437597

theorem tailTrace_2715294 : CollatzResearch.WordTrace tailWord_2715294 prefixEnd_2715294 1394250940269404633437597 := by
  unfold tailWord_2715294
  simp only [CollatzResearch.WordTrace]
  refine ⟨12379363528120131017557117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66023272149974032093637957 12379363528120131017557117)
  ·
    refine ⟨4642261323045049131583919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12379363528120131017557117 4642261323045049131583919)
    ·
      refine ⟨6963391984567573697375879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4642261323045049131583919 6963391984567573697375879)
      ·
        refine ⟨10445087976851360546063819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6963391984567573697375879 10445087976851360546063819)
        ·
          refine ⟨15667631965277040819095729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10445087976851360546063819 15667631965277040819095729)
          ·
            refine ⟨11750723973957780614321797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15667631965277040819095729 11750723973957780614321797)
            ·
              refine ⟨2203260745117083865185337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11750723973957780614321797 2203260745117083865185337)
              ·
                refine ⟨1652445558837812898889003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2203260745117083865185337 1652445558837812898889003)
                ·
                  refine ⟨2478668338256719348333505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1652445558837812898889003 2478668338256719348333505)
                  ·
                    refine ⟨1859001253692539511250129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2478668338256719348333505 1859001253692539511250129)
                    ·
                      refine ⟨1394250940269404633437597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1859001253692539511250129 1394250940269404633437597)
                      ·
                        rfl

theorem cell23_2715294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 4, 2, 1, 2, 2].length) (baseStart_2715294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2715294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2715294 prefixEnd_2715294 := by exact prefixLift 2715294
  have htrace : WordTrace (prefixWord ++ tailWord_2715294) baseStart_2715294 baseEnd_2715294 := by
    simpa [prefixWord, tailWord_2715294, baseEnd_2715294] using wordTrace_append hprefix tailTrace_2715294
  have hstable : (prefixWord ++ tailWord_2715294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2715294).length < 2 ^ (prefixWord ++ tailWord_2715294).sum := by decide
  have hdescent : baseEnd_2715294 < baseStart_2715294 := by decide
  rcases family_descends (prefixWord ++ tailWord_2715294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2715310 : List Nat := [4, 1, 4, 1, 2, 1, 2, 1, 1, 3, 3]
def baseStart_2715310 : Nat := 118140960795 + 2715310 * 2 ^ 59
def prefixEnd_2715310 : Nat := 4983230072969 + 3 ^ 40 * 2715310 * 2
def baseEnd_2715310 : Nat := 1394259155959876570837523

theorem tailTrace_2715310 : CollatzResearch.WordTrace tailWord_2715310 prefixEnd_2715310 1394259155959876570837523 := by
  unfold tailWord_2715310
  simp only [CollatzResearch.WordTrace]
  refine ⟨12379436474112885359129923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66023661195268721915359589 12379436474112885359129923)
  ·
    refine ⟨18569154711169328038694885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12379436474112885359129923 18569154711169328038694885)
    ·
      refine ⟨3481716508344249007255291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18569154711169328038694885 3481716508344249007255291)
      ·
        refine ⟨5222574762516373510882937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3481716508344249007255291 5222574762516373510882937)
        ·
          refine ⟨3916931071887280133162203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5222574762516373510882937 3916931071887280133162203)
          ·
            refine ⟨5875396607830920199743305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3916931071887280133162203 5875396607830920199743305)
            ·
              refine ⟨4406547455873190149807479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5875396607830920199743305 4406547455873190149807479)
              ·
                refine ⟨6609821183809785224711219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4406547455873190149807479 6609821183809785224711219)
                ·
                  refine ⟨9914731775714677837066829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6609821183809785224711219 9914731775714677837066829)
                  ·
                    refine ⟨3718024415893004188900061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9914731775714677837066829 3718024415893004188900061)
                    ·
                      refine ⟨1394259155959876570837523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3718024415893004188900061 1394259155959876570837523)
                      ·
                        rfl

theorem cell23_2715310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 2, 1, 1, 3, 3].length) (baseStart_2715310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2715310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2715310 prefixEnd_2715310 := by exact prefixLift 2715310
  have htrace : WordTrace (prefixWord ++ tailWord_2715310) baseStart_2715310 baseEnd_2715310 := by
    simpa [prefixWord, tailWord_2715310, baseEnd_2715310] using wordTrace_append hprefix tailTrace_2715310
  have hstable : (prefixWord ++ tailWord_2715310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2715310).length < 2 ^ (prefixWord ++ tailWord_2715310).sum := by decide
  have hdescent : baseEnd_2715310 < baseStart_2715310 := by decide
  rcases family_descends (prefixWord ++ tailWord_2715310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2715346 : List Nat := [3, 2, 2, 2, 2, 1, 1, 2, 2, 2, 4]
def baseStart_2715346 : Nat := 118140960795 + 2715346 * 2 ^ 59
def prefixEnd_2715346 : Nat := 4983230072969 + 3 ^ 40 * 2715346 * 2
def baseEnd_2715346 : Nat := 1394277641263438429987357

theorem tailTrace_2715346 : CollatzResearch.WordTrace tailWord_2715346 prefixEnd_2715346 1394277641263438429987357 := by
  unfold tailWord_2715346
  simp only [CollatzResearch.WordTrace]
  refine ⟨24759201205193165255337473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66024536547181774014233261 24759201205193165255337473)
  ·
    refine ⟨18569400903894873941503105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24759201205193165255337473 18569400903894873941503105)
    ·
      refine ⟨13927050677921155456127329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18569400903894873941503105 13927050677921155456127329)
      ·
        refine ⟨10445288008440866592095497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13927050677921155456127329 10445288008440866592095497)
        ·
          refine ⟨7833966006330649944071623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10445288008440866592095497 7833966006330649944071623)
          ·
            refine ⟨11750949009495974916107435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7833966006330649944071623 11750949009495974916107435)
            ·
              refine ⟨17626423514243962374161153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11750949009495974916107435 17626423514243962374161153)
              ·
                refine ⟨13219817635682971780620865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17626423514243962374161153 13219817635682971780620865)
                ·
                  refine ⟨9914863226762228835465649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13219817635682971780620865 9914863226762228835465649)
                  ·
                    refine ⟨7436147420071671626599237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9914863226762228835465649 7436147420071671626599237)
                    ·
                      refine ⟨1394277641263438429987357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7436147420071671626599237 1394277641263438429987357)
                      ·
                        rfl

theorem cell23_2715346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 2, 2, 2, 4].length) (baseStart_2715346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2715346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2715346 prefixEnd_2715346 := by exact prefixLift 2715346
  have htrace : WordTrace (prefixWord ++ tailWord_2715346) baseStart_2715346 baseEnd_2715346 := by
    simpa [prefixWord, tailWord_2715346, baseEnd_2715346] using wordTrace_append hprefix tailTrace_2715346
  have hstable : (prefixWord ++ tailWord_2715346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2715346).length < 2 ^ (prefixWord ++ tailWord_2715346).sum := by decide
  have hdescent : baseEnd_2715346 < baseStart_2715346 := by decide
  rcases family_descends (prefixWord ++ tailWord_2715346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2715367 : List Nat := [1, 1, 5, 4, 1, 2, 1, 1, 1, 4, 2]
def baseStart_2715367 : Nat := 118140960795 + 2715367 * 2 ^ 59
def prefixEnd_2715367 : Nat := 4983230072969 + 3 ^ 40 * 2715367 * 2
def baseEnd_2715367 : Nat := 1394288424357182847824761

theorem tailTrace_2715367 : CollatzResearch.WordTrace tailWord_2715367 prefixEnd_2715367 1394288424357182847824761 := by
  unfold tailWord_2715367
  simp only [CollatzResearch.WordTrace]
  refine ⟨99037570753696581607864355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66025047169131054405242903 99037570753696581607864355)
  ·
    refine ⟨148556356130544872411796533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99037570753696581607864355 148556356130544872411796533)
    ·
      refine ⟨13927158387238581788605925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 148556356130544872411796533 13927158387238581788605925)
      ·
        refine ⟨2611342197607234085363611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13927158387238581788605925 2611342197607234085363611)
        ·
          refine ⟨3917013296410851128045417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2611342197607234085363611 3917013296410851128045417)
          ·
            refine ⟨2937759972308138346034063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3917013296410851128045417 2937759972308138346034063)
            ·
              refine ⟨4406639958462207519051095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2937759972308138346034063 4406639958462207519051095)
              ·
                refine ⟨6609959937693311278576643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4406639958462207519051095 6609959937693311278576643)
                ·
                  refine ⟨9914939906539966917864965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6609959937693311278576643 9914939906539966917864965)
                  ·
                    refine ⟨1859051232476243797099681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9914939906539966917864965 1859051232476243797099681)
                    ·
                      refine ⟨1394288424357182847824761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1859051232476243797099681 1394288424357182847824761)
                      ·
                        rfl

theorem cell23_2715367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 1, 1, 1, 4, 2].length) (baseStart_2715367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2715367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2715367 prefixEnd_2715367 := by exact prefixLift 2715367
  have htrace : WordTrace (prefixWord ++ tailWord_2715367) baseStart_2715367 baseEnd_2715367 := by
    simpa [prefixWord, tailWord_2715367, baseEnd_2715367] using wordTrace_append hprefix tailTrace_2715367
  have hstable : (prefixWord ++ tailWord_2715367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2715367).length < 2 ^ (prefixWord ++ tailWord_2715367).sum := by decide
  have hdescent : baseEnd_2715367 < baseStart_2715367 := by decide
  rcases family_descends (prefixWord ++ tailWord_2715367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2715406 : List Nat := [4, 1, 1, 2, 1, 1, 3, 1, 4, 1, 4]
def baseStart_2715406 : Nat := 118140960795 + 2715406 * 2 ^ 59
def prefixEnd_2715406 : Nat := 4983230072969 + 3 ^ 40 * 2715406 * 2
def baseEnd_2715406 : Nat := 1394308450102708195237081

theorem tailTrace_2715406 : CollatzResearch.WordTrace tailWord_2715406 prefixEnd_2715406 1394308450102708195237081 := by
  unfold tailWord_2715406
  simp only [CollatzResearch.WordTrace]
  refine ⟨12379874150069411408566759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66025995467036860845689381 12379874150069411408566759)
  ·
    refine ⟨18569811225104117112850139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12379874150069411408566759 18569811225104117112850139)
    ·
      refine ⟨27854716837656175669275209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18569811225104117112850139 27854716837656175669275209)
      ·
        refine ⟨20891037628242131751956407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27854716837656175669275209 20891037628242131751956407)
        ·
          refine ⟨31336556442363197627934611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20891037628242131751956407 31336556442363197627934611)
          ·
            refine ⟨47004834663544796441901917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31336556442363197627934611 47004834663544796441901917)
            ·
              refine ⟨17626812998829298665713219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47004834663544796441901917 17626812998829298665713219)
              ·
                refine ⟨26440219498243947998569829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17626812998829298665713219 26440219498243947998569829)
                ·
                  refine ⟨4957541155920740249731843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26440219498243947998569829 4957541155920740249731843)
                  ·
                    refine ⟨7436311733881110374597765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4957541155920740249731843 7436311733881110374597765)
                    ·
                      refine ⟨1394308450102708195237081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7436311733881110374597765 1394308450102708195237081)
                      ·
                        rfl

theorem cell23_2715406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 1, 4, 1, 4].length) (baseStart_2715406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2715406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2715406 prefixEnd_2715406 := by exact prefixLift 2715406
  have htrace : WordTrace (prefixWord ++ tailWord_2715406) baseStart_2715406 baseEnd_2715406 := by
    simpa [prefixWord, tailWord_2715406, baseEnd_2715406] using wordTrace_append hprefix tailTrace_2715406
  have hstable : (prefixWord ++ tailWord_2715406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2715406).length < 2 ^ (prefixWord ++ tailWord_2715406).sum := by decide
  have hdescent : baseEnd_2715406 < baseStart_2715406 := by decide
  rcases family_descends (prefixWord ++ tailWord_2715406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2715490 : List Nat := [3, 3, 2, 1, 2, 1, 1, 1, 5, 1, 3]
def baseStart_2715490 : Nat := 118140960795 + 2715490 * 2 ^ 59
def prefixEnd_2715490 : Nat := 4983230072969 + 3 ^ 40 * 2715490 * 2
def baseEnd_2715490 : Nat := 1394351582477685866586695

theorem tailTrace_2715490 : CollatzResearch.WordTrace tailWord_2715490 prefixEnd_2715490 1394351582477685866586695 := by
  unfold tailWord_2715490
  simp only [CollatzResearch.WordTrace]
  refine ⟨24760514233062743403647981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66028037954833982409727949 24760514233062743403647981)
  ·
    refine ⟨9285192837398528776367993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24760514233062743403647981 9285192837398528776367993)
    ·
      refine ⟨6963894628048896582275995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9285192837398528776367993 6963894628048896582275995)
      ·
        refine ⟨10445841942073344873413993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6963894628048896582275995 10445841942073344873413993)
        ·
          refine ⟨7834381456555008655060495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10445841942073344873413993 7834381456555008655060495)
          ·
            refine ⟨11751572184832512982590743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7834381456555008655060495 11751572184832512982590743)
            ·
              refine ⟨17627358277248769473886115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11751572184832512982590743 17627358277248769473886115)
              ·
                refine ⟨26441037415873154210829173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17627358277248769473886115 26441037415873154210829173)
                ·
                  refine ⟨2478847257738108207265235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26441037415873154210829173 2478847257738108207265235)
                  ·
                    refine ⟨3718270886607162310897853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2478847257738108207265235 3718270886607162310897853)
                    ·
                      refine ⟨1394351582477685866586695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3718270886607162310897853 1394351582477685866586695)
                      ·
                        rfl

theorem cell23_2715490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 1, 5, 1, 3].length) (baseStart_2715490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2715490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2715490 prefixEnd_2715490 := by exact prefixLift 2715490
  have htrace : WordTrace (prefixWord ++ tailWord_2715490) baseStart_2715490 baseEnd_2715490 := by
    simpa [prefixWord, tailWord_2715490, baseEnd_2715490] using wordTrace_append hprefix tailTrace_2715490
  have hstable : (prefixWord ++ tailWord_2715490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2715490).length < 2 ^ (prefixWord ++ tailWord_2715490).sum := by decide
  have hdescent : baseEnd_2715490 < baseStart_2715490 := by decide
  rcases family_descends (prefixWord ++ tailWord_2715490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2715500 : List Nat := [2, 2, 1, 1, 4, 2, 3, 1, 2, 3, 2]
def baseStart_2715500 : Nat := 118140960795 + 2715500 * 2 ^ 59
def prefixEnd_2715500 : Nat := 4983230072969 + 3 ^ 40 * 2715500 * 2
def baseEnd_2715500 : Nat := 1394356717284230827461649

theorem tailTrace_2715500 : CollatzResearch.WordTrace tailWord_2715500 prefixEnd_2715500 1394356717284230827461649 := by
  unfold tailWord_2715500
  simp only [CollatzResearch.WordTrace]
  refine ⟨49521210831107372661227977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66028281108143163548303969 49521210831107372661227977)
  ·
    refine ⟨37140908123330529495920983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49521210831107372661227977 37140908123330529495920983)
    ·
      refine ⟨55711362184995794243881475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37140908123330529495920983 55711362184995794243881475)
      ·
        refine ⟨83567043277493691365822213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55711362184995794243881475 83567043277493691365822213)
        ·
          refine ⟨15668820614530067131091665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 83567043277493691365822213 15668820614530067131091665)
          ·
            refine ⟨11751615460897550348318749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15668820614530067131091665 11751615460897550348318749)
            ·
              refine ⟨4406855797836581380619531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11751615460897550348318749 4406855797836581380619531)
              ·
                refine ⟨6610283696754872070929297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4406855797836581380619531 6610283696754872070929297)
                ·
                  refine ⟨4957712772566154053196973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6610283696754872070929297 4957712772566154053196973)
                  ·
                    refine ⟨1859142289712307769948865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4957712772566154053196973 1859142289712307769948865)
                    ·
                      refine ⟨1394356717284230827461649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1859142289712307769948865 1394356717284230827461649)
                      ·
                        rfl

theorem cell23_2715500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 3, 2].length) (baseStart_2715500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2715500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2715500 prefixEnd_2715500 := by exact prefixLift 2715500
  have htrace : WordTrace (prefixWord ++ tailWord_2715500) baseStart_2715500 baseEnd_2715500 := by
    simpa [prefixWord, tailWord_2715500, baseEnd_2715500] using wordTrace_append hprefix tailTrace_2715500
  have hstable : (prefixWord ++ tailWord_2715500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2715500).length < 2 ^ (prefixWord ++ tailWord_2715500).sum := by decide
  have hdescent : baseEnd_2715500 < baseStart_2715500 := by decide
  rcases family_descends (prefixWord ++ tailWord_2715500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2715513 : List Nat := [1, 2, 1, 3, 2, 2, 3, 3, 1, 1, 4]
def baseStart_2715513 : Nat := 118140960795 + 2715513 * 2 ^ 59
def prefixEnd_2715513 : Nat := 4983230072969 + 3 ^ 40 * 2715513 * 2
def baseEnd_2715513 : Nat := 1394363392532739276599089

theorem tailTrace_2715513 : CollatzResearch.WordTrace tailWord_2715513 prefixEnd_2715513 1394363392532739276599089 := by
  unfold tailWord_2715513
  simp only [CollatzResearch.WordTrace]
  refine ⟨99042895811167648542679193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66028597207445099028452795 99042895811167648542679193)
  ·
    refine ⟨74282171858375736407009395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99042895811167648542679193 74282171858375736407009395)
    ·
      refine ⟨111423257787563604610514093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74282171858375736407009395 111423257787563604610514093)
      ·
        refine ⟨41783721670336351728942785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 111423257787563604610514093 41783721670336351728942785)
        ·
          refine ⟨31337791252752263796707089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41783721670336351728942785 31337791252752263796707089)
          ·
            refine ⟨23503343439564197847530317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31337791252752263796707089 23503343439564197847530317)
            ·
              refine ⟨8813753789836574192823869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23503343439564197847530317 8813753789836574192823869)
              ·
                refine ⟨3305157671188715322308951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8813753789836574192823869 3305157671188715322308951)
                ·
                  refine ⟨4957736506783072983463427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3305157671188715322308951 4957736506783072983463427)
                  ·
                    refine ⟨7436604760174609475195141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4957736506783072983463427 7436604760174609475195141)
                    ·
                      refine ⟨1394363392532739276599089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7436604760174609475195141 1394363392532739276599089)
                      ·
                        rfl

theorem cell23_2715513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 3, 1, 1, 4].length) (baseStart_2715513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2715513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2715513 prefixEnd_2715513 := by exact prefixLift 2715513
  have htrace : WordTrace (prefixWord ++ tailWord_2715513) baseStart_2715513 baseEnd_2715513 := by
    simpa [prefixWord, tailWord_2715513, baseEnd_2715513] using wordTrace_append hprefix tailTrace_2715513
  have hstable : (prefixWord ++ tailWord_2715513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2715513).length < 2 ^ (prefixWord ++ tailWord_2715513).sum := by decide
  have hdescent : baseEnd_2715513 < baseStart_2715513 := by decide
  rcases family_descends (prefixWord ++ tailWord_2715513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2715523 : List Nat := [1, 1, 1, 3, 4, 3, 1, 1, 4, 4]
def baseStart_2715523 : Nat := 118140960795 + 2715523 * 2 ^ 59
def prefixEnd_2715523 : Nat := 4983230072969 + 3 ^ 40 * 2715523 * 2
def baseEnd_2715523 : Nat := 464789509113094745824681

theorem tailTrace_2715523 : CollatzResearch.WordTrace tailWord_2715523 prefixEnd_2715523 464789509113094745824681 := by
  unfold tailWord_2715523
  simp only [CollatzResearch.WordTrace]
  refine ⟨99043260541131420250543223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66028840360754280167028815 99043260541131420250543223)
  ·
    refine ⟨148564890811697130375814835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99043260541131420250543223 148564890811697130375814835)
    ·
      refine ⟨222847336217545695563722253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148564890811697130375814835 222847336217545695563722253)
      ·
        refine ⟨83567751081579635836395845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 222847336217545695563722253 83567751081579635836395845)
        ·
          refine ⟨15668953327796181719324221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 83567751081579635836395845 15668953327796181719324221)
          ·
            refine ⟨5875857497923568144746583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15668953327796181719324221 5875857497923568144746583)
            ·
              refine ⟨8813786246885352217119875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5875857497923568144746583 8813786246885352217119875)
              ·
                refine ⟨13220679370328028325679813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8813786246885352217119875 13220679370328028325679813)
                ·
                  refine ⟨2478877381936505311064965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13220679370328028325679813 2478877381936505311064965)
                  ·
                    refine ⟨464789509113094745824681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2478877381936505311064965 464789509113094745824681)
                    ·
                      rfl

theorem cell23_2715523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 1, 4, 4].length) (baseStart_2715523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2715523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2715523 prefixEnd_2715523 := by exact prefixLift 2715523
  have htrace : WordTrace (prefixWord ++ tailWord_2715523) baseStart_2715523 baseEnd_2715523 := by
    simpa [prefixWord, tailWord_2715523, baseEnd_2715523] using wordTrace_append hprefix tailTrace_2715523
  have hstable : (prefixWord ++ tailWord_2715523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2715523).length < 2 ^ (prefixWord ++ tailWord_2715523).sum := by decide
  have hdescent : baseEnd_2715523 < baseStart_2715523 := by decide
  rcases family_descends (prefixWord ++ tailWord_2715523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2715540 : List Nat := [2, 4, 2, 1, 1, 4, 1, 1, 1, 6]
def baseStart_2715540 : Nat := 118140960795 + 2715540 * 2 ^ 59
def prefixEnd_2715540 : Nat := 4983230072969 + 3 ^ 40 * 2715540 * 2
def baseEnd_2715540 : Nat := 464792418836803556987155

theorem tailTrace_2715540 : CollatzResearch.WordTrace tailWord_2715540 prefixEnd_2715540 464792418836803556987155 := by
  unfold tailWord_2715540
  simp only [CollatzResearch.WordTrace]
  refine ⟨49521940291034916076956037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66029253721379888102608049 49521940291034916076956037)
  ·
    refine ⟨9285363804569046764429257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49521940291034916076956037 9285363804569046764429257)
    ·
      refine ⟨6964022853426785073321943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9285363804569046764429257 6964022853426785073321943)
      ·
        refine ⟨10446034280140177609982915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6964022853426785073321943 10446034280140177609982915)
        ·
          refine ⟨15669051420210266414974373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10446034280140177609982915 15669051420210266414974373)
          ·
            refine ⟨2937947141289424952807695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15669051420210266414974373 2937947141289424952807695)
            ·
              refine ⟨4406920711934137429211543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2937947141289424952807695 4406920711934137429211543)
              ·
                refine ⟨6610381067901206143817315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4406920711934137429211543 6610381067901206143817315)
                ·
                  refine ⟨9915571601851809215725973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6610381067901206143817315 9915571601851809215725973)
                  ·
                    refine ⟨464792418836803556987155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9915571601851809215725973 464792418836803556987155)
                    ·
                      rfl

theorem cell23_2715540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 1, 1, 1, 6].length) (baseStart_2715540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2715540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2715540 prefixEnd_2715540 := by exact prefixLift 2715540
  have htrace : WordTrace (prefixWord ++ tailWord_2715540) baseStart_2715540 baseEnd_2715540 := by
    simpa [prefixWord, tailWord_2715540, baseEnd_2715540] using wordTrace_append hprefix tailTrace_2715540
  have hstable : (prefixWord ++ tailWord_2715540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2715540).length < 2 ^ (prefixWord ++ tailWord_2715540).sum := by decide
  have hdescent : baseEnd_2715540 < baseStart_2715540 := by decide
  rcases family_descends (prefixWord ++ tailWord_2715540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2715543 : List Nat := [1, 1, 3, 3, 1, 3, 3, 1, 1, 2, 4]
def baseStart_2715543 : Nat := 118140960795 + 2715543 * 2 ^ 59
def prefixEnd_2715543 : Nat := 4983230072969 + 3 ^ 40 * 2715543 * 2
def baseEnd_2715543 : Nat := 1394378796952374159223951

theorem tailTrace_2715543 : CollatzResearch.WordTrace tailWord_2715543 prefixEnd_2715543 1394378796952374159223951 := by
  unfold tailWord_2715543
  simp only [CollatzResearch.WordTrace]
  refine ⟨99043990001058963666271283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66029326667372642444180855 99043990001058963666271283)
  ·
    refine ⟨148565985001588445499406925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99043990001058963666271283 148565985001588445499406925)
    ·
      refine ⟨55712244375595667062277597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 148565985001588445499406925 55712244375595667062277597)
      ·
        refine ⟨20892091640848375148354099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55712244375595667062277597 20892091640848375148354099)
        ·
          refine ⟨31338137461272562722531149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20892091640848375148354099 31338137461272562722531149)
          ·
            refine ⟨11751801547977211020949181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31338137461272562722531149 11751801547977211020949181)
            ·
              refine ⟨4406925580491454132855943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11751801547977211020949181 4406925580491454132855943)
              ·
                refine ⟨6610388370737181199283915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4406925580491454132855943 6610388370737181199283915)
                ·
                  refine ⟨9915582556105771798925873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6610388370737181199283915 9915582556105771798925873)
                  ·
                    refine ⟨7436686917079328849194405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9915582556105771798925873 7436686917079328849194405)
                    ·
                      refine ⟨1394378796952374159223951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7436686917079328849194405 1394378796952374159223951)
                      ·
                        rfl

theorem cell23_2715543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 3, 1, 1, 2, 4].length) (baseStart_2715543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2715543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2715543 prefixEnd_2715543 := by exact prefixLift 2715543
  have htrace : WordTrace (prefixWord ++ tailWord_2715543) baseStart_2715543 baseEnd_2715543 := by
    simpa [prefixWord, tailWord_2715543, baseEnd_2715543] using wordTrace_append hprefix tailTrace_2715543
  have hstable : (prefixWord ++ tailWord_2715543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2715543).length < 2 ^ (prefixWord ++ tailWord_2715543).sum := by decide
  have hdescent : baseEnd_2715543 < baseStart_2715543 := by decide
  rcases family_descends (prefixWord ++ tailWord_2715543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2715553 : List Nat := [1, 2, 3, 4, 2, 1, 1, 9]
def baseStart_2715553 : Nat := 118140960795 + 2715553 * 2 ^ 59
def prefixEnd_2715553 : Nat := 4983230072969 + 3 ^ 40 * 2715553 * 2
def baseEnd_2715553 : Nat := 51643849324404411855515

theorem tailTrace_2715553 : CollatzResearch.WordTrace tailWord_2715553 prefixEnd_2715553 51643849324404411855515 := by
  unfold tailWord_2715553
  simp only [CollatzResearch.WordTrace]
  refine ⟨99044354731022735374135313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66029569820681823582756875 99044354731022735374135313)
  ·
    refine ⟨74283266048267051530601485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99044354731022735374135313 74283266048267051530601485)
    ·
      refine ⟨27856224768100144323975557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74283266048267051530601485 27856224768100144323975557)
      ·
        refine ⟨5223042144018777060745417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27856224768100144323975557 5223042144018777060745417)
        ·
          refine ⟨3917281608014082795559063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5223042144018777060745417 3917281608014082795559063)
          ·
            refine ⟨5875922412021124193338595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3917281608014082795559063 5875922412021124193338595)
            ·
              refine ⟨8813883618031686290007893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5875922412021124193338595 8813883618031686290007893)
              ·
                refine ⟨51643849324404411855515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8813883618031686290007893 51643849324404411855515)
                ·
                  rfl

theorem cell23_2715553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 9].length) (baseStart_2715553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2715553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2715553 prefixEnd_2715553 := by exact prefixLift 2715553
  have htrace : WordTrace (prefixWord ++ tailWord_2715553) baseStart_2715553 baseEnd_2715553 := by
    simpa [prefixWord, tailWord_2715553, baseEnd_2715553] using wordTrace_append hprefix tailTrace_2715553
  have hstable : (prefixWord ++ tailWord_2715553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2715553).length < 2 ^ (prefixWord ++ tailWord_2715553).sum := by decide
  have hdescent : baseEnd_2715553 < baseStart_2715553 := by decide
  rcases family_descends (prefixWord ++ tailWord_2715553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2715576 : List Nat := [2, 1, 2, 1, 2, 3, 1, 2, 2, 2, 5]
def baseStart_2715576 : Nat := 118140960795 + 2715576 * 2 ^ 59
def prefixEnd_2715576 : Nat := 4983230072969 + 3 ^ 40 * 2715576 * 2
def baseEnd_2715576 : Nat := 1394395741813972530111299

theorem tailTrace_2715576 : CollatzResearch.WordTrace tailWord_2715576 prefixEnd_2715576 1394395741813972530111299 := by
  unfold tailWord_2715576
  simp only [CollatzResearch.WordTrace]
  refine ⟨49522596804969705151111291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66030129073292940201481721 49522596804969705151111291)
  ·
    refine ⟨74283895207454557726666937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49522596804969705151111291 74283895207454557726666937)
    ·
      refine ⟨55712921405590918295000203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74283895207454557726666937 55712921405590918295000203)
      ·
        refine ⟨83569382108386377442500305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55712921405590918295000203 83569382108386377442500305)
        ·
          refine ⟨62677036581289783081875229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83569382108386377442500305 62677036581289783081875229)
          ·
            refine ⟨23503888717983668655703211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62677036581289783081875229 23503888717983668655703211)
            ·
              refine ⟨35255833076975502983554817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23503888717983668655703211 35255833076975502983554817)
              ·
                refine ⟨26441874807731627237666113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35255833076975502983554817 26441874807731627237666113)
                ·
                  refine ⟨19831406105798720428249585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26441874807731627237666113 19831406105798720428249585)
                  ·
                    refine ⟨14873554579349040321187189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19831406105798720428249585 14873554579349040321187189)
                    ·
                      refine ⟨1394395741813972530111299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14873554579349040321187189 1394395741813972530111299)
                      ·
                        rfl

theorem cell23_2715576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 2, 2, 2, 5].length) (baseStart_2715576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2715576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2715576 prefixEnd_2715576 := by exact prefixLift 2715576
  have htrace : WordTrace (prefixWord ++ tailWord_2715576) baseStart_2715576 baseEnd_2715576 := by
    simpa [prefixWord, tailWord_2715576, baseEnd_2715576] using wordTrace_append hprefix tailTrace_2715576
  have hstable : (prefixWord ++ tailWord_2715576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2715576).length < 2 ^ (prefixWord ++ tailWord_2715576).sum := by decide
  have hdescent : baseEnd_2715576 < baseStart_2715576 := by decide
  rcases family_descends (prefixWord ++ tailWord_2715576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2715581 : List Nat := [1, 4, 1, 2, 3, 2, 3, 2, 1, 2, 2]
def baseStart_2715581 : Nat := 118140960795 + 2715581 * 2 ^ 59
def prefixEnd_2715581 : Nat := 4983230072969 + 3 ^ 40 * 2715581 * 2
def baseEnd_2715581 : Nat := 1394398309217245010548777

theorem tailTrace_2715581 : CollatzResearch.WordTrace tailWord_2715581 prefixEnd_2715581 1394398309217245010548777 := by
  unfold tailWord_2715581
  simp only [CollatzResearch.WordTrace]
  refine ⟨99045375974921296156154597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66030250649947530770769731 99045375974921296156154597)
  ·
    refine ⟨18571007995297743029278987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 99045375974921296156154597 18571007995297743029278987)
    ·
      refine ⟨27856511992946614543918481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18571007995297743029278987 27856511992946614543918481)
      ·
        refine ⟨20892383994709960907938861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27856511992946614543918481 20892383994709960907938861)
        ·
          refine ⟨7834643998016235340477073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20892383994709960907938861 7834643998016235340477073)
          ·
            refine ⟨5875982998512176505357805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7834643998016235340477073 5875982998512176505357805)
            ·
              refine ⟨2203493624442066189509177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5875982998512176505357805 2203493624442066189509177)
              ·
                refine ⟨1652620218331549642131883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2203493624442066189509177 1652620218331549642131883)
                ·
                  refine ⟨2478930327497324463197825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1652620218331549642131883 2478930327497324463197825)
                  ·
                    refine ⟨1859197745622993347398369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2478930327497324463197825 1859197745622993347398369)
                    ·
                      refine ⟨1394398309217245010548777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1859197745622993347398369 1394398309217245010548777)
                      ·
                        rfl

theorem cell23_2715581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 3, 2, 1, 2, 2].length) (baseStart_2715581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2715581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2715581 prefixEnd_2715581 := by exact prefixLift 2715581
  have htrace : WordTrace (prefixWord ++ tailWord_2715581) baseStart_2715581 baseEnd_2715581 := by
    simpa [prefixWord, tailWord_2715581, baseEnd_2715581] using wordTrace_append hprefix tailTrace_2715581
  have hstable : (prefixWord ++ tailWord_2715581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2715581).length < 2 ^ (prefixWord ++ tailWord_2715581).sum := by decide
  have hdescent : baseEnd_2715581 < baseStart_2715581 := by decide
  rcases family_descends (prefixWord ++ tailWord_2715581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2715620 : List Nat := [2, 3, 1, 1, 1, 1, 5, 2, 1, 4, 2]
def baseStart_2715620 : Nat := 118140960795 + 2715620 * 2 ^ 59
def prefixEnd_2715620 : Nat := 4983230072969 + 3 ^ 40 * 2715620 * 2
def baseEnd_2715620 : Nat := 1394418334962770357961097

theorem tailTrace_2715620 : CollatzResearch.WordTrace tailWord_2715620 prefixEnd_2715620 1394418334962770357961097 := by
  unfold tailWord_2715620
  simp only [CollatzResearch.WordTrace]
  refine ⟨49523399210890002908412157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66031198947853337211216209 49523399210890002908412157)
  ·
    refine ⟨18571274704083751090654559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49523399210890002908412157 18571274704083751090654559)
    ·
      refine ⟨27856912056125626635981839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18571274704083751090654559 27856912056125626635981839)
      ·
        refine ⟨41785368084188439953972759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27856912056125626635981839 41785368084188439953972759)
        ·
          refine ⟨62678052126282659930959139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41785368084188439953972759 62678052126282659930959139)
          ·
            refine ⟨94017078189423989896438709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62678052126282659930959139 94017078189423989896438709)
            ·
              refine ⟨8814101080258499052791129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 94017078189423989896438709 8814101080258499052791129)
              ·
                refine ⟨6610575810193874289593347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8814101080258499052791129 6610575810193874289593347)
                ·
                  refine ⟨9915863715290811434390021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6610575810193874289593347 9915863715290811434390021)
                  ·
                    refine ⟨1859224446617027143948129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9915863715290811434390021 1859224446617027143948129)
                    ·
                      refine ⟨1394418334962770357961097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1859224446617027143948129 1394418334962770357961097)
                      ·
                        rfl

theorem cell23_2715620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 2, 1, 4, 2].length) (baseStart_2715620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2715620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2715620 prefixEnd_2715620 := by exact prefixLift 2715620
  have htrace : WordTrace (prefixWord ++ tailWord_2715620) baseStart_2715620 baseEnd_2715620 := by
    simpa [prefixWord, tailWord_2715620, baseEnd_2715620] using wordTrace_append hprefix tailTrace_2715620
  have hstable : (prefixWord ++ tailWord_2715620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2715620).length < 2 ^ (prefixWord ++ tailWord_2715620).sum := by decide
  have hdescent : baseEnd_2715620 < baseStart_2715620 := by decide
  rcases family_descends (prefixWord ++ tailWord_2715620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2715653 : List Nat := [1, 3, 1, 1, 2, 4, 1, 1, 1, 5, 3]
def baseStart_2715653 : Nat := 118140960795 + 2715653 * 2 ^ 59
def prefixEnd_2715653 : Nat := 4983230072969 + 3 ^ 40 * 2715653 * 2
def baseEnd_2715653 : Nat := 1394435279824368728848445

theorem tailTrace_2715653 : CollatzResearch.WordTrace tailWord_2715653 prefixEnd_2715653 1394435279824368728848445 := by
  unfold tailWord_2715653
  simp only [CollatzResearch.WordTrace]
  refine ⟨99048002030660452452775613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66032001353773634968517075 99048002030660452452775613)
  ·
    refine ⟨37143000761497669669790855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99048002030660452452775613 37143000761497669669790855)
    ·
      refine ⟨55714501142246504504686283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37143000761497669669790855 55714501142246504504686283)
      ·
        refine ⟨83571751713369756757029425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55714501142246504504686283 83571751713369756757029425)
        ·
          refine ⟨62678813785027317567772069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83571751713369756757029425 62678813785027317567772069)
          ·
            refine ⟨11752277584692622043957263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62678813785027317567772069 11752277584692622043957263)
            ·
              refine ⟨17628416377038933065935895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11752277584692622043957263 17628416377038933065935895)
              ·
                refine ⟨26442624565558399598903843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17628416377038933065935895 26442624565558399598903843)
                ·
                  refine ⟨39663936848337599398355765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26442624565558399598903843 39663936848337599398355765)
                  ·
                    refine ⟨3718494079531649943595853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39663936848337599398355765 3718494079531649943595853)
                    ·
                      refine ⟨1394435279824368728848445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3718494079531649943595853 1394435279824368728848445)
                      ·
                        rfl

theorem cell23_2715653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 1, 1, 5, 3].length) (baseStart_2715653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2715653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2715653 prefixEnd_2715653 := by exact prefixLift 2715653
  have htrace : WordTrace (prefixWord ++ tailWord_2715653) baseStart_2715653 baseEnd_2715653 := by
    simpa [prefixWord, tailWord_2715653, baseEnd_2715653] using wordTrace_append hprefix tailTrace_2715653
  have hstable : (prefixWord ++ tailWord_2715653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2715653).length < 2 ^ (prefixWord ++ tailWord_2715653).sum := by decide
  have hdescent : baseEnd_2715653 < baseStart_2715653 := by decide
  rcases family_descends (prefixWord ++ tailWord_2715653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2715677 : List Nat := [1, 4, 2, 2, 2, 2, 2, 3, 5]
def baseStart_2715677 : Nat := 118140960795 + 2715677 * 2 ^ 59
def prefixEnd_2715677 : Nat := 4983230072969 + 3 ^ 40 * 2715677 * 2
def baseEnd_2715677 : Nat := 154938622595564070549815

theorem tailTrace_2715677 : CollatzResearch.WordTrace tailWord_2715677 prefixEnd_2715677 154938622595564070549815 := by
  unfold tailWord_2715677
  simp only [CollatzResearch.WordTrace]
  refine ⟨99048877382573504551649285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66032584921715669701099523 99048877382573504551649285)
  ·
    refine ⟨18571664509232532103434241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 99048877382573504551649285 18571664509232532103434241)
    ·
      refine ⟨13928748381924399077575681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18571664509232532103434241 13928748381924399077575681)
      ·
        refine ⟨10446561286443299308181761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13928748381924399077575681 10446561286443299308181761)
        ·
          refine ⟨7834920964832474481136321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10446561286443299308181761 7834920964832474481136321)
          ·
            refine ⟨5876190723624355860852241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7834920964832474481136321 5876190723624355860852241)
            ·
              refine ⟨4407143042718266895639181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5876190723624355860852241 4407143042718266895639181)
              ·
                refine ⟨1652678641019350085864693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4407143042718266895639181 1652678641019350085864693)
                ·
                  refine ⟨154938622595564070549815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1652678641019350085864693 154938622595564070549815)
                  ·
                    rfl

theorem cell23_2715677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 2, 3, 5].length) (baseStart_2715677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2715677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2715677 prefixEnd_2715677 := by exact prefixLift 2715677
  have htrace : WordTrace (prefixWord ++ tailWord_2715677) baseStart_2715677 baseEnd_2715677 := by
    simpa [prefixWord, tailWord_2715677, baseEnd_2715677] using wordTrace_append hprefix tailTrace_2715677
  have hstable : (prefixWord ++ tailWord_2715677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2715677).length < 2 ^ (prefixWord ++ tailWord_2715677).sum := by decide
  have hdescent : baseEnd_2715677 < baseStart_2715677 := by decide
  rcases family_descends (prefixWord ++ tailWord_2715677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2715688 : List Nat := [2, 1, 5, 3, 1, 2, 1, 2, 2, 2, 2]
def baseStart_2715688 : Nat := 118140960795 + 2715688 * 2 ^ 59
def prefixEnd_2715688 : Nat := 4983230072969 + 3 ^ 40 * 2715688 * 2
def baseEnd_2715688 : Nat := 1394453251647276091910785

theorem tailTrace_2715688 : CollatzResearch.WordTrace tailWord_2715688 prefixEnd_2715688 1394453251647276091910785 := by
  unfold tailWord_2715688
  simp only [CollatzResearch.WordTrace]
  refine ⟨49524639292766826715149859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66032852390355768953533145 49524639292766826715149859)
  ·
    refine ⟨74286958939150240072724789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49524639292766826715149859 74286958939150240072724789)
    ·
      refine ⟨6964402400545335006817949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 74286958939150240072724789 6964402400545335006817949)
      ·
        refine ⟨2611650900204500627556731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6964402400545335006817949 2611650900204500627556731)
        ·
          refine ⟨3917476350306750941335097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2611650900204500627556731 3917476350306750941335097)
          ·
            refine ⟨2938107262730063206001323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3917476350306750941335097 2938107262730063206001323)
            ·
              refine ⟨4407160894095094809001985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2938107262730063206001323 4407160894095094809001985)
              ·
                refine ⟨3305370670571321106751489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4407160894095094809001985 3305370670571321106751489)
                ·
                  refine ⟨2479028002928490830063617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3305370670571321106751489 2479028002928490830063617)
                  ·
                    refine ⟨1859271002196368122547713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2479028002928490830063617 1859271002196368122547713)
                    ·
                      refine ⟨1394453251647276091910785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1859271002196368122547713 1394453251647276091910785)
                      ·
                        rfl

theorem cell23_2715688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 1, 2, 2, 2, 2].length) (baseStart_2715688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2715688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2715688 prefixEnd_2715688 := by exact prefixLift 2715688
  have htrace : WordTrace (prefixWord ++ tailWord_2715688) baseStart_2715688 baseEnd_2715688 := by
    simpa [prefixWord, tailWord_2715688, baseEnd_2715688] using wordTrace_append hprefix tailTrace_2715688
  have hstable : (prefixWord ++ tailWord_2715688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2715688).length < 2 ^ (prefixWord ++ tailWord_2715688).sum := by decide
  have hdescent : baseEnd_2715688 < baseStart_2715688 := by decide
  rcases family_descends (prefixWord ++ tailWord_2715688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
