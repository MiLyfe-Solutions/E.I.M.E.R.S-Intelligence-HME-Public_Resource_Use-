import V185TrunkScan23Chunk0854

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5059767 : List Nat := [1, 1, 3, 1, 4, 1, 2, 3, 2, 1, 4]
def baseStart_5059767 : Nat := 118140960795 + 5059767 * 2 ^ 59
def prefixEnd_5059767 : Nat := 4983230072969 + 3 ^ 40 * 5059767 * 2
def baseEnd_5059767 : Nat := 2598092470757810372043061

theorem tailTrace_5059767 : CollatzResearch.WordTrace tailWord_5059767 prefixEnd_5059767 2598092470757810372043061 := by
  unfold tailWord_5059767
  simp only [CollatzResearch.WordTrace]
  refine ⟨184544863460335773251057555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123029908973557182167371703 184544863460335773251057555)
  ·
    refine ⟨276817295190503659876586333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184544863460335773251057555 276817295190503659876586333)
    ·
      refine ⟨103806485696438872453719875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 276817295190503659876586333 103806485696438872453719875)
      ·
        refine ⟨155709728544658308680579813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103806485696438872453719875 155709728544658308680579813)
        ·
          refine ⟨29195574102123432877608715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 155709728544658308680579813 29195574102123432877608715)
          ·
            refine ⟨43793361153185149316413073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29195574102123432877608715 43793361153185149316413073)
            ·
              refine ⟨32845020864888861987309805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43793361153185149316413073 32845020864888861987309805)
              ·
                refine ⟨12316882824333323245241177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32845020864888861987309805 12316882824333323245241177)
                ·
                  refine ⟨9237662118249992433930883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12316882824333323245241177 9237662118249992433930883)
                  ·
                    refine ⟨13856493177374988650896325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9237662118249992433930883 13856493177374988650896325)
                    ·
                      refine ⟨2598092470757810372043061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13856493177374988650896325 2598092470757810372043061)
                      ·
                        rfl

theorem cell23_5059767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 3, 2, 1, 4].length) (baseStart_5059767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5059767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5059767 prefixEnd_5059767 := by exact prefixLift 5059767
  have htrace : WordTrace (prefixWord ++ tailWord_5059767) baseStart_5059767 baseEnd_5059767 := by
    simpa [prefixWord, tailWord_5059767, baseEnd_5059767] using wordTrace_append hprefix tailTrace_5059767
  have hstable : (prefixWord ++ tailWord_5059767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5059767).length < 2 ^ (prefixWord ++ tailWord_5059767).sum := by decide
  have hdescent : baseEnd_5059767 < baseStart_5059767 := by decide
  rcases family_descends (prefixWord ++ tailWord_5059767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5059770 : List Nat := [3, 1, 1, 1, 2, 2, 1, 2, 2, 3, 5]
def baseStart_5059770 : Nat := 118140960795 + 5059770 * 2 ^ 59
def prefixEnd_5059770 : Nat := 4983230072969 + 3 ^ 40 * 5059770 * 2
def baseEnd_5059770 : Nat := 2598094011199773860305547

theorem tailTrace_5059770 : CollatzResearch.WordTrace tailWord_5059770 prefixEnd_5059770 2598094011199773860305547 := by
  unfold tailWord_5059770
  simp only [CollatzResearch.WordTrace]
  refine ⟨46136243219831226190854191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123029981919549936508944509 46136243219831226190854191)
  ·
    refine ⟨69204364829746839286281287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46136243219831226190854191 69204364829746839286281287)
    ·
      refine ⟨103806547244620258929421931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69204364829746839286281287 103806547244620258929421931)
      ·
        refine ⟨155709820866930388394132897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103806547244620258929421931 155709820866930388394132897)
        ·
          refine ⟨116782365650197791295599673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 155709820866930388394132897 116782365650197791295599673)
          ·
            refine ⟨87586774237648343471699755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 116782365650197791295599673 87586774237648343471699755)
            ·
              refine ⟨131380161356472515207549633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87586774237648343471699755 131380161356472515207549633)
              ·
                refine ⟨98535121017354386405662225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 131380161356472515207549633 98535121017354386405662225)
                ·
                  refine ⟨73901340763015789804246669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 98535121017354386405662225 73901340763015789804246669)
                  ·
                    refine ⟨27713002786130921176592501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 73901340763015789804246669 27713002786130921176592501)
                    ·
                      refine ⟨2598094011199773860305547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27713002786130921176592501 2598094011199773860305547)
                      ·
                        rfl

theorem cell23_5059770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 2, 2, 3, 5].length) (baseStart_5059770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5059770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5059770 prefixEnd_5059770 := by exact prefixLift 5059770
  have htrace : WordTrace (prefixWord ++ tailWord_5059770) baseStart_5059770 baseEnd_5059770 := by
    simpa [prefixWord, tailWord_5059770, baseEnd_5059770] using wordTrace_append hprefix tailTrace_5059770
  have hstable : (prefixWord ++ tailWord_5059770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5059770).length < 2 ^ (prefixWord ++ tailWord_5059770).sum := by decide
  have hdescent : baseEnd_5059770 < baseStart_5059770 := by decide
  rcases family_descends (prefixWord ++ tailWord_5059770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5059821 : List Nat := [1, 5, 1, 2, 2, 2, 2, 1, 2, 2, 3]
def baseStart_5059821 : Nat := 118140960795 + 5059821 * 2 ^ 59
def prefixEnd_5059821 : Nat := 4983230072969 + 3 ^ 40 * 5059821 * 2
def baseEnd_5059821 : Nat := 2598120198713153160767813

theorem tailTrace_5059821 : CollatzResearch.WordTrace tailWord_5059821 prefixEnd_5059821 2598120198713153160767813 := by
  unfold tailWord_5059821
  simp only [CollatzResearch.WordTrace]
  refine ⟨184546833002140140473523317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123031222001426760315682211 184546833002140140473523317)
  ·
    refine ⟨17301265593950638169392811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 184546833002140140473523317 17301265593950638169392811)
    ·
      refine ⟨25951898390925957254089217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17301265593950638169392811 25951898390925957254089217)
      ·
        refine ⟨19463923793194467940566913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25951898390925957254089217 19463923793194467940566913)
        ·
          refine ⟨14597942844895850955425185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19463923793194467940566913 14597942844895850955425185)
          ·
            refine ⟨10948457133671888216568889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14597942844895850955425185 10948457133671888216568889)
            ·
              refine ⟨8211342850253916162426667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10948457133671888216568889 8211342850253916162426667)
              ·
                refine ⟨12317014275380874243640001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8211342850253916162426667 12317014275380874243640001)
                ·
                  refine ⟨9237760706535655682730001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12317014275380874243640001 9237760706535655682730001)
                  ·
                    refine ⟨6928320529901741762047501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9237760706535655682730001 6928320529901741762047501)
                    ·
                      refine ⟨2598120198713153160767813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6928320529901741762047501 2598120198713153160767813)
                      ·
                        rfl

theorem cell23_5059821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 2, 1, 2, 2, 3].length) (baseStart_5059821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5059821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5059821 prefixEnd_5059821 := by exact prefixLift 5059821
  have htrace : WordTrace (prefixWord ++ tailWord_5059821) baseStart_5059821 baseEnd_5059821 := by
    simpa [prefixWord, tailWord_5059821, baseEnd_5059821] using wordTrace_append hprefix tailTrace_5059821
  have hstable : (prefixWord ++ tailWord_5059821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5059821).length < 2 ^ (prefixWord ++ tailWord_5059821).sum := by decide
  have hdescent : baseEnd_5059821 < baseStart_5059821 := by decide
  rcases family_descends (prefixWord ++ tailWord_5059821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5059857 : List Nat := [1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 4]
def baseStart_5059857 : Nat := 118140960795 + 5059857 * 2 ^ 59
def prefixEnd_5059857 : Nat := 4983230072969 + 3 ^ 40 * 5059857 * 2
def baseEnd_5059857 : Nat := 2598138684016715019917647

theorem tailTrace_5059857 : CollatzResearch.WordTrace tailWord_5059857 prefixEnd_5059857 2598138684016715019917647 := by
  unfold tailWord_5059857
  simp only [CollatzResearch.WordTrace]
  refine ⟨184548146030009718621833825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123032097353339812414555883 184548146030009718621833825)
  ·
    refine ⟨138411109522507288966375369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184548146030009718621833825 138411109522507288966375369)
    ·
      refine ⟨103808332141880466724781527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138411109522507288966375369 103808332141880466724781527)
      ·
        refine ⟨155712498212820700087172291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103808332141880466724781527 155712498212820700087172291)
        ·
          refine ⟨233568747319231050130758437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155712498212820700087172291 233568747319231050130758437)
          ·
            refine ⟨43794140122355821899517207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 233568747319231050130758437 43794140122355821899517207)
            ·
              refine ⟨65691210183533732849275811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43794140122355821899517207 65691210183533732849275811)
              ·
                refine ⟨98536815275300599273913717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65691210183533732849275811 98536815275300599273913717)
                ·
                  refine ⟨9237826432059431181929411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 98536815275300599273913717 9237826432059431181929411)
                  ·
                    refine ⟨13856739648089146772894117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9237826432059431181929411 13856739648089146772894117)
                    ·
                      refine ⟨2598138684016715019917647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13856739648089146772894117 2598138684016715019917647)
                      ·
                        rfl

theorem cell23_5059857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 4].length) (baseStart_5059857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5059857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5059857 prefixEnd_5059857 := by exact prefixLift 5059857
  have htrace : WordTrace (prefixWord ++ tailWord_5059857) baseStart_5059857 baseEnd_5059857 := by
    simpa [prefixWord, tailWord_5059857, baseEnd_5059857] using wordTrace_append hprefix tailTrace_5059857
  have hstable : (prefixWord ++ tailWord_5059857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5059857).length < 2 ^ (prefixWord ++ tailWord_5059857).sum := by decide
  have hdescent : baseEnd_5059857 < baseStart_5059857 := by decide
  rcases family_descends (prefixWord ++ tailWord_5059857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5059867 : List Nat := [1, 1, 1, 1, 1, 1, 5, 2, 6, 4]
def baseStart_5059867 : Nat := 118140960795 + 5059867 * 2 ^ 59
def prefixEnd_5059867 : Nat := 4983230072969 + 3 ^ 40 * 5059867 * 2
def baseEnd_5059867 : Nat := 866047939607753326930867

theorem tailTrace_5059867 : CollatzResearch.WordTrace tailWord_5059867 prefixEnd_5059867 866047939607753326930867 := by
  unfold tailWord_5059867
  simp only [CollatzResearch.WordTrace]
  refine ⟨184548510759973490329697855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123032340506648993553131903 184548510759973490329697855)
  ·
    refine ⟨276822766139960235494546783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184548510759973490329697855 276822766139960235494546783)
    ·
      refine ⟨415234149209940353241820175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 276822766139960235494546783 415234149209940353241820175)
      ·
        refine ⟨622851223814910529862730263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 415234149209940353241820175 622851223814910529862730263)
        ·
          refine ⟨934276835722365794794095395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 622851223814910529862730263 934276835722365794794095395)
          ·
            refine ⟨1401415253583548692191143093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 934276835722365794794095395 1401415253583548692191143093)
            ·
              refine ⟨131382680023457689892919665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1401415253583548692191143093 131382680023457689892919665)
              ·
                refine ⟨98537010017593267419689749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 131382680023457689892919665 98537010017593267419689749)
                ·
                  refine ⟨4618922344574684410297957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 98537010017593267419689749 4618922344574684410297957)
                  ·
                    refine ⟨866047939607753326930867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4618922344574684410297957 866047939607753326930867)
                    ·
                      rfl

theorem cell23_5059867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 2, 6, 4].length) (baseStart_5059867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5059867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5059867 prefixEnd_5059867 := by exact prefixLift 5059867
  have htrace : WordTrace (prefixWord ++ tailWord_5059867) baseStart_5059867 baseEnd_5059867 := by
    simpa [prefixWord, tailWord_5059867, baseEnd_5059867] using wordTrace_append hprefix tailTrace_5059867
  have hstable : (prefixWord ++ tailWord_5059867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5059867).length < 2 ^ (prefixWord ++ tailWord_5059867).sum := by decide
  have hdescent : baseEnd_5059867 < baseStart_5059867 := by decide
  rcases family_descends (prefixWord ++ tailWord_5059867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5059885 : List Nat := [1, 5, 3, 1, 1, 1, 1, 5, 1, 1, 3]
def baseStart_5059885 : Nat := 118140960795 + 5059885 * 2 ^ 59
def prefixEnd_5059885 : Nat := 4983230072969 + 3 ^ 40 * 5059885 * 2
def baseEnd_5059885 : Nat := 2598153061475040910367519

theorem tailTrace_5059885 : CollatzResearch.WordTrace tailWord_5059885 prefixEnd_5059885 2598153061475040910367519 := by
  unfold tailWord_5059885
  simp only [CollatzResearch.WordTrace]
  refine ⟨184549167273908279403853109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123032778182605519602568739 184549167273908279403853109)
  ·
    refine ⟨17301484431928901194111229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 184549167273908279403853109 17301484431928901194111229)
    ·
      refine ⟨6488056661973337947791711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17301484431928901194111229 6488056661973337947791711)
      ·
        refine ⟨9732084992960006921687567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6488056661973337947791711 9732084992960006921687567)
        ·
          refine ⟨14598127489440010382531351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9732084992960006921687567 14598127489440010382531351)
          ·
            refine ⟨21897191234160015573797027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14598127489440010382531351 21897191234160015573797027)
            ·
              refine ⟨32845786851240023360695541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21897191234160015573797027 32845786851240023360695541)
              ·
                refine ⟨3079292517303752190065207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32845786851240023360695541 3079292517303752190065207)
                ·
                  refine ⟨4618938775955628285097811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3079292517303752190065207 4618938775955628285097811)
                  ·
                    refine ⟨6928408163933442427646717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4618938775955628285097811 6928408163933442427646717)
                    ·
                      refine ⟨2598153061475040910367519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6928408163933442427646717 2598153061475040910367519)
                      ·
                        rfl

theorem cell23_5059885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 5, 1, 1, 3].length) (baseStart_5059885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5059885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5059885 prefixEnd_5059885 := by exact prefixLift 5059885
  have htrace : WordTrace (prefixWord ++ tailWord_5059885) baseStart_5059885 baseEnd_5059885 := by
    simpa [prefixWord, tailWord_5059885, baseEnd_5059885] using wordTrace_append hprefix tailTrace_5059885
  have hstable : (prefixWord ++ tailWord_5059885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5059885).length < 2 ^ (prefixWord ++ tailWord_5059885).sum := by decide
  have hdescent : baseEnd_5059885 < baseStart_5059885 := by decide
  rcases family_descends (prefixWord ++ tailWord_5059885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5059891 : List Nat := [1, 1, 1, 2, 5, 2, 4, 1, 1, 1, 4]
def baseStart_5059891 : Nat := 118140960795 + 5059891 * 2 ^ 59
def prefixEnd_5059891 : Nat := 4983230072969 + 3 ^ 40 * 5059891 * 2
def baseEnd_5059891 : Nat := 2598156142358967886892491

theorem tailTrace_5059891 : CollatzResearch.WordTrace tailWord_5059891 prefixEnd_5059891 2598156142358967886892491 := by
  unfold tailWord_5059891
  simp only [CollatzResearch.WordTrace]
  refine ⟨184549386111886542428571527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123032924074591028285714351 184549386111886542428571527)
  ·
    refine ⟨276824079167829813642857291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184549386111886542428571527 276824079167829813642857291)
    ·
      refine ⟨415236118751744720464285937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 276824079167829813642857291 415236118751744720464285937)
      ·
        refine ⟨311427089063808540348214453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 415236118751744720464285937 311427089063808540348214453)
        ·
          refine ⟨29196289599732050657645105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 311427089063808540348214453 29196289599732050657645105)
          ·
            refine ⟨21897217199799037993233829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29196289599732050657645105 21897217199799037993233829)
            ·
              refine ⟨4105728224962319623731343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21897217199799037993233829 4105728224962319623731343)
              ·
                refine ⟨6158592337443479435597015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4105728224962319623731343 6158592337443479435597015)
                ·
                  refine ⟨9237888506165219153395523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6158592337443479435597015 9237888506165219153395523)
                  ·
                    refine ⟨13856832759247828730093285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9237888506165219153395523 13856832759247828730093285)
                    ·
                      refine ⟨2598156142358967886892491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13856832759247828730093285 2598156142358967886892491)
                      ·
                        rfl

theorem cell23_5059891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 4, 1, 1, 1, 4].length) (baseStart_5059891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5059891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5059891 prefixEnd_5059891 := by exact prefixLift 5059891
  have htrace : WordTrace (prefixWord ++ tailWord_5059891) baseStart_5059891 baseEnd_5059891 := by
    simpa [prefixWord, tailWord_5059891, baseEnd_5059891] using wordTrace_append hprefix tailTrace_5059891
  have hstable : (prefixWord ++ tailWord_5059891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5059891).length < 2 ^ (prefixWord ++ tailWord_5059891).sum := by decide
  have hdescent : baseEnd_5059891 < baseStart_5059891 := by decide
  rcases family_descends (prefixWord ++ tailWord_5059891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5059951 : List Nat := [1, 1, 2, 1, 3, 1, 3, 5, 1, 3, 2]
def baseStart_5059951 : Nat := 118140960795 + 5059951 * 2 ^ 59
def prefixEnd_5059951 : Nat := 4983230072969 + 3 ^ 40 * 5059951 * 2
def baseEnd_5059951 : Nat := 2598186951198237652142215

theorem tailTrace_5059951 : CollatzResearch.WordTrace tailWord_5059951 prefixEnd_5059951 2598186951198237652142215 := by
  unfold tailWord_5059951
  simp only [CollatzResearch.WordTrace]
  refine ⟨184551574491669172675755707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123034382994446115117170471 184551574491669172675755707)
  ·
    refine ⟨276827361737503759013633561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184551574491669172675755707 276827361737503759013633561)
    ·
      refine ⟨207620521303127819260225171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 276827361737503759013633561 207620521303127819260225171)
      ·
        refine ⟨311430781954691728890337757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 207620521303127819260225171 311430781954691728890337757)
        ·
          refine ⟨116786543233009398333876659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 311430781954691728890337757 116786543233009398333876659)
          ·
            refine ⟨175179814849514097500814989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116786543233009398333876659 175179814849514097500814989)
            ·
              refine ⟨65692430568567786562805621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 175179814849514097500814989 65692430568567786562805621)
              ·
                refine ⟨6158665365803229990263027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 65692430568567786562805621 6158665365803229990263027)
                ·
                  refine ⟨9237998048704844985394541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6158665365803229990263027 9237998048704844985394541)
                  ·
                    refine ⟨3464249268264316869522953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9237998048704844985394541 3464249268264316869522953)
                    ·
                      refine ⟨2598186951198237652142215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3464249268264316869522953 2598186951198237652142215)
                      ·
                        rfl

theorem cell23_5059951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 5, 1, 3, 2].length) (baseStart_5059951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5059951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5059951 prefixEnd_5059951 := by exact prefixLift 5059951
  have htrace : WordTrace (prefixWord ++ tailWord_5059951) baseStart_5059951 baseEnd_5059951 := by
    simpa [prefixWord, tailWord_5059951, baseEnd_5059951] using wordTrace_append hprefix tailTrace_5059951
  have hstable : (prefixWord ++ tailWord_5059951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5059951).length < 2 ^ (prefixWord ++ tailWord_5059951).sum := by decide
  have hdescent : baseEnd_5059951 < baseStart_5059951 := by decide
  rcases family_descends (prefixWord ++ tailWord_5059951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5059967 : List Nat := [1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 5]
def baseStart_5059967 : Nat := 118140960795 + 5059967 * 2 ^ 59
def prefixEnd_5059967 : Nat := 4983230072969 + 3 ^ 40 * 5059967 * 2
def baseEnd_5059967 : Nat := 2598195166888709589542141

theorem tailTrace_5059967 : CollatzResearch.WordTrace tailWord_5059967 prefixEnd_5059967 2598195166888709589542141 := by
  unfold tailWord_5059967
  simp only [CollatzResearch.WordTrace]
  refine ⟨184552158059611207408338155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123034772039740804938892103 184552158059611207408338155)
  ·
    refine ⟨276828237089416811112507233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184552158059611207408338155 276828237089416811112507233)
    ·
      refine ⟨207621177817062608334380425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 276828237089416811112507233 207621177817062608334380425)
      ·
        refine ⟨155715883362796956250785319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 207621177817062608334380425 155715883362796956250785319)
        ·
          refine ⟨233573825044195434376177979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155715883362796956250785319 233573825044195434376177979)
          ·
            refine ⟨350360737566293151564266969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 233573825044195434376177979 350360737566293151564266969)
            ·
              refine ⟨262770553174719863673200227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 350360737566293151564266969 262770553174719863673200227)
              ·
                refine ⟨394155829762079795509800341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 262770553174719863673200227 394155829762079795509800341)
                ·
                  refine ⟨18476054520097490414521891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 394155829762079795509800341 18476054520097490414521891)
                  ·
                    refine ⟨27714081780146235621782837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18476054520097490414521891 27714081780146235621782837)
                    ·
                      refine ⟨2598195166888709589542141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27714081780146235621782837 2598195166888709589542141)
                      ·
                        rfl

theorem cell23_5059967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 5].length) (baseStart_5059967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5059967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5059967 prefixEnd_5059967 := by exact prefixLift 5059967
  have htrace : WordTrace (prefixWord ++ tailWord_5059967) baseStart_5059967 baseEnd_5059967 := by
    simpa [prefixWord, tailWord_5059967, baseEnd_5059967] using wordTrace_append hprefix tailTrace_5059967
  have hstable : (prefixWord ++ tailWord_5059967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5059967).length < 2 ^ (prefixWord ++ tailWord_5059967).sum := by decide
  have hdescent : baseEnd_5059967 < baseStart_5059967 := by decide
  rcases family_descends (prefixWord ++ tailWord_5059967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5059975 : List Nat := [1, 1, 4, 2, 2, 4, 2, 1, 2, 1, 3]
def baseStart_5059975 : Nat := 118140960795 + 5059975 * 2 ^ 59
def prefixEnd_5059975 : Nat := 4983230072969 + 3 ^ 40 * 5059975 * 2
def baseEnd_5059975 : Nat := 2598199274733945558242105

theorem tailTrace_5059975 : CollatzResearch.WordTrace tailWord_5059975 prefixEnd_5059975 2598199274733945558242105 := by
  unfold tailWord_5059975
  simp only [CollatzResearch.WordTrace]
  refine ⟨184552449843582224774629379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123034966562388149849752919 184552449843582224774629379)
  ·
    refine ⟨276828674765373337161944069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184552449843582224774629379 276828674765373337161944069)
    ·
      refine ⟨51905376518507500717864513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 276828674765373337161944069 51905376518507500717864513)
      ·
        refine ⟨38929032388880625538398385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51905376518507500717864513 38929032388880625538398385)
        ·
          refine ⟨29196774291660469153798789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38929032388880625538398385 29196774291660469153798789)
          ·
            refine ⟨5474395179686337966337273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29196774291660469153798789 5474395179686337966337273)
            ·
              refine ⟨4105796384764753474752955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5474395179686337966337273 4105796384764753474752955)
              ·
                refine ⟨6158694577147130212129433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4105796384764753474752955 6158694577147130212129433)
                ·
                  refine ⟨4619020932860347659097075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6158694577147130212129433 4619020932860347659097075)
                  ·
                    refine ⟨6928531399290521488645613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4619020932860347659097075 6928531399290521488645613)
                    ·
                      refine ⟨2598199274733945558242105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6928531399290521488645613 2598199274733945558242105)
                      ·
                        rfl

theorem cell23_5059975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 2, 1, 2, 1, 3].length) (baseStart_5059975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5059975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5059975 prefixEnd_5059975 := by exact prefixLift 5059975
  have htrace : WordTrace (prefixWord ++ tailWord_5059975) baseStart_5059975 baseEnd_5059975 := by
    simpa [prefixWord, tailWord_5059975, baseEnd_5059975] using wordTrace_append hprefix tailTrace_5059975
  have hstable : (prefixWord ++ tailWord_5059975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5059975).length < 2 ^ (prefixWord ++ tailWord_5059975).sum := by decide
  have hdescent : baseEnd_5059975 < baseStart_5059975 := by decide
  rcases family_descends (prefixWord ++ tailWord_5059975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5060081 : List Nat := [1, 2, 2, 2, 3, 2, 1, 3, 3, 4]
def baseStart_5060081 : Nat := 118140960795 + 5060081 * 2 ^ 59
def prefixEnd_5060081 : Nat := 4983230072969 + 3 ^ 40 * 5060081 * 2
def baseEnd_5060081 : Nat := 866084567894440714505539

theorem tailTrace_5060081 : CollatzResearch.WordTrace tailWord_5060081 prefixEnd_5060081 866084567894440714505539 := by
  unfold tailWord_5060081
  simp only [CollatzResearch.WordTrace]
  refine ⟨184556315981198204877988097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123037543987465469918658731 184556315981198204877988097)
  ·
    refine ⟨138417236985898653658491073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184556315981198204877988097 138417236985898653658491073)
    ·
      refine ⟨103812927739423990243868305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138417236985898653658491073 103812927739423990243868305)
      ·
        refine ⟨77859695804567992682901229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103812927739423990243868305 77859695804567992682901229)
        ·
          refine ⟨29197385926712997256087961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77859695804567992682901229 29197385926712997256087961)
          ·
            refine ⟨21898039445034747942065971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29197385926712997256087961 21898039445034747942065971)
            ·
              refine ⟨32847059167552121913098957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21898039445034747942065971 32847059167552121913098957)
              ·
                refine ⟨12317647187832045717412109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32847059167552121913098957 12317647187832045717412109)
                ·
                  refine ⟨4619117695437017144029541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12317647187832045717412109 4619117695437017144029541)
                  ·
                    refine ⟨866084567894440714505539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4619117695437017144029541 866084567894440714505539)
                    ·
                      rfl

theorem cell23_5060081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 3, 3, 4].length) (baseStart_5060081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5060081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5060081 prefixEnd_5060081 := by exact prefixLift 5060081
  have htrace : WordTrace (prefixWord ++ tailWord_5060081) baseStart_5060081 baseEnd_5060081 := by
    simpa [prefixWord, tailWord_5060081, baseEnd_5060081] using wordTrace_append hprefix tailTrace_5060081
  have hstable : (prefixWord ++ tailWord_5060081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5060081).length < 2 ^ (prefixWord ++ tailWord_5060081).sum := by decide
  have hdescent : baseEnd_5060081 < baseStart_5060081 := by decide
  rcases family_descends (prefixWord ++ tailWord_5060081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5060115 : List Nat := [1, 1, 1, 2, 1, 8, 1, 3, 1, 4]
def baseStart_5060115 : Nat := 118140960795 + 5060115 * 2 ^ 59
def prefixEnd_5060115 : Nat := 4983230072969 + 3 ^ 40 * 5060115 * 2
def baseEnd_5060115 : Nat := 866090387341858336830487

theorem tailTrace_5060115 : CollatzResearch.WordTrace tailWord_5060115 prefixEnd_5060115 866090387341858336830487 := by
  unfold tailWord_5060115
  simp only [CollatzResearch.WordTrace]
  refine ⟨184557556063075028684725799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123038370708716685789817199 184557556063075028684725799)
  ·
    refine ⟨276836334094612543027088699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184557556063075028684725799 276836334094612543027088699)
    ·
      refine ⟨415254501141918814540633049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 276836334094612543027088699 415254501141918814540633049)
      ·
        refine ⟨311440875856439110905474787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 415254501141918814540633049 311440875856439110905474787)
        ·
          refine ⟨467161313784658666358212181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 311440875856439110905474787 467161313784658666358212181)
          ·
            refine ⟨5474546645913968746385299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 467161313784658666358212181 5474546645913968746385299)
            ·
              refine ⟨8211819968870953119577949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5474546645913968746385299 8211819968870953119577949)
              ·
                refine ⟨3079432488326607419841731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8211819968870953119577949 3079432488326607419841731)
                ·
                  refine ⟨4619148732489911129762597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3079432488326607419841731 4619148732489911129762597)
                  ·
                    refine ⟨866090387341858336830487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4619148732489911129762597 866090387341858336830487)
                    ·
                      rfl

theorem cell23_5060115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 1, 3, 1, 4].length) (baseStart_5060115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5060115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5060115 prefixEnd_5060115 := by exact prefixLift 5060115
  have htrace : WordTrace (prefixWord ++ tailWord_5060115) baseStart_5060115 baseEnd_5060115 := by
    simpa [prefixWord, tailWord_5060115, baseEnd_5060115] using wordTrace_append hprefix tailTrace_5060115
  have hstable : (prefixWord ++ tailWord_5060115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5060115).length < 2 ^ (prefixWord ++ tailWord_5060115).sum := by decide
  have hdescent : baseEnd_5060115 < baseStart_5060115 := by decide
  rcases family_descends (prefixWord ++ tailWord_5060115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5060144 : List Nat := [2, 1, 1, 1, 2, 3, 1, 1, 2, 5, 4]
def baseStart_5060144 : Nat := 118140960795 + 5060144 * 2 ^ 59
def prefixEnd_5060144 : Nat := 4983230072969 + 3 ^ 40 * 5060144 * 2
def baseEnd_5060144 : Nat := 2598286052964555397028827

theorem tailTrace_5060144 : CollatzResearch.WordTrace tailWord_5060144 prefixEnd_5060144 2598286052964555397028827 := by
  unfold tailWord_5060144
  simp only [CollatzResearch.WordTrace]
  refine ⟨92279306889984983318765743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123039075853313311091687657 92279306889984983318765743)
  ·
    refine ⟨138418960334977474978148615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92279306889984983318765743 138418960334977474978148615)
    ·
      refine ⟨207628440502466212467222923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138418960334977474978148615 207628440502466212467222923)
      ·
        refine ⟨311442660753699318700834385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 207628440502466212467222923 311442660753699318700834385)
        ·
          refine ⟨233581995565274489025625789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 311442660753699318700834385 233581995565274489025625789)
          ·
            refine ⟨87593248336977933384609671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 233581995565274489025625789 87593248336977933384609671)
            ·
              refine ⟨131389872505466900076914507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87593248336977933384609671 131389872505466900076914507)
              ·
                refine ⟨197084808758200350115371761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 131389872505466900076914507 197084808758200350115371761)
                ·
                  refine ⟨147813606568650262586528821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 197084808758200350115371761 147813606568650262586528821)
                  ·
                    refine ⟨13857525615810962117487077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 147813606568650262586528821 13857525615810962117487077)
                    ·
                      refine ⟨2598286052964555397028827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13857525615810962117487077 2598286052964555397028827)
                      ·
                        rfl

theorem cell23_5060144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 2, 5, 4].length) (baseStart_5060144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5060144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5060144 prefixEnd_5060144 := by exact prefixLift 5060144
  have htrace : WordTrace (prefixWord ++ tailWord_5060144) baseStart_5060144 baseEnd_5060144 := by
    simpa [prefixWord, tailWord_5060144, baseEnd_5060144] using wordTrace_append hprefix tailTrace_5060144
  have hstable : (prefixWord ++ tailWord_5060144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5060144).length < 2 ^ (prefixWord ++ tailWord_5060144).sum := by decide
  have hdescent : baseEnd_5060144 < baseStart_5060144 := by decide
  rcases family_descends (prefixWord ++ tailWord_5060144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5060208 : List Nat := [2, 1, 1, 1, 6, 2, 2, 1, 1, 2, 4]
def baseStart_5060208 : Nat := 118140960795 + 5060208 * 2 ^ 59
def prefixEnd_5060208 : Nat := 4983230072969 + 3 ^ 40 * 5060208 * 2
def baseEnd_5060208 : Nat := 2598318915726443146628533

theorem tailTrace_5060208 : CollatzResearch.WordTrace tailWord_5060208 prefixEnd_5060208 2598318915726443146628533 := by
  unfold tailWord_5060208
  simp only [CollatzResearch.WordTrace]
  refine ⟨92280474025869052783930639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123040632034492070378574185 92280474025869052783930639)
  ·
    refine ⟨138420711038803579175895959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92280474025869052783930639 138420711038803579175895959)
    ·
      refine ⟨207631066558205368763843939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138420711038803579175895959 207631066558205368763843939)
      ·
        refine ⟨311446599837308053145765909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 207631066558205368763843939 311446599837308053145765909)
        ·
          refine ⟨14599059367373814991207777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 311446599837308053145765909 14599059367373814991207777)
          ·
            refine ⟨10949294525530361243405833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14599059367373814991207777 10949294525530361243405833)
            ·
              refine ⟨8211970894147770932554375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10949294525530361243405833 8211970894147770932554375)
              ·
                refine ⟨12317956341221656398831563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8211970894147770932554375 12317956341221656398831563)
                ·
                  refine ⟨18476934511832484598247345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12317956341221656398831563 18476934511832484598247345)
                  ·
                    refine ⟨13857700883874363448685509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18476934511832484598247345 13857700883874363448685509)
                    ·
                      refine ⟨2598318915726443146628533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13857700883874363448685509 2598318915726443146628533)
                      ·
                        rfl

theorem cell23_5060208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 2, 1, 1, 2, 4].length) (baseStart_5060208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5060208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5060208 prefixEnd_5060208 := by exact prefixLift 5060208
  have htrace : WordTrace (prefixWord ++ tailWord_5060208) baseStart_5060208 baseEnd_5060208 := by
    simpa [prefixWord, tailWord_5060208, baseEnd_5060208] using wordTrace_append hprefix tailTrace_5060208
  have hstable : (prefixWord ++ tailWord_5060208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5060208).length < 2 ^ (prefixWord ++ tailWord_5060208).sum := by decide
  have hdescent : baseEnd_5060208 < baseStart_5060208 := by decide
  rcases family_descends (prefixWord ++ tailWord_5060208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5060232 : List Nat := [2, 1, 3, 5, 1, 1, 1, 3, 1, 2, 3]
def baseStart_5060232 : Nat := 118140960795 + 5060232 * 2 ^ 59
def prefixEnd_5060232 : Nat := 4983230072969 + 3 ^ 40 * 5060232 * 2
def baseEnd_5060232 : Nat := 2598331239262151052728423

theorem tailTrace_5060232 : CollatzResearch.WordTrace tailWord_5060232 prefixEnd_5060232 2598331239262151052728423 := by
  unfold tailWord_5060232
  simp only [CollatzResearch.WordTrace]
  refine ⟨92280911701825578833367475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123041215602434105111156633 92280911701825578833367475)
  ·
    refine ⟨138421367552738368250051213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92280911701825578833367475 138421367552738368250051213)
    ·
      refine ⟨51908012832276888093769205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 138421367552738368250051213 51908012832276888093769205)
      ·
        refine ⟨4866376203025958258790863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 51908012832276888093769205 4866376203025958258790863)
        ·
          refine ⟨7299564304538937388186295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4866376203025958258790863 7299564304538937388186295)
          ·
            refine ⟨10949346456808406082279443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7299564304538937388186295 10949346456808406082279443)
            ·
              refine ⟨16424019685212609123419165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10949346456808406082279443 16424019685212609123419165)
              ·
                refine ⟨6159007381954728421282187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16424019685212609123419165 6159007381954728421282187)
                ·
                  refine ⟨9238511072932092631923281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6159007381954728421282187 9238511072932092631923281)
                  ·
                    refine ⟨6928883304699069473942461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9238511072932092631923281 6928883304699069473942461)
                    ·
                      refine ⟨2598331239262151052728423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6928883304699069473942461 2598331239262151052728423)
                      ·
                        rfl

theorem cell23_5060232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_5060232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5060232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5060232 prefixEnd_5060232 := by exact prefixLift 5060232
  have htrace : WordTrace (prefixWord ++ tailWord_5060232) baseStart_5060232 baseEnd_5060232 := by
    simpa [prefixWord, tailWord_5060232, baseEnd_5060232] using wordTrace_append hprefix tailTrace_5060232
  have hstable : (prefixWord ++ tailWord_5060232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5060232).length < 2 ^ (prefixWord ++ tailWord_5060232).sum := by decide
  have hdescent : baseEnd_5060232 < baseStart_5060232 := by decide
  rcases family_descends (prefixWord ++ tailWord_5060232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5060261 : List Nat := [1, 3, 1, 2, 1, 2, 4, 1, 2, 6]
def baseStart_5060261 : Nat := 118140960795 + 5060261 * 2 ^ 59
def prefixEnd_5060261 : Nat := 4983230072969 + 3 ^ 40 * 5060261 * 2
def baseEnd_5060261 : Nat := 866115376733710479755263

theorem tailTrace_5060261 : CollatzResearch.WordTrace tailWord_5060261 prefixEnd_5060261 866115376733710479755263 := by
  unfold tailWord_5060261
  simp only [CollatzResearch.WordTrace]
  refine ⟨184562881120546095619540637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123041920747030730413027091 184562881120546095619540637)
  ·
    refine ⟨69211080420204785857327739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 184562881120546095619540637 69211080420204785857327739)
    ·
      refine ⟨103816620630307178785991609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69211080420204785857327739 103816620630307178785991609)
      ·
        refine ⟨77862465472730384089493707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103816620630307178785991609 77862465472730384089493707)
        ·
          refine ⟨116793698209095576134240561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77862465472730384089493707 116793698209095576134240561)
          ·
            refine ⟨87595273656821682100680421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 116793698209095576134240561 87595273656821682100680421)
            ·
              refine ⟨16424113810654065393877579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 87595273656821682100680421 16424113810654065393877579)
              ·
                refine ⟨24636170715981098090816369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16424113810654065393877579 24636170715981098090816369)
                ·
                  refine ⟨18477128036985823568112277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24636170715981098090816369 18477128036985823568112277)
                  ·
                    refine ⟨866115376733710479755263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18477128036985823568112277 866115376733710479755263)
                    ·
                      rfl

theorem cell23_5060261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 1, 2, 6].length) (baseStart_5060261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5060261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5060261 prefixEnd_5060261 := by exact prefixLift 5060261
  have htrace : WordTrace (prefixWord ++ tailWord_5060261) baseStart_5060261 baseEnd_5060261 := by
    simpa [prefixWord, tailWord_5060261, baseEnd_5060261] using wordTrace_append hprefix tailTrace_5060261
  have hstable : (prefixWord ++ tailWord_5060261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5060261).length < 2 ^ (prefixWord ++ tailWord_5060261).sum := by decide
  have hdescent : baseEnd_5060261 < baseStart_5060261 := by decide
  rcases family_descends (prefixWord ++ tailWord_5060261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5060271 : List Nat := [1, 1, 2, 1, 2, 4, 2, 2, 2, 1, 5]
def baseStart_5060271 : Nat := 118140960795 + 5060271 * 2 ^ 59
def prefixEnd_5060271 : Nat := 4983230072969 + 3 ^ 40 * 5060271 * 2
def baseEnd_5060271 : Nat := 2598351265007676400140743

theorem tailTrace_5060271 : CollatzResearch.WordTrace tailWord_5060271 prefixEnd_5060271 2598351265007676400140743 := by
  unfold tailWord_5060271
  simp only [CollatzResearch.WordTrace]
  refine ⟨184563245850509867327404667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123042163900339911551603111 184563245850509867327404667)
  ·
    refine ⟨276844868775764800991107001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184563245850509867327404667 276844868775764800991107001)
    ·
      refine ⟨207633651581823600743330251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 276844868775764800991107001 207633651581823600743330251)
      ·
        refine ⟨311450477372735401114995377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 207633651581823600743330251 311450477372735401114995377)
        ·
          refine ⟨233587858029551550836246533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 311450477372735401114995377 233587858029551550836246533)
          ·
            refine ⟨43797723380540915781796225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 233587858029551550836246533 43797723380540915781796225)
            ·
              refine ⟨32848292535405686836347169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43797723380540915781796225 32848292535405686836347169)
              ·
                refine ⟨24636219401554265127260377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32848292535405686836347169 24636219401554265127260377)
                ·
                  refine ⟨18477164551165698845445283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24636219401554265127260377 18477164551165698845445283)
                  ·
                    refine ⟨27715746826748548268167925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18477164551165698845445283 27715746826748548268167925)
                    ·
                      refine ⟨2598351265007676400140743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27715746826748548268167925 2598351265007676400140743)
                      ·
                        rfl

theorem cell23_5060271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 2, 2, 1, 5].length) (baseStart_5060271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5060271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5060271 prefixEnd_5060271 := by exact prefixLift 5060271
  have htrace : WordTrace (prefixWord ++ tailWord_5060271) baseStart_5060271 baseEnd_5060271 := by
    simpa [prefixWord, tailWord_5060271, baseEnd_5060271] using wordTrace_append hprefix tailTrace_5060271
  have hstable : (prefixWord ++ tailWord_5060271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5060271).length < 2 ^ (prefixWord ++ tailWord_5060271).sum := by decide
  have hdescent : baseEnd_5060271 < baseStart_5060271 := by decide
  rcases family_descends (prefixWord ++ tailWord_5060271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5060281 : List Nat := [1, 2, 1, 4, 1, 1, 2, 2, 1, 4, 4]
def baseStart_5060281 : Nat := 118140960795 + 5060281 * 2 ^ 59
def prefixEnd_5060281 : Nat := 4983230072969 + 3 ^ 40 * 5060281 * 2
def baseEnd_5060281 : Nat := 2598356399814221361015697

theorem tailTrace_5060281 : CollatzResearch.WordTrace tailWord_5060281 prefixEnd_5060281 2598356399814221361015697 := by
  unfold tailWord_5060281
  simp only [CollatzResearch.WordTrace]
  refine ⟨184563610580473639035268697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123042407053649092690179131 184563610580473639035268697)
  ·
    refine ⟨138422707935355229276451523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184563610580473639035268697 138422707935355229276451523)
    ·
      refine ⟨207634061903032843914677285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138422707935355229276451523 207634061903032843914677285)
      ·
        refine ⟨38931386606818658234001991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 207634061903032843914677285 38931386606818658234001991)
        ·
          refine ⟨58397079910227987351002987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38931386606818658234001991 58397079910227987351002987)
          ·
            refine ⟨87595619865341981026504481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58397079910227987351002987 87595619865341981026504481)
            ·
              refine ⟨65696714899006485769878361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87595619865341981026504481 65696714899006485769878361)
              ·
                refine ⟨49272536174254864327408771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65696714899006485769878361 49272536174254864327408771)
                ·
                  refine ⟨73908804261382296491113157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49272536174254864327408771 73908804261382296491113157)
                  ·
                    refine ⟨13857900799009180592083717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 73908804261382296491113157 13857900799009180592083717)
                    ·
                      refine ⟨2598356399814221361015697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13857900799009180592083717 2598356399814221361015697)
                      ·
                        rfl

theorem cell23_5060281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 2, 1, 4, 4].length) (baseStart_5060281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5060281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5060281 prefixEnd_5060281 := by exact prefixLift 5060281
  have htrace : WordTrace (prefixWord ++ tailWord_5060281) baseStart_5060281 baseEnd_5060281 := by
    simpa [prefixWord, tailWord_5060281, baseEnd_5060281] using wordTrace_append hprefix tailTrace_5060281
  have hstable : (prefixWord ++ tailWord_5060281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5060281).length < 2 ^ (prefixWord ++ tailWord_5060281).sum := by decide
  have hdescent : baseEnd_5060281 < baseStart_5060281 := by decide
  rcases family_descends (prefixWord ++ tailWord_5060281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5060285 : List Nat := [1, 4, 1, 2, 1, 2, 1, 1, 6, 2, 2]
def baseStart_5060285 : Nat := 118140960795 + 5060285 * 2 ^ 59
def prefixEnd_5060285 : Nat := 4983230072969 + 3 ^ 40 * 5060285 * 2
def baseEnd_5060285 : Nat := 2598358453736839345365679

theorem tailTrace_5060285 : CollatzResearch.WordTrace tailWord_5060285 prefixEnd_5060285 2598358453736839345365679 := by
  unfold tailWord_5060285
  simp only [CollatzResearch.WordTrace]
  refine ⟨184563756472459147718414309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123042504314972765145609539 184563756472459147718414309)
  ·
    refine ⟨34605704338586090197202683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 184563756472459147718414309 34605704338586090197202683)
    ·
      refine ⟨51908556507879135295804025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34605704338586090197202683 51908556507879135295804025)
      ·
        refine ⟨38931417380909351471853019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51908556507879135295804025 38931417380909351471853019)
        ·
          refine ⟨58397126071364027207779529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38931417380909351471853019 58397126071364027207779529)
          ·
            refine ⟨43797844553523020405834647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58397126071364027207779529 43797844553523020405834647)
            ·
              refine ⟨65696766830284530608751971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43797844553523020405834647 65696766830284530608751971)
              ·
                refine ⟨98545150245426795913127957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65696766830284530608751971 98545150245426795913127957)
                ·
                  refine ⟨4619303917754381058427873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 98545150245426795913127957 4619303917754381058427873)
                  ·
                    refine ⟨3464477938315785793820905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4619303917754381058427873 3464477938315785793820905)
                    ·
                      refine ⟨2598358453736839345365679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3464477938315785793820905 2598358453736839345365679)
                      ·
                        rfl

theorem cell23_5060285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 1, 6, 2, 2].length) (baseStart_5060285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5060285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5060285 prefixEnd_5060285 := by exact prefixLift 5060285
  have htrace : WordTrace (prefixWord ++ tailWord_5060285) baseStart_5060285 baseEnd_5060285 := by
    simpa [prefixWord, tailWord_5060285, baseEnd_5060285] using wordTrace_append hprefix tailTrace_5060285
  have hstable : (prefixWord ++ tailWord_5060285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5060285).length < 2 ^ (prefixWord ++ tailWord_5060285).sum := by decide
  have hdescent : baseEnd_5060285 < baseStart_5060285 := by decide
  rcases family_descends (prefixWord ++ tailWord_5060285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5060302 : List Nat := [4, 1, 1, 1, 3, 1, 2, 4, 2, 2, 2]
def baseStart_5060302 : Nat := 118140960795 + 5060302 * 2 ^ 59
def prefixEnd_5060302 : Nat := 4983230072969 + 3 ^ 40 * 5060302 * 2
def baseEnd_5060302 : Nat := 2598367182907965778853101

theorem tailTrace_5060302 : CollatzResearch.WordTrace tailWord_5060302 prefixEnd_5060302 2598367182907965778853101 := by
  unfold tailWord_5060302
  simp only [CollatzResearch.WordTrace]
  refine ⟨23070547064174694952722895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 123042917675598373081188773 23070547064174694952722895)
  ·
    refine ⟨34605820596262042429084343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23070547064174694952722895 34605820596262042429084343)
    ·
      refine ⟨51908730894393063643626515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34605820596262042429084343 51908730894393063643626515)
      ·
        refine ⟨77863096341589595465439773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51908730894393063643626515 77863096341589595465439773)
        ·
          refine ⟨29198661128096098299539915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77863096341589595465439773 29198661128096098299539915)
          ·
            refine ⟨43797991692144147449309873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29198661128096098299539915 43797991692144147449309873)
            ·
              refine ⟨32848493769108110586982405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43797991692144147449309873 32848493769108110586982405)
              ·
                refine ⟨6159092581707770735059201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32848493769108110586982405 6159092581707770735059201)
                ·
                  refine ⟨4619319436280828051294401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6159092581707770735059201 4619319436280828051294401)
                  ·
                    refine ⟨3464489577210621038470801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4619319436280828051294401 3464489577210621038470801)
                    ·
                      refine ⟨2598367182907965778853101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3464489577210621038470801 2598367182907965778853101)
                      ·
                        rfl

theorem cell23_5060302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 4, 2, 2, 2].length) (baseStart_5060302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5060302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5060302 prefixEnd_5060302 := by exact prefixLift 5060302
  have htrace : WordTrace (prefixWord ++ tailWord_5060302) baseStart_5060302 baseEnd_5060302 := by
    simpa [prefixWord, tailWord_5060302, baseEnd_5060302] using wordTrace_append hprefix tailTrace_5060302
  have hstable : (prefixWord ++ tailWord_5060302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5060302).length < 2 ^ (prefixWord ++ tailWord_5060302).sum := by decide
  have hdescent : baseEnd_5060302 < baseStart_5060302 := by decide
  rcases family_descends (prefixWord ++ tailWord_5060302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5060359 : List Nat := [1, 1, 4, 4, 2, 2, 2, 2, 5]
def baseStart_5060359 : Nat := 118140960795 + 5060359 * 2 ^ 59
def prefixEnd_5060359 : Nat := 4983230072969 + 3 ^ 40 * 5060359 * 2
def baseEnd_5060359 : Nat := 288710716811696895093371

theorem tailTrace_5060359 : CollatzResearch.WordTrace tailWord_5060359 prefixEnd_5060359 288710716811696895093371 := by
  unfold tailWord_5060359
  simp only [CollatzResearch.WordTrace]
  refine ⟨184566455474191058356608131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123044303649460705571072087 184566455474191058356608131)
  ·
    refine ⟨276849683211286587534912197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184566455474191058356608131 276849683211286587534912197)
    ·
      refine ⟨51909315602116235162796037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 276849683211286587534912197 51909315602116235162796037)
      ·
        refine ⟨9732996675396794093024257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51909315602116235162796037 9732996675396794093024257)
        ·
          refine ⟨7299747506547595569768193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9732996675396794093024257 7299747506547595569768193)
          ·
            refine ⟨5474810629910696677326145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7299747506547595569768193 5474810629910696677326145)
            ·
              refine ⟨4106107972433022507994609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5474810629910696677326145 4106107972433022507994609)
              ·
                refine ⟨3079580979324766880995957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4106107972433022507994609 3079580979324766880995957)
                ·
                  refine ⟨288710716811696895093371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3079580979324766880995957 288710716811696895093371)
                  ·
                    rfl

theorem cell23_5060359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 2, 2, 5].length) (baseStart_5060359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5060359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5060359 prefixEnd_5060359 := by exact prefixLift 5060359
  have htrace : WordTrace (prefixWord ++ tailWord_5060359) baseStart_5060359 baseEnd_5060359 := by
    simpa [prefixWord, tailWord_5060359, baseEnd_5060359] using wordTrace_append hprefix tailTrace_5060359
  have hstable : (prefixWord ++ tailWord_5060359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5060359).length < 2 ^ (prefixWord ++ tailWord_5060359).sum := by decide
  have hdescent : baseEnd_5060359 < baseStart_5060359 := by decide
  rcases family_descends (prefixWord ++ tailWord_5060359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5060361 : List Nat := [1, 2, 1, 1, 3, 2, 1, 1, 1, 5, 5]
def baseStart_5060361 : Nat := 118140960795 + 5060361 * 2 ^ 59
def prefixEnd_5060361 : Nat := 4983230072969 + 3 ^ 40 * 5060361 * 2
def baseEnd_5060361 : Nat := 2598397478266581048015329

theorem tailTrace_5060361 : CollatzResearch.WordTrace tailWord_5060361 prefixEnd_5060361 2598397478266581048015329 := by
  unfold tailWord_5060361
  simp only [CollatzResearch.WordTrace]
  refine ⟨184566528420183812698180937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123044352280122541798787291 184566528420183812698180937)
  ·
    refine ⟨138424896315137859523635703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184566528420183812698180937 138424896315137859523635703)
    ·
      refine ⟨207637344472706789285453555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138424896315137859523635703 207637344472706789285453555)
      ·
        refine ⟨311456016709060183928180333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 207637344472706789285453555 311456016709060183928180333)
        ·
          refine ⟨116796006265897568973067625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 311456016709060183928180333 116796006265897568973067625)
          ·
            refine ⟨87597004699423176729800719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 116796006265897568973067625 87597004699423176729800719)
            ·
              refine ⟨131395507049134765094701079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87597004699423176729800719 131395507049134765094701079)
              ·
                refine ⟨197093260573702147642051619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 131395507049134765094701079 197093260573702147642051619)
                ·
                  refine ⟨295639890860553221463077429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 197093260573702147642051619 295639890860553221463077429)
                  ·
                    refine ⟨27716239768176864512163509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 295639890860553221463077429 27716239768176864512163509)
                    ·
                      refine ⟨2598397478266581048015329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27716239768176864512163509 2598397478266581048015329)
                      ·
                        rfl

theorem cell23_5060361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 5, 5].length) (baseStart_5060361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5060361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5060361 prefixEnd_5060361 := by exact prefixLift 5060361
  have htrace : WordTrace (prefixWord ++ tailWord_5060361) baseStart_5060361 baseEnd_5060361 := by
    simpa [prefixWord, tailWord_5060361, baseEnd_5060361] using wordTrace_append hprefix tailTrace_5060361
  have hstable : (prefixWord ++ tailWord_5060361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5060361).length < 2 ^ (prefixWord ++ tailWord_5060361).sum := by decide
  have hdescent : baseEnd_5060361 < baseStart_5060361 := by decide
  rcases family_descends (prefixWord ++ tailWord_5060361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5060371 : List Nat := [1, 1, 1, 2, 1, 3, 2, 1, 4, 1, 6]
def baseStart_5060371 : Nat := 118140960795 + 5060371 * 2 ^ 59
def prefixEnd_5060371 : Nat := 4983230072969 + 3 ^ 40 * 5060371 * 2
def baseEnd_5060371 : Nat := 2598402613073126008890283

theorem tailTrace_5060371 : CollatzResearch.WordTrace tailWord_5060371 prefixEnd_5060371 2598402613073126008890283 := by
  unfold tailWord_5060371
  simp only [CollatzResearch.WordTrace]
  refine ⟨184566893150147584406044967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123044595433431722937363311 184566893150147584406044967)
  ·
    refine ⟨276850339725221376609067451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184566893150147584406044967 276850339725221376609067451)
    ·
      refine ⟨415275509587832064913601177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 276850339725221376609067451 415275509587832064913601177)
      ·
        refine ⟨311456632190874048685200883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 415275509587832064913601177 311456632190874048685200883)
        ·
          refine ⟨467184948286311073027801325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 311456632190874048685200883 467184948286311073027801325)
          ·
            refine ⟨175194355607366652385425497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 467184948286311073027801325 175194355607366652385425497)
            ·
              refine ⟨131395766705524989289069123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 175194355607366652385425497 131395766705524989289069123)
              ·
                refine ⟨197093650058287483933603685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 131395766705524989289069123 197093650058287483933603685)
                ·
                  refine ⟨36955059385928903237550691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 197093650058287483933603685 36955059385928903237550691)
                  ·
                    refine ⟨55432589078893354856326037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36955059385928903237550691 55432589078893354856326037)
                    ·
                      refine ⟨2598402613073126008890283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 55432589078893354856326037 2598402613073126008890283)
                      ·
                        rfl

theorem cell23_5060371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 1, 4, 1, 6].length) (baseStart_5060371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5060371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5060371 prefixEnd_5060371 := by exact prefixLift 5060371
  have htrace : WordTrace (prefixWord ++ tailWord_5060371) baseStart_5060371 baseEnd_5060371 := by
    simpa [prefixWord, tailWord_5060371, baseEnd_5060371] using wordTrace_append hprefix tailTrace_5060371
  have hstable : (prefixWord ++ tailWord_5060371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5060371).length < 2 ^ (prefixWord ++ tailWord_5060371).sum := by decide
  have hdescent : baseEnd_5060371 < baseStart_5060371 := by decide
  rcases family_descends (prefixWord ++ tailWord_5060371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5060375 : List Nat := [1, 1, 3, 4, 2, 1, 1, 1, 1, 6, 2]
def baseStart_5060375 : Nat := 118140960795 + 5060375 * 2 ^ 59
def prefixEnd_5060375 : Nat := 4983230072969 + 3 ^ 40 * 5060375 * 2
def baseEnd_5060375 : Nat := 2598404666995743993240265

theorem tailTrace_5060375 : CollatzResearch.WordTrace tailWord_5060375 prefixEnd_5060375 2598404666995743993240265 := by
  unfold tailWord_5060375
  simp only [CollatzResearch.WordTrace]
  refine ⟨184567039042133093089190579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123044692694755395392793719 184567039042133093089190579)
  ·
    refine ⟨276850558563199639633785869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184567039042133093089190579 276850558563199639633785869)
    ·
      refine ⟨103818959461199864862669701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 276850558563199639633785869 103818959461199864862669701)
      ·
        refine ⟨19466054898974974661750569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 103818959461199864862669701 19466054898974974661750569)
        ·
          refine ⟨14599541174231230996312927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19466054898974974661750569 14599541174231230996312927)
          ·
            refine ⟨21899311761346846494469391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14599541174231230996312927 21899311761346846494469391)
            ·
              refine ⟨32848967642020269741704087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21899311761346846494469391 32848967642020269741704087)
              ·
                refine ⟨49273451463030404612556131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32848967642020269741704087 49273451463030404612556131)
                ·
                  refine ⟨73910177194545606918834197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49273451463030404612556131 73910177194545606918834197)
                  ·
                    refine ⟨3464539555994325324320353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 73910177194545606918834197 3464539555994325324320353)
                    ·
                      refine ⟨2598404666995743993240265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3464539555994325324320353 2598404666995743993240265)
                      ·
                        rfl

theorem cell23_5060375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 1, 1, 6, 2].length) (baseStart_5060375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5060375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5060375 prefixEnd_5060375 := by exact prefixLift 5060375
  have htrace : WordTrace (prefixWord ++ tailWord_5060375) baseStart_5060375 baseEnd_5060375 := by
    simpa [prefixWord, tailWord_5060375, baseEnd_5060375] using wordTrace_append hprefix tailTrace_5060375
  have hstable : (prefixWord ++ tailWord_5060375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5060375).length < 2 ^ (prefixWord ++ tailWord_5060375).sum := by decide
  have hdescent : baseEnd_5060375 < baseStart_5060375 := by decide
  rcases family_descends (prefixWord ++ tailWord_5060375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5060385 : List Nat := [1, 2, 3, 2, 1, 4, 1, 2, 3, 4]
def baseStart_5060385 : Nat := 118140960795 + 5060385 * 2 ^ 59
def prefixEnd_5060385 : Nat := 4983230072969 + 3 ^ 40 * 5060385 * 2
def baseEnd_5060385 : Nat := 866136600600762984705073

theorem tailTrace_5060385 : CollatzResearch.WordTrace tailWord_5060385 prefixEnd_5060385 866136600600762984705073 := by
  unfold tailWord_5060385
  simp only [CollatzResearch.WordTrace]
  refine ⟨184567403772096864797054609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123044935848064576531369739 184567403772096864797054609)
  ·
    refine ⟨138425552829072648597790957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184567403772096864797054609 138425552829072648597790957)
    ·
      refine ⟨51909582310902243224171609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 138425552829072648597790957 51909582310902243224171609)
      ·
        refine ⟨38932186733176682418128707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51909582310902243224171609 38932186733176682418128707)
        ·
          refine ⟨58398280099765023627193061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38932186733176682418128707 58398280099765023627193061)
          ·
            refine ⟨10949677518705941930098699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58398280099765023627193061 10949677518705941930098699)
            ·
              refine ⟨16424516278058912895148049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10949677518705941930098699 16424516278058912895148049)
              ·
                refine ⟨12318387208544184671361037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16424516278058912895148049 12318387208544184671361037)
                ·
                  refine ⟨4619395203204069251760389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12318387208544184671361037 4619395203204069251760389)
                  ·
                    refine ⟨866136600600762984705073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4619395203204069251760389 866136600600762984705073)
                    ·
                      rfl

theorem cell23_5060385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 2, 3, 4].length) (baseStart_5060385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5060385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5060385 prefixEnd_5060385 := by exact prefixLift 5060385
  have htrace : WordTrace (prefixWord ++ tailWord_5060385) baseStart_5060385 baseEnd_5060385 := by
    simpa [prefixWord, tailWord_5060385, baseEnd_5060385] using wordTrace_append hprefix tailTrace_5060385
  have hstable : (prefixWord ++ tailWord_5060385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5060385).length < 2 ^ (prefixWord ++ tailWord_5060385).sum := by decide
  have hdescent : baseEnd_5060385 < baseStart_5060385 := by decide
  rcases family_descends (prefixWord ++ tailWord_5060385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5060392 : List Nat := [2, 1, 5, 1, 1, 4, 1, 1, 2, 1, 4]
def baseStart_5060392 : Nat := 118140960795 + 5060392 * 2 ^ 59
def prefixEnd_5060392 : Nat := 4983230072969 + 3 ^ 40 * 5060392 * 2
def baseEnd_5060392 : Nat := 2598413396166870426727687

theorem tailTrace_5060392 : CollatzResearch.WordTrace tailWord_5060392 prefixEnd_5060392 2598413396166870426727687 := by
  unfold tailWord_5060392
  simp only [CollatzResearch.WordTrace]
  refine ⟨92283829541535752496279715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123045106055381003328372953 92283829541535752496279715)
  ·
    refine ⟨138425744312303628744419573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92283829541535752496279715 138425744312303628744419573)
    ·
      refine ⟨12977413529278465194789335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 138425744312303628744419573 12977413529278465194789335)
      ·
        refine ⟨19466120293917697792184003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12977413529278465194789335 19466120293917697792184003)
        ·
          refine ⟨29199180440876546688276005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19466120293917697792184003 29199180440876546688276005)
          ·
            refine ⟨5474846332664352504051751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29199180440876546688276005 5474846332664352504051751)
            ·
              refine ⟨8212269498996528756077627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5474846332664352504051751 8212269498996528756077627)
              ·
                refine ⟨12318404248494793134116441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8212269498996528756077627 12318404248494793134116441)
                ·
                  refine ⟨9238803186371094850587331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12318404248494793134116441 9238803186371094850587331)
                  ·
                    refine ⟨13858204779556642275880997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9238803186371094850587331 13858204779556642275880997)
                    ·
                      refine ⟨2598413396166870426727687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13858204779556642275880997 2598413396166870426727687)
                      ·
                        rfl

theorem cell23_5060392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 1, 1, 2, 1, 4].length) (baseStart_5060392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5060392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5060392 prefixEnd_5060392 := by exact prefixLift 5060392
  have htrace : WordTrace (prefixWord ++ tailWord_5060392) baseStart_5060392 baseEnd_5060392 := by
    simpa [prefixWord, tailWord_5060392, baseEnd_5060392] using wordTrace_append hprefix tailTrace_5060392
  have hstable : (prefixWord ++ tailWord_5060392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5060392).length < 2 ^ (prefixWord ++ tailWord_5060392).sum := by decide
  have hdescent : baseEnd_5060392 < baseStart_5060392 := by decide
  rcases family_descends (prefixWord ++ tailWord_5060392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5060402 : List Nat := [3, 2, 1, 1, 3, 2, 1, 5, 1, 4]
def baseStart_5060402 : Nat := 118140960795 + 5060402 * 2 ^ 59
def prefixEnd_5060402 : Nat := 4983230072969 + 3 ^ 40 * 5060402 * 2
def baseEnd_5060402 : Nat := 866139510324471795867547

theorem tailTrace_5060402 : CollatzResearch.WordTrace tailWord_5060402 prefixEnd_5060402 866139510324471795867547 := by
  unfold tailWord_5060402
  simp only [CollatzResearch.WordTrace]
  refine ⟨46142005953258819175105865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123045349208690184466948973 46142005953258819175105865)
  ·
    refine ⟨34606504464944114381329399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46142005953258819175105865 34606504464944114381329399)
    ·
      refine ⟨51909756697416171571994099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34606504464944114381329399 51909756697416171571994099)
      ·
        refine ⟨77864635046124257357991149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51909756697416171571994099 77864635046124257357991149)
        ·
          refine ⟨29199238142296596509246681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77864635046124257357991149 29199238142296596509246681)
          ·
            refine ⟨21899428606722447381935011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29199238142296596509246681 21899428606722447381935011)
            ·
              refine ⟨32849142910083671072902517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21899428606722447381935011 32849142910083671072902517)
              ·
                refine ⟨3079607147820344163084611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32849142910083671072902517 3079607147820344163084611)
                ·
                  refine ⟨4619410721730516244626917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3079607147820344163084611 4619410721730516244626917)
                  ·
                    refine ⟨866139510324471795867547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4619410721730516244626917 866139510324471795867547)
                    ·
                      rfl

theorem cell23_5060402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 5, 1, 4].length) (baseStart_5060402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5060402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5060402 prefixEnd_5060402 := by exact prefixLift 5060402
  have htrace : WordTrace (prefixWord ++ tailWord_5060402) baseStart_5060402 baseEnd_5060402 := by
    simpa [prefixWord, tailWord_5060402, baseEnd_5060402] using wordTrace_append hprefix tailTrace_5060402
  have hstable : (prefixWord ++ tailWord_5060402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5060402).length < 2 ^ (prefixWord ++ tailWord_5060402).sum := by decide
  have hdescent : baseEnd_5060402 < baseStart_5060402 := by decide
  rcases family_descends (prefixWord ++ tailWord_5060402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5060462 : List Nat := [4, 1, 2, 3, 1, 1, 2, 3, 1, 5]
def baseStart_5060462 : Nat := 118140960795 + 5060462 * 2 ^ 59
def prefixEnd_5060462 : Nat := 4983230072969 + 3 ^ 40 * 5060462 * 2
def baseEnd_5060462 : Nat := 866149779937561717617455

theorem tailTrace_5060462 : CollatzResearch.WordTrace tailWord_5060462 prefixEnd_5060462 866149779937561717617455 := by
  unfold tailWord_5060462
  simp only [CollatzResearch.WordTrace]
  refine ⟨23071276524102238368450955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 123046808128545271298405093 23071276524102238368450955)
  ·
    refine ⟨34606914786153357552676433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23071276524102238368450955 34606914786153357552676433)
    ·
      refine ⟨25955186089615018164507325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34606914786153357552676433 25955186089615018164507325)
      ·
        refine ⟨9733194783605631811690247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25955186089615018164507325 9733194783605631811690247)
        ·
          refine ⟨14599792175408447717535371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9733194783605631811690247 14599792175408447717535371)
          ·
            refine ⟨21899688263112671576303057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14599792175408447717535371 21899688263112671576303057)
            ·
              refine ⟨16424766197334503682227293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21899688263112671576303057 16424766197334503682227293)
              ·
                refine ⟨6159287324000438880835235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16424766197334503682227293 6159287324000438880835235)
                ·
                  refine ⟨9238930986000658321252853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6159287324000438880835235 9238930986000658321252853)
                  ·
                    refine ⟨866149779937561717617455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9238930986000658321252853 866149779937561717617455)
                    ·
                      rfl

theorem cell23_5060462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 3, 1, 5].length) (baseStart_5060462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5060462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5060462 prefixEnd_5060462 := by exact prefixLift 5060462
  have htrace : WordTrace (prefixWord ++ tailWord_5060462) baseStart_5060462 baseEnd_5060462 := by
    simpa [prefixWord, tailWord_5060462, baseEnd_5060462] using wordTrace_append hprefix tailTrace_5060462
  have hstable : (prefixWord ++ tailWord_5060462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5060462).length < 2 ^ (prefixWord ++ tailWord_5060462).sum := by decide
  have hdescent : baseEnd_5060462 < baseStart_5060462 := by decide
  rcases family_descends (prefixWord ++ tailWord_5060462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5060465 : List Nat := [1, 2, 2, 2, 1, 3, 1, 5, 1, 1, 4]
def baseStart_5060465 : Nat := 118140960795 + 5060465 * 2 ^ 59
def prefixEnd_5060465 : Nat := 4983230072969 + 3 ^ 40 * 5060465 * 2
def baseEnd_5060465 : Nat := 2598450880254648641114851

theorem tailTrace_5060465 : CollatzResearch.WordTrace tailWord_5060465 prefixEnd_5060465 2598450880254648641114851 := by
  unfold tailWord_5060465
  simp only [CollatzResearch.WordTrace]
  refine ⟨184570321611807038459966849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123046881074538025639977899 184570321611807038459966849)
  ·
    refine ⟨138427741208855278844975137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184570321611807038459966849 138427741208855278844975137)
    ·
      refine ⟨103820805906641459133731353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138427741208855278844975137 103820805906641459133731353)
      ·
        refine ⟨77865604429981094350298515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103820805906641459133731353 77865604429981094350298515)
        ·
          refine ⟨116798406644971641525447773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77865604429981094350298515 116798406644971641525447773)
          ·
            refine ⟨43799402491864365572042915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 116798406644971641525447773 43799402491864365572042915)
            ·
              refine ⟨65699103737796548358064373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43799402491864365572042915 65699103737796548358064373)
              ·
                refine ⟨6159290975418426408568535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 65699103737796548358064373 6159290975418426408568535)
                ·
                  refine ⟨9238936463127639612852803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6159290975418426408568535 9238936463127639612852803)
                  ·
                    refine ⟨13858404694691459419279205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9238936463127639612852803 13858404694691459419279205)
                    ·
                      refine ⟨2598450880254648641114851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13858404694691459419279205 2598450880254648641114851)
                      ·
                        rfl

theorem cell23_5060465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 5, 1, 1, 4].length) (baseStart_5060465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5060465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5060465 prefixEnd_5060465 := by exact prefixLift 5060465
  have htrace : WordTrace (prefixWord ++ tailWord_5060465) baseStart_5060465 baseEnd_5060465 := by
    simpa [prefixWord, tailWord_5060465, baseEnd_5060465] using wordTrace_append hprefix tailTrace_5060465
  have hstable : (prefixWord ++ tailWord_5060465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5060465).length < 2 ^ (prefixWord ++ tailWord_5060465).sum := by decide
  have hdescent : baseEnd_5060465 < baseStart_5060465 := by decide
  rcases family_descends (prefixWord ++ tailWord_5060465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5060475 : List Nat := [1, 1, 1, 1, 1, 5, 1, 6, 2, 4]
def baseStart_5060475 : Nat := 118140960795 + 5060475 * 2 ^ 59
def prefixEnd_5060475 : Nat := 4983230072969 + 3 ^ 40 * 5060475 * 2
def baseEnd_5060475 : Nat := 866152005020397867329935

theorem tailTrace_5060475 : CollatzResearch.WordTrace tailWord_5060475 prefixEnd_5060475 866152005020397867329935 := by
  unfold tailWord_5060475
  simp only [CollatzResearch.WordTrace]
  refine ⟨184570686341770810167830879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123047124227847206778553919 184570686341770810167830879)
  ·
    refine ⟨276856029512656215251746319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184570686341770810167830879 276856029512656215251746319)
    ·
      refine ⟨415284044268984322877619479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 276856029512656215251746319 415284044268984322877619479)
      ·
        refine ⟨622926066403476484316429219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 415284044268984322877619479 622926066403476484316429219)
        ·
          refine ⟨934389099605214726474643829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 622926066403476484316429219 934389099605214726474643829)
          ·
            refine ⟨87598978087988880606997859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 934389099605214726474643829 87598978087988880606997859)
            ·
              refine ⟨131398467131983320910496789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87598978087988880606997859 131398467131983320910496789)
              ·
                refine ⟨6159303146811718167679537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 131398467131983320910496789 6159303146811718167679537)
                ·
                  refine ⟨4619477360108788625759653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6159303146811718167679537 4619477360108788625759653)
                  ·
                    refine ⟨866152005020397867329935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4619477360108788625759653 866152005020397867329935)
                    ·
                      rfl

theorem cell23_5060475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 6, 2, 4].length) (baseStart_5060475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5060475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5060475 prefixEnd_5060475 := by exact prefixLift 5060475
  have htrace : WordTrace (prefixWord ++ tailWord_5060475) baseStart_5060475 baseEnd_5060475 := by
    simpa [prefixWord, tailWord_5060475, baseEnd_5060475] using wordTrace_append hprefix tailTrace_5060475
  have hstable : (prefixWord ++ tailWord_5060475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5060475).length < 2 ^ (prefixWord ++ tailWord_5060475).sum := by decide
  have hdescent : baseEnd_5060475 < baseStart_5060475 := by decide
  rcases family_descends (prefixWord ++ tailWord_5060475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5060485 : List Nat := [1, 3, 1, 1, 3, 2, 2, 2, 3, 2, 3]
def baseStart_5060485 : Nat := 118140960795 + 5060485 * 2 ^ 59
def prefixEnd_5060485 : Nat := 4983230072969 + 3 ^ 40 * 5060485 * 2
def baseEnd_5060485 : Nat := 2598461149867738562864759

theorem tailTrace_5060485 : CollatzResearch.WordTrace tailWord_5060485 prefixEnd_5060485 2598461149867738562864759 := by
  unfold tailWord_5060485
  simp only [CollatzResearch.WordTrace]
  refine ⟨184571051071734581875694909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123047367381156387917129939 184571051071734581875694909)
  ·
    refine ⟨69214144151900468203385591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 184571051071734581875694909 69214144151900468203385591)
    ·
      refine ⟨103821216227850702305078387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69214144151900468203385591 103821216227850702305078387)
      ·
        refine ⟨155731824341776053457617581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103821216227850702305078387 155731824341776053457617581)
        ·
          refine ⟨58399434128166020046606593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 155731824341776053457617581 58399434128166020046606593)
          ·
            refine ⟨43799575596124515034954945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58399434128166020046606593 43799575596124515034954945)
            ·
              refine ⟨32849681697093386276216209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43799575596124515034954945 32849681697093386276216209)
              ·
                refine ⟨24637261272820039707162157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32849681697093386276216209 24637261272820039707162157)
                ·
                  refine ⟨9238972977307514890185809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24637261272820039707162157 9238972977307514890185809)
                  ·
                    refine ⟨6929229732980636167639357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9238972977307514890185809 6929229732980636167639357)
                    ·
                      refine ⟨2598461149867738562864759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6929229732980636167639357 2598461149867738562864759)
                      ·
                        rfl

theorem cell23_5060485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 2, 3, 2, 3].length) (baseStart_5060485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5060485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5060485 prefixEnd_5060485 := by exact prefixLift 5060485
  have htrace : WordTrace (prefixWord ++ tailWord_5060485) baseStart_5060485 baseEnd_5060485 := by
    simpa [prefixWord, tailWord_5060485, baseEnd_5060485] using wordTrace_append hprefix tailTrace_5060485
  have hstable : (prefixWord ++ tailWord_5060485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5060485).length < 2 ^ (prefixWord ++ tailWord_5060485).sum := by decide
  have hdescent : baseEnd_5060485 < baseStart_5060485 := by decide
  rcases family_descends (prefixWord ++ tailWord_5060485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5060533 : List Nat := [1, 3, 3, 2, 1, 2, 4, 2, 1, 2, 2]
def baseStart_5060533 : Nat := 118140960795 + 5060533 * 2 ^ 59
def prefixEnd_5060533 : Nat := 4983230072969 + 3 ^ 40 * 5060533 * 2
def baseEnd_5060533 : Nat := 2598485796939154375064539

theorem tailTrace_5060533 : CollatzResearch.WordTrace tailWord_5060533 prefixEnd_5060533 2598485796939154375064539 := by
  unfold tailWord_5060533
  simp only [CollatzResearch.WordTrace]
  refine ⟨184572801775560686073442253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123048534517040457382294835 184572801775560686073442253)
  ·
    refine ⟨69214800665835257277540845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 184572801775560686073442253 69214800665835257277540845)
    ·
      refine ⟨25955550249688221479077817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69214800665835257277540845 25955550249688221479077817)
      ·
        refine ⟨19466662687266166109308363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25955550249688221479077817 19466662687266166109308363)
        ·
          refine ⟨29199994030899249163962545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19466662687266166109308363 29199994030899249163962545)
          ·
            refine ⟨21899995523174436872971909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29199994030899249163962545 21899995523174436872971909)
            ·
              refine ⟨4106249160595206913682233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21899995523174436872971909 4106249160595206913682233)
              ·
                refine ⟨3079686870446405185261675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4106249160595206913682233 3079686870446405185261675)
                ·
                  refine ⟨4619530305669607777892513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3079686870446405185261675 4619530305669607777892513)
                  ·
                    refine ⟨3464647729252205833419385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4619530305669607777892513 3464647729252205833419385)
                    ·
                      refine ⟨2598485796939154375064539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3464647729252205833419385 2598485796939154375064539)
                      ·
                        rfl

theorem cell23_5060533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 4, 2, 1, 2, 2].length) (baseStart_5060533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5060533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5060533 prefixEnd_5060533 := by exact prefixLift 5060533
  have htrace : WordTrace (prefixWord ++ tailWord_5060533) baseStart_5060533 baseEnd_5060533 := by
    simpa [prefixWord, tailWord_5060533, baseEnd_5060533] using wordTrace_append hprefix tailTrace_5060533
  have hstable : (prefixWord ++ tailWord_5060533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5060533).length < 2 ^ (prefixWord ++ tailWord_5060533).sum := by decide
  have hdescent : baseEnd_5060533 < baseStart_5060533 := by decide
  rcases family_descends (prefixWord ++ tailWord_5060533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5060583 : List Nat := [1, 1, 5, 2, 4, 1, 1, 2, 2, 1, 3]
def baseStart_5060583 : Nat := 118140960795 + 5060583 * 2 ^ 59
def prefixEnd_5060583 : Nat := 4983230072969 + 3 ^ 40 * 5060583 * 2
def baseEnd_5060583 : Nat := 2598511470971879179439309

theorem tailTrace_5060583 : CollatzResearch.WordTrace tailWord_5060583 prefixEnd_5060583 2598511470971879179439309 := by
  unfold tailWord_5060583
  simp only [CollatzResearch.WordTrace]
  refine ⟨184574625425379544612762403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123049750283586363075174935 184574625425379544612762403)
  ·
    refine ⟨276861938138069316919143605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184574625425379544612762403 276861938138069316919143605)
    ·
      refine ⟨25955806700443998461169713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 276861938138069316919143605 25955806700443998461169713)
      ·
        refine ⟨19466855025332998845877285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25955806700443998461169713 19466855025332998845877285)
        ·
          refine ⟨3650035317249937283601991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19466855025332998845877285 3650035317249937283601991)
          ·
            refine ⟨5475052975874905925402987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3650035317249937283601991 5475052975874905925402987)
            ·
              refine ⟨8212579463812358888104481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5475052975874905925402987 8212579463812358888104481)
              ·
                refine ⟨6159434597859269166078361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8212579463812358888104481 6159434597859269166078361)
                ·
                  refine ⟨4619575948394451874558771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6159434597859269166078361 4619575948394451874558771)
                  ·
                    refine ⟨6929363922591677811838157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4619575948394451874558771 6929363922591677811838157)
                    ·
                      refine ⟨2598511470971879179439309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6929363922591677811838157 2598511470971879179439309)
                      ·
                        rfl

theorem cell23_5060583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 1, 2, 2, 1, 3].length) (baseStart_5060583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5060583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5060583 prefixEnd_5060583 := by exact prefixLift 5060583
  have htrace : WordTrace (prefixWord ++ tailWord_5060583) baseStart_5060583 baseEnd_5060583 := by
    simpa [prefixWord, tailWord_5060583, baseEnd_5060583] using wordTrace_append hprefix tailTrace_5060583
  have hstable : (prefixWord ++ tailWord_5060583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5060583).length < 2 ^ (prefixWord ++ tailWord_5060583).sum := by decide
  have hdescent : baseEnd_5060583 < baseStart_5060583 := by decide
  rcases family_descends (prefixWord ++ tailWord_5060583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5060606 : List Nat := [4, 2, 2, 2, 1, 1, 3, 1, 1, 4, 2]
def baseStart_5060606 : Nat := 118140960795 + 5060606 * 2 ^ 59
def prefixEnd_5060606 : Nat := 4983230072969 + 3 ^ 40 * 5060606 * 2
def baseEnd_5060606 : Nat := 2598523281026932589451703

theorem tailTrace_5060606 : CollatzResearch.WordTrace tailWord_5060606 prefixEnd_5060606 2598523281026932589451703 := by
  unfold tailWord_5060606
  simp only [CollatzResearch.WordTrace]
  refine ⟨23071933038037027442606209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 123050309536197479693899781 23071933038037027442606209)
  ·
    refine ⟨17303949778527770581954657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23071933038037027442606209 17303949778527770581954657)
    ·
      refine ⟨12977962333895827936465993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17303949778527770581954657 12977962333895827936465993)
      ·
        refine ⟨9733471750421870952349495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12977962333895827936465993 9733471750421870952349495)
        ·
          refine ⟨14600207625632806428524243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9733471750421870952349495 14600207625632806428524243)
          ·
            refine ⟨21900311438449209642786365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14600207625632806428524243 21900311438449209642786365)
            ·
              refine ⟨8212616789418453616044887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21900311438449209642786365 8212616789418453616044887)
              ·
                refine ⟨12318925184127680424067331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8212616789418453616044887 12318925184127680424067331)
                ·
                  refine ⟨18478387776191520636100997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12318925184127680424067331 18478387776191520636100997)
                  ·
                    refine ⟨3464697708035910119268937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18478387776191520636100997 3464697708035910119268937)
                    ·
                      refine ⟨2598523281026932589451703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3464697708035910119268937 2598523281026932589451703)
                      ·
                        rfl

theorem cell23_5060606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 3, 1, 1, 4, 2].length) (baseStart_5060606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5060606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5060606 prefixEnd_5060606 := by exact prefixLift 5060606
  have htrace : WordTrace (prefixWord ++ tailWord_5060606) baseStart_5060606 baseEnd_5060606 := by
    simpa [prefixWord, tailWord_5060606, baseEnd_5060606] using wordTrace_append hprefix tailTrace_5060606
  have hstable : (prefixWord ++ tailWord_5060606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5060606).length < 2 ^ (prefixWord ++ tailWord_5060606).sum := by decide
  have hdescent : baseEnd_5060606 < baseStart_5060606 := by decide
  rcases family_descends (prefixWord ++ tailWord_5060606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5060642 : List Nat := [3, 3, 1, 1, 1, 2, 3, 2, 2, 5]
def baseStart_5060642 : Nat := 118140960795 + 5060642 * 2 ^ 59
def prefixEnd_5060642 : Nat := 4983230072969 + 3 ^ 40 * 5060642 * 2
def baseEnd_5060642 : Nat := 866180588776831482867179

theorem tailTrace_5060642 : CollatzResearch.WordTrace tailWord_5060642 prefixEnd_5060642 866180588776831482867179 := by
  unfold tailWord_5060642
  simp only [CollatzResearch.WordTrace]
  refine ⟨46144194333041449422290045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123051184888110531792773453 46144194333041449422290045)
  ·
    refine ⟨17304072874890543533358767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46144194333041449422290045 17304072874890543533358767)
    ·
      refine ⟨25956109312335815300038151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17304072874890543533358767 25956109312335815300038151)
      ·
        refine ⟨38934163968503722950057227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25956109312335815300038151 38934163968503722950057227)
        ·
          refine ⟨58401245952755584425085841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38934163968503722950057227 58401245952755584425085841)
          ·
            refine ⟨43800934464566688318814381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58401245952755584425085841 43800934464566688318814381)
            ·
              refine ⟨16425350424212508119555393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43800934464566688318814381 16425350424212508119555393)
              ·
                refine ⟨12319012818159381089666545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16425350424212508119555393 12319012818159381089666545)
                ·
                  refine ⟨9239259613619535817249909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12319012818159381089666545 9239259613619535817249909)
                  ·
                    refine ⟨866180588776831482867179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9239259613619535817249909 866180588776831482867179)
                    ·
                      rfl

theorem cell23_5060642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 2, 2, 5].length) (baseStart_5060642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5060642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5060642 prefixEnd_5060642 := by exact prefixLift 5060642
  have htrace : WordTrace (prefixWord ++ tailWord_5060642) baseStart_5060642 baseEnd_5060642 := by
    simpa [prefixWord, tailWord_5060642, baseEnd_5060642] using wordTrace_append hprefix tailTrace_5060642
  have hstable : (prefixWord ++ tailWord_5060642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5060642).length < 2 ^ (prefixWord ++ tailWord_5060642).sum := by decide
  have hdescent : baseEnd_5060642 < baseStart_5060642 := by decide
  rcases family_descends (prefixWord ++ tailWord_5060642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5060689 : List Nat := [1, 2, 2, 1, 3, 1, 1, 7, 1, 4]
def baseStart_5060689 : Nat := 118140960795 + 5060689 * 2 ^ 59
def prefixEnd_5060689 : Nat := 4983230072969 + 3 ^ 40 * 5060689 * 2
def baseEnd_5060689 : Nat := 866188633307085254904607

theorem tailTrace_5060689 : CollatzResearch.WordTrace tailWord_5060689 prefixEnd_5060689 866188633307085254904607 := by
  unfold tailWord_5060689
  simp only [CollatzResearch.WordTrace]
  refine ⟨184578491562995524716121121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123052327708663683144080747 184578491562995524716121121)
  ·
    refine ⟨138433868672246643537090841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184578491562995524716121121 138433868672246643537090841)
    ·
      refine ⟨103825401504184982652818131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138433868672246643537090841 103825401504184982652818131)
      ·
        refine ⟨155738102256277473979227197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103825401504184982652818131 155738102256277473979227197)
        ·
          refine ⟨58401788346104052742210199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 155738102256277473979227197 58401788346104052742210199)
          ·
            refine ⟨87602682519156079113315299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58401788346104052742210199 87602682519156079113315299)
            ·
              refine ⟨131404023778734118669972949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87602682519156079113315299 131404023778734118669972949)
              ·
                refine ⟨3079781807314080906327491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 131404023778734118669972949 3079781807314080906327491)
                ·
                  refine ⟨4619672710971121359491237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3079781807314080906327491 4619672710971121359491237)
                  ·
                    refine ⟨866188633307085254904607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4619672710971121359491237 866188633307085254904607)
                    ·
                      rfl

theorem cell23_5060689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 7, 1, 4].length) (baseStart_5060689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5060689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5060689 prefixEnd_5060689 := by exact prefixLift 5060689
  have htrace : WordTrace (prefixWord ++ tailWord_5060689) baseStart_5060689 baseEnd_5060689 := by
    simpa [prefixWord, tailWord_5060689, baseEnd_5060689] using wordTrace_append hprefix tailTrace_5060689
  have hstable : (prefixWord ++ tailWord_5060689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5060689).length < 2 ^ (prefixWord ++ tailWord_5060689).sum := by decide
  have hdescent : baseEnd_5060689 < baseStart_5060689 := by decide
  rcases family_descends (prefixWord ++ tailWord_5060689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5060705 : List Nat := [1, 2, 3, 1, 1, 2, 1, 3, 1, 2, 6]
def baseStart_5060705 : Nat := 118140960795 + 5060705 * 2 ^ 59
def prefixEnd_5060705 : Nat := 4983230072969 + 3 ^ 40 * 5060705 * 2
def baseEnd_5060705 : Nat := 2598574115611727702113747

theorem tailTrace_5060705 : CollatzResearch.WordTrace tailWord_5060705 prefixEnd_5060705 2598574115611727702113747 := by
  unfold tailWord_5060705
  simp only [CollatzResearch.WordTrace]
  refine ⟨184579075130937559448703569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123052716753958372965802379 184579075130937559448703569)
  ·
    refine ⟨138434306348203169586527677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184579075130937559448703569 138434306348203169586527677)
    ·
      refine ⟨51912864880576188594947879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 138434306348203169586527677 51912864880576188594947879)
      ·
        refine ⟨77869297320864282892421819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51912864880576188594947879 77869297320864282892421819)
        ·
          refine ⟨116803945981296424338632729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77869297320864282892421819 116803945981296424338632729)
          ·
            refine ⟨87602959485972318253974547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 116803945981296424338632729 87602959485972318253974547)
            ·
              refine ⟨131404439228958477380961821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87602959485972318253974547 131404439228958477380961821)
              ·
                refine ⟨49276664710859429017860683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 131404439228958477380961821 49276664710859429017860683)
                ·
                  refine ⟨73914997066289143526791025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49276664710859429017860683 73914997066289143526791025)
                  ·
                    refine ⟨55436247799716857645093269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 73914997066289143526791025 55436247799716857645093269)
                    ·
                      refine ⟨2598574115611727702113747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 55436247799716857645093269 2598574115611727702113747)
                      ·
                        rfl

theorem cell23_5060705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 3, 1, 2, 6].length) (baseStart_5060705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5060705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5060705 prefixEnd_5060705 := by exact prefixLift 5060705
  have htrace : WordTrace (prefixWord ++ tailWord_5060705) baseStart_5060705 baseEnd_5060705 := by
    simpa [prefixWord, tailWord_5060705, baseEnd_5060705] using wordTrace_append hprefix tailTrace_5060705
  have hstable : (prefixWord ++ tailWord_5060705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5060705).length < 2 ^ (prefixWord ++ tailWord_5060705).sum := by decide
  have hdescent : baseEnd_5060705 < baseStart_5060705 := by decide
  rcases family_descends (prefixWord ++ tailWord_5060705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5060729 : List Nat := [1, 2, 1, 3, 4, 1, 1, 1, 5, 1, 3]
def baseStart_5060729 : Nat := 118140960795 + 5060729 * 2 ^ 59
def prefixEnd_5060729 : Nat := 4983230072969 + 3 ^ 40 * 5060729 * 2
def baseEnd_5060729 : Nat := 2598586439147435608213637

theorem tailTrace_5060729 : CollatzResearch.WordTrace tailWord_5060729 prefixEnd_5060729 2598586439147435608213637 := by
  unfold tailWord_5060729
  simp only [CollatzResearch.WordTrace]
  refine ⟨184579950482850611547577241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123053300321900407698384827 184579950482850611547577241)
  ·
    refine ⟨138434962862137958660682931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184579950482850611547577241 138434962862137958660682931)
    ·
      refine ⟨207652444293206937991024397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138434962862137958660682931 207652444293206937991024397)
      ·
        refine ⟨77869666609952601746634149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 207652444293206937991024397 77869666609952601746634149)
        ·
          refine ⟨14600562489366112827493903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 77869666609952601746634149 14600562489366112827493903)
          ·
            refine ⟨21900843734049169241240855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14600562489366112827493903 21900843734049169241240855)
            ·
              refine ⟨32851265601073753861861283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21900843734049169241240855 32851265601073753861861283)
              ·
                refine ⟨49276898401610630792791925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32851265601073753861861283 49276898401610630792791925)
                ·
                  refine ⟨4619709225150996636824243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 49276898401610630792791925 4619709225150996636824243)
                  ·
                    refine ⟨6929563837726494955236365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4619709225150996636824243 6929563837726494955236365)
                    ·
                      refine ⟨2598586439147435608213637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6929563837726494955236365 2598586439147435608213637)
                      ·
                        rfl

theorem cell23_5060729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 1, 5, 1, 3].length) (baseStart_5060729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5060729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5060729 prefixEnd_5060729 := by exact prefixLift 5060729
  have htrace : WordTrace (prefixWord ++ tailWord_5060729) baseStart_5060729 baseEnd_5060729 := by
    simpa [prefixWord, tailWord_5060729, baseEnd_5060729] using wordTrace_append hprefix tailTrace_5060729
  have hstable : (prefixWord ++ tailWord_5060729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5060729).length < 2 ^ (prefixWord ++ tailWord_5060729).sum := by decide
  have hdescent : baseEnd_5060729 < baseStart_5060729 := by decide
  rcases family_descends (prefixWord ++ tailWord_5060729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5060732 : List Nat := [2, 2, 2, 1, 1, 4, 2, 1, 3, 5]
def baseStart_5060732 : Nat := 118140960795 + 5060732 * 2 ^ 59
def prefixEnd_5060732 : Nat := 4983230072969 + 3 ^ 40 * 5060732 * 2
def baseEnd_5060732 : Nat := 866195993196466365492041

theorem tailTrace_5060732 : CollatzResearch.WordTrace tailWord_5060732 prefixEnd_5060732 866195993196466365492041 := by
  unfold tailWord_5060732
  simp only [CollatzResearch.WordTrace]
  refine ⟨92290029950919871529968225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123053373267893162039957633 92290029950919871529968225)
  ·
    refine ⟨69217522463189903647476169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92290029950919871529968225 69217522463189903647476169)
    ·
      refine ⟨51913141847392427735607127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69217522463189903647476169 51913141847392427735607127)
      ·
        refine ⟨77869712771088641603410691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51913141847392427735607127 77869712771088641603410691)
        ·
          refine ⟨116804569156632962405116037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77869712771088641603410691 116804569156632962405116037)
          ·
            refine ⟨21900856716868680450959257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 116804569156632962405116037 21900856716868680450959257)
            ·
              refine ⟨16425642537651510338219443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21900856716868680450959257 16425642537651510338219443)
              ·
                refine ⟨24638463806477265507329165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16425642537651510338219443 24638463806477265507329165)
                ·
                  refine ⟨9239423927428974565248437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24638463806477265507329165 9239423927428974565248437)
                  ·
                    refine ⟨866195993196466365492041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9239423927428974565248437 866195993196466365492041)
                    ·
                      rfl

theorem cell23_5060732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 1, 3, 5].length) (baseStart_5060732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5060732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5060732 prefixEnd_5060732 := by exact prefixLift 5060732
  have htrace : WordTrace (prefixWord ++ tailWord_5060732) baseStart_5060732 baseEnd_5060732 := by
    simpa [prefixWord, tailWord_5060732, baseEnd_5060732] using wordTrace_append hprefix tailTrace_5060732
  have hstable : (prefixWord ++ tailWord_5060732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5060732).length < 2 ^ (prefixWord ++ tailWord_5060732).sum := by decide
  have hdescent : baseEnd_5060732 < baseStart_5060732 := by decide
  rcases family_descends (prefixWord ++ tailWord_5060732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5060739 : List Nat := [1, 1, 1, 3, 3, 4, 1, 1, 1, 5, 2]
def baseStart_5060739 : Nat := 118140960795 + 5060739 * 2 ^ 59
def prefixEnd_5060739 : Nat := 4983230072969 + 3 ^ 40 * 5060739 * 2
def baseEnd_5060739 : Nat := 2598591573953980569088591

theorem tailTrace_5060739 : CollatzResearch.WordTrace tailWord_5060739 prefixEnd_5060739 2598591573953980569088591 := by
  unfold tailWord_5060739
  simp only [CollatzResearch.WordTrace]
  refine ⟨184580315212814383255441271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123053543475209588836960847 184580315212814383255441271)
  ·
    refine ⟨276870472819221574883161907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184580315212814383255441271 276870472819221574883161907)
    ·
      refine ⟨415305709228832362324742861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 276870472819221574883161907 415305709228832362324742861)
      ·
        refine ⟨155739640960812135871778573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 415305709228832362324742861 155739640960812135871778573)
        ·
          refine ⟨58402365360304550951916965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 155739640960812135871778573 58402365360304550951916965)
          ·
            refine ⟨10950443505057103303484431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58402365360304550951916965 10950443505057103303484431)
            ·
              refine ⟨16425665257585654955226647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10950443505057103303484431 16425665257585654955226647)
              ·
                refine ⟨24638497886378482432839971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16425665257585654955226647 24638497886378482432839971)
                ·
                  refine ⟨36957746829567723649259957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24638497886378482432839971 36957746829567723649259957)
                  ·
                    refine ⟨3464788765271974092118121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 36957746829567723649259957 3464788765271974092118121)
                    ·
                      refine ⟨2598591573953980569088591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3464788765271974092118121 2598591573953980569088591)
                      ·
                        rfl

theorem cell23_5060739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 1, 1, 5, 2].length) (baseStart_5060739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5060739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5060739 prefixEnd_5060739 := by exact prefixLift 5060739
  have htrace : WordTrace (prefixWord ++ tailWord_5060739) baseStart_5060739 baseEnd_5060739 := by
    simpa [prefixWord, tailWord_5060739, baseEnd_5060739] using wordTrace_append hprefix tailTrace_5060739
  have hstable : (prefixWord ++ tailWord_5060739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5060739).length < 2 ^ (prefixWord ++ tailWord_5060739).sum := by decide
  have hdescent : baseEnd_5060739 < baseStart_5060739 := by decide
  rcases family_descends (prefixWord ++ tailWord_5060739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5060786 : List Nat := [3, 2, 1, 1, 1, 3, 1, 4, 3, 2, 2]
def baseStart_5060786 : Nat := 118140960795 + 5060786 * 2 ^ 59
def prefixEnd_5060786 : Nat := 4983230072969 + 3 ^ 40 * 5060786 * 2
def baseEnd_5060786 : Nat := 2598615707544741885200875

theorem tailTrace_5060786 : CollatzResearch.WordTrace tailWord_5060786 prefixEnd_5060786 2598615707544741885200875 := by
  unfold tailWord_5060786
  simp only [CollatzResearch.WordTrace]
  refine ⟨46145507360911027570600553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123054686295762740188268141 46145507360911027570600553)
  ·
    refine ⟨34609130520683270677950415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46145507360911027570600553 34609130520683270677950415)
    ·
      refine ⟨51913695781024906016925623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34609130520683270677950415 51913695781024906016925623)
      ·
        refine ⟨77870543671537359025388435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51913695781024906016925623 77870543671537359025388435)
        ·
          refine ⟨116805815507306038538082653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77870543671537359025388435 116805815507306038538082653)
          ·
            refine ⟨43802180815239764451780995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 116805815507306038538082653 43802180815239764451780995)
            ·
              refine ⟨65703271222859646677671493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43802180815239764451780995 65703271222859646677671493)
              ·
                refine ⟨12319363354286183752063405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 65703271222859646677671493 12319363354286183752063405)
                ·
                  refine ⟨4619761257857318907023777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12319363354286183752063405 4619761257857318907023777)
                  ·
                    refine ⟨3464820943392989180267833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4619761257857318907023777 3464820943392989180267833)
                    ·
                      refine ⟨2598615707544741885200875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3464820943392989180267833 2598615707544741885200875)
                      ·
                        rfl

theorem cell23_5060786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 4, 3, 2, 2].length) (baseStart_5060786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5060786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5060786 prefixEnd_5060786 := by exact prefixLift 5060786
  have htrace : WordTrace (prefixWord ++ tailWord_5060786) baseStart_5060786 baseEnd_5060786 := by
    simpa [prefixWord, tailWord_5060786, baseEnd_5060786] using wordTrace_append hprefix tailTrace_5060786
  have hstable : (prefixWord ++ tailWord_5060786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5060786).length < 2 ^ (prefixWord ++ tailWord_5060786).sum := by decide
  have hdescent : baseEnd_5060786 < baseStart_5060786 := by decide
  rcases family_descends (prefixWord ++ tailWord_5060786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5060863 : List Nat := [1, 1, 2, 2, 1, 4, 5, 1, 1, 3, 2]
def baseStart_5060863 : Nat := 118140960795 + 5060863 * 2 ^ 59
def prefixEnd_5060863 : Nat := 4983230072969 + 3 ^ 40 * 5060863 * 2
def baseEnd_5060863 : Nat := 2598655245555138083938021

theorem tailTrace_5060863 : CollatzResearch.WordTrace tailWord_5060863 prefixEnd_5060863 2598655245555138083938021 := by
  unfold tailWord_5060863
  simp only [CollatzResearch.WordTrace]
  refine ⟨184584837864365152432955243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123056558576243434955303495 184584837864365152432955243)
  ·
    refine ⟨276877256796547728649432865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184584837864365152432955243 276877256796547728649432865)
    ·
      refine ⟨207657942597410796487074649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 276877256796547728649432865 207657942597410796487074649)
      ·
        refine ⟨155743456948058097365305987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 207657942597410796487074649 155743456948058097365305987)
        ·
          refine ⟨233615185422087146047958981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155743456948058097365305987 233615185422087146047958981)
          ·
            refine ⟨43802847266641339883992309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 233615185422087146047958981 43802847266641339883992309)
            ·
              refine ⟨4106516931247625614124279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 43802847266641339883992309 4106516931247625614124279)
              ·
                refine ⟨6159775396871438421186419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4106516931247625614124279 6159775396871438421186419)
                ·
                  refine ⟨9239663095307157631779629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6159775396871438421186419 9239663095307157631779629)
                  ·
                    refine ⟨3464873660740184111917361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9239663095307157631779629 3464873660740184111917361)
                    ·
                      refine ⟨2598655245555138083938021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3464873660740184111917361 2598655245555138083938021)
                      ·
                        rfl

theorem cell23_5060863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 5, 1, 1, 3, 2].length) (baseStart_5060863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5060863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5060863 prefixEnd_5060863 := by exact prefixLift 5060863
  have htrace : WordTrace (prefixWord ++ tailWord_5060863) baseStart_5060863 baseEnd_5060863 := by
    simpa [prefixWord, tailWord_5060863, baseEnd_5060863] using wordTrace_append hprefix tailTrace_5060863
  have hstable : (prefixWord ++ tailWord_5060863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5060863).length < 2 ^ (prefixWord ++ tailWord_5060863).sum := by decide
  have hdescent : baseEnd_5060863 < baseStart_5060863 := by decide
  rcases family_descends (prefixWord ++ tailWord_5060863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5060871 : List Nat := [1, 1, 4, 5, 2, 1, 2, 2, 1, 2, 2]
def baseStart_5060871 : Nat := 118140960795 + 5060871 * 2 ^ 59
def prefixEnd_5060871 : Nat := 4983230072969 + 3 ^ 40 * 5060871 * 2
def baseEnd_5060871 : Nat := 2598659353400374052637985

theorem tailTrace_5060871 : CollatzResearch.WordTrace tailWord_5060871 prefixEnd_5060871 2598659353400374052637985 := by
  unfold tailWord_5060871
  simp only [CollatzResearch.WordTrace]
  refine ⟨184585129648336169799246467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123056753098890779866164311 184585129648336169799246467)
  ·
    refine ⟨276877694472504254698869701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184585129648336169799246467 276877694472504254698869701)
    ·
      refine ⟨51914567713594547756038069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 276877694472504254698869701 51914567713594547756038069)
      ·
        refine ⟨4866990723149488852128569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 51914567713594547756038069 4866990723149488852128569)
        ·
          refine ⟨3650243042362116639096427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4866990723149488852128569 3650243042362116639096427)
          ·
            refine ⟨5475364563543174958644641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3650243042362116639096427 5475364563543174958644641)
            ·
              refine ⟨4106523422657381218983481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5475364563543174958644641 4106523422657381218983481)
              ·
                refine ⟨3079892566993035914237611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4106523422657381218983481 3079892566993035914237611)
                ·
                  refine ⟨4619838850489553871356417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3079892566993035914237611 4619838850489553871356417)
                  ·
                    refine ⟨3464879137867165403517313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4619838850489553871356417 3464879137867165403517313)
                    ·
                      refine ⟨2598659353400374052637985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3464879137867165403517313 2598659353400374052637985)
                      ·
                        rfl

theorem cell23_5060871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 2, 2, 1, 2, 2].length) (baseStart_5060871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5060871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5060871 prefixEnd_5060871 := by exact prefixLift 5060871
  have htrace : WordTrace (prefixWord ++ tailWord_5060871) baseStart_5060871 baseEnd_5060871 := by
    simpa [prefixWord, tailWord_5060871, baseEnd_5060871] using wordTrace_append hprefix tailTrace_5060871
  have hstable : (prefixWord ++ tailWord_5060871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5060871).length < 2 ^ (prefixWord ++ tailWord_5060871).sum := by decide
  have hdescent : baseEnd_5060871 < baseStart_5060871 := by decide
  rcases family_descends (prefixWord ++ tailWord_5060871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5060926 : List Nat := [4, 2, 1, 2, 1, 2, 1, 2, 2, 3, 3]
def baseStart_5060926 : Nat := 118140960795 + 5060926 * 2 ^ 59
def prefixEnd_5060926 : Nat := 4983230072969 + 3 ^ 40 * 5060926 * 2
def baseEnd_5060926 : Nat := 2598687594836371337450231

theorem tailTrace_5060926 : CollatzResearch.WordTrace tailWord_5060926 prefixEnd_5060926 2598687594836371337450231 := by
  unfold tailWord_5060926
  simp only [CollatzResearch.WordTrace]
  refine ⟨23073391957892114274062329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 123058090442091276128332421 23073391957892114274062329)
  ·
    refine ⟨17305043968419085705546747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23073391957892114274062329 17305043968419085705546747)
    ·
      refine ⟨25957565952628628558320121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17305043968419085705546747 25957565952628628558320121)
      ·
        refine ⟨19468174464471471418740091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25957565952628628558320121 19468174464471471418740091)
        ·
          refine ⟨29202261696707207128110137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19468174464471471418740091 29202261696707207128110137)
          ·
            refine ⟨21901696272530405346082603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29202261696707207128110137 21901696272530405346082603)
            ·
              refine ⟨32852544408795608019123905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21901696272530405346082603 32852544408795608019123905)
              ·
                refine ⟨24639408306596706014342929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32852544408795608019123905 24639408306596706014342929)
                ·
                  refine ⟨18479556229947529510757197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24639408306596706014342929 18479556229947529510757197)
                  ·
                    refine ⟨6929833586230323566533949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18479556229947529510757197 6929833586230323566533949)
                    ·
                      refine ⟨2598687594836371337450231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6929833586230323566533949 2598687594836371337450231)
                      ·
                        rfl

theorem cell23_5060926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 2, 2, 3, 3].length) (baseStart_5060926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5060926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5060926 prefixEnd_5060926 := by exact prefixLift 5060926
  have htrace : WordTrace (prefixWord ++ tailWord_5060926) baseStart_5060926 baseEnd_5060926 := by
    simpa [prefixWord, tailWord_5060926, baseEnd_5060926] using wordTrace_append hprefix tailTrace_5060926
  have hstable : (prefixWord ++ tailWord_5060926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5060926).length < 2 ^ (prefixWord ++ tailWord_5060926).sum := by decide
  have hdescent : baseEnd_5060926 < baseStart_5060926 := by decide
  rcases family_descends (prefixWord ++ tailWord_5060926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5060969 : List Nat := [1, 2, 1, 1, 1, 3, 3, 3, 1, 4, 3]
def baseStart_5060969 : Nat := 118140960795 + 5060969 * 2 ^ 59
def prefixEnd_5060969 : Nat := 4983230072969 + 3 ^ 40 * 5060969 * 2
def baseEnd_5060969 : Nat := 2598709674504514669212533

theorem tailTrace_5060969 : CollatzResearch.WordTrace tailWord_5060969 prefixEnd_5060969 2598709674504514669212533 := by
  unfold tailWord_5060969
  simp only [CollatzResearch.WordTrace]
  refine ⟨184588704001981132536313961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123059136001320755024209307 184588704001981132536313961)
  ·
    refine ⟨138441528001485849402235471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184588704001981132536313961 138441528001485849402235471)
    ·
      refine ⟨207662292002228774103353207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138441528001485849402235471 207662292002228774103353207)
      ·
        refine ⟨311493438003343161155029811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 207662292002228774103353207 311493438003343161155029811)
        ·
          refine ⟨467240157005014741732544717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 311493438003343161155029811 467240157005014741732544717)
          ·
            refine ⟨175215058876880528149704269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 467240157005014741732544717 175215058876880528149704269)
            ·
              refine ⟨65705647078830198056139101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 175215058876880528149704269 65705647078830198056139101)
              ·
                refine ⟨24639617654561324271052163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 65705647078830198056139101 24639617654561324271052163)
                ·
                  refine ⟨36959426481841986406578245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24639617654561324271052163 36959426481841986406578245)
                  ·
                    refine ⟨6929892465345372451233421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36959426481841986406578245 6929892465345372451233421)
                    ·
                      refine ⟨2598709674504514669212533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6929892465345372451233421 2598709674504514669212533)
                      ·
                        rfl

theorem cell23_5060969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 3, 1, 4, 3].length) (baseStart_5060969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5060969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5060969 prefixEnd_5060969 := by exact prefixLift 5060969
  have htrace : WordTrace (prefixWord ++ tailWord_5060969) baseStart_5060969 baseEnd_5060969 := by
    simpa [prefixWord, tailWord_5060969, baseEnd_5060969] using wordTrace_append hprefix tailTrace_5060969
  have hstable : (prefixWord ++ tailWord_5060969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5060969).length < 2 ^ (prefixWord ++ tailWord_5060969).sum := by decide
  have hdescent : baseEnd_5060969 < baseStart_5060969 := by decide
  rcases family_descends (prefixWord ++ tailWord_5060969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5060989 : List Nat := [1, 4, 1, 1, 2, 3, 2, 1, 8]
def baseStart_5060989 : Nat := 118140960795 + 5060989 * 2 ^ 59
def prefixEnd_5060989 : Nat := 4983230072969 + 3 ^ 40 * 5060989 * 2
def baseEnd_5060989 : Nat := 288746660457511621218049

theorem tailTrace_5060989 : CollatzResearch.WordTrace tailWord_5060989 prefixEnd_5060989 288746660457511621218049 := by
  unfold tailWord_5060989
  simp only [CollatzResearch.WordTrace]
  refine ⟨184589433461908675952042021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123059622307939117301361347 184589433461908675952042021)
  ·
    refine ⟨34610518774107876741007879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 184589433461908675952042021 34610518774107876741007879)
    ·
      refine ⟨51915778161161815111511819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34610518774107876741007879 51915778161161815111511819)
      ·
        refine ⟨77873667241742722667267729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51915778161161815111511819 77873667241742722667267729)
        ·
          refine ⟨58405250431307042000450797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77873667241742722667267729 58405250431307042000450797)
          ·
            refine ⟨21901968911740140750169049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58405250431307042000450797 21901968911740140750169049)
            ·
              refine ⟨16426476683805105562626787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21901968911740140750169049 16426476683805105562626787)
              ·
                refine ⟨24639715025707658343940181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16426476683805105562626787 24639715025707658343940181)
                ·
                  refine ⟨288746660457511621218049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24639715025707658343940181 288746660457511621218049)
                  ·
                    rfl

theorem cell23_5060989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 1, 8].length) (baseStart_5060989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5060989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5060989 prefixEnd_5060989 := by exact prefixLift 5060989
  have htrace : WordTrace (prefixWord ++ tailWord_5060989) baseStart_5060989 baseEnd_5060989 := by
    simpa [prefixWord, tailWord_5060989, baseEnd_5060989] using wordTrace_append hprefix tailTrace_5060989
  have hstable : (prefixWord ++ tailWord_5060989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5060989).length < 2 ^ (prefixWord ++ tailWord_5060989).sum := by decide
  have hdescent : baseEnd_5060989 < baseStart_5060989 := by decide
  rcases family_descends (prefixWord ++ tailWord_5060989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5060993 : List Nat := [1, 2, 4, 3, 1, 1, 3, 1, 3, 4]
def baseStart_5060993 : Nat := 118140960795 + 5060993 * 2 ^ 59
def prefixEnd_5060993 : Nat := 4983230072969 + 3 ^ 40 * 5060993 * 2
def baseEnd_5060993 : Nat := 866240666013407525104141

theorem tailTrace_5060993 : CollatzResearch.WordTrace tailWord_5060993 prefixEnd_5060993 866240666013407525104141 := by
  unfold tailWord_5060993
  simp only [CollatzResearch.WordTrace]
  refine ⟨184589579353894184635187633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123059719569262789756791755 184589579353894184635187633)
  ·
    refine ⟨138442184515420638476390725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184589579353894184635187633 138442184515420638476390725)
    ·
      refine ⟨25957909596641369714323261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 138442184515420638476390725 25957909596641369714323261)
      ·
        refine ⟨9734216098740513642871223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25957909596641369714323261 9734216098740513642871223)
        ·
          refine ⟨14601324148110770464306835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9734216098740513642871223 14601324148110770464306835)
          ·
            refine ⟨21901986222166155696460253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14601324148110770464306835 21901986222166155696460253)
            ·
              refine ⟨8213244833312308386172595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21901986222166155696460253 8213244833312308386172595)
              ·
                refine ⟨12319867249968462579258893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8213244833312308386172595 12319867249968462579258893)
                ·
                  refine ⟨4619950218738173467222085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12319867249968462579258893 4619950218738173467222085)
                  ·
                    refine ⟨866240666013407525104141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4619950218738173467222085 866240666013407525104141)
                    ·
                      rfl

theorem cell23_5060993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 3, 1, 3, 4].length) (baseStart_5060993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5060993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5060993 prefixEnd_5060993 := by exact prefixLift 5060993
  have htrace : WordTrace (prefixWord ++ tailWord_5060993) baseStart_5060993 baseEnd_5060993 := by
    simpa [prefixWord, tailWord_5060993, baseEnd_5060993] using wordTrace_append hprefix tailTrace_5060993
  have hstable : (prefixWord ++ tailWord_5060993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5060993).length < 2 ^ (prefixWord ++ tailWord_5060993).sum := by decide
  have hdescent : baseEnd_5060993 < baseStart_5060993 := by decide
  rcases family_descends (prefixWord ++ tailWord_5060993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5061044 : List Nat := [2, 5, 2, 2, 1, 1, 1, 4, 1, 4]
def baseStart_5061044 : Nat := 118140960795 + 5061044 * 2 ^ 59
def prefixEnd_5061044 : Nat := 4983230072969 + 3 ^ 40 * 5061044 * 2
def baseEnd_5061044 : Nat := 866249395184533958591563

theorem tailTrace_5061044 : CollatzResearch.WordTrace tailWord_5061044 prefixEnd_5061044 866249395184533958591563 := by
  unfold tailWord_5061044
  simp only [CollatzResearch.WordTrace]
  refine ⟨92295719738354710172647093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123060959651139613563529457 92295719738354710172647093)
  ·
    refine ⟨8652723725470754078685665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 92295719738354710172647093 8652723725470754078685665)
    ·
      refine ⟨6489542794103065559014249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8652723725470754078685665 6489542794103065559014249)
      ·
        refine ⟨4867157095577299169260687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6489542794103065559014249 4867157095577299169260687)
        ·
          refine ⟨7300735643365948753891031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4867157095577299169260687 7300735643365948753891031)
          ·
            refine ⟨10951103465048923130836547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7300735643365948753891031 10951103465048923130836547)
            ·
              refine ⟨16426655197573384696254821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10951103465048923130836547 16426655197573384696254821)
              ·
                refine ⟨3079997849545009630547779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16426655197573384696254821 3079997849545009630547779)
                ·
                  refine ⟨4619996774317514445821669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3079997849545009630547779 4619996774317514445821669)
                  ·
                    refine ⟨866249395184533958591563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4619996774317514445821669 866249395184533958591563)
                    ·
                      rfl

theorem cell23_5061044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 4, 1, 4].length) (baseStart_5061044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5061044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5061044 prefixEnd_5061044 := by exact prefixLift 5061044
  have htrace : WordTrace (prefixWord ++ tailWord_5061044) baseStart_5061044 baseEnd_5061044 := by
    simpa [prefixWord, tailWord_5061044, baseEnd_5061044] using wordTrace_append hprefix tailTrace_5061044
  have hstable : (prefixWord ++ tailWord_5061044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5061044).length < 2 ^ (prefixWord ++ tailWord_5061044).sum := by decide
  have hdescent : baseEnd_5061044 < baseStart_5061044 := by decide
  rcases family_descends (prefixWord ++ tailWord_5061044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5061056 : List Nat := [2, 1, 1, 2, 3, 1, 1, 2, 2, 6, 2]
def baseStart_5061056 : Nat := 118140960795 + 5061056 * 2 ^ 59
def prefixEnd_5061056 : Nat := 4983230072969 + 3 ^ 40 * 5061056 * 2
def baseEnd_5061056 : Nat := 2598754347321455828824633

theorem tailTrace_5061056 : CollatzResearch.WordTrace tailWord_5061056 prefixEnd_5061056 2598754347321455828824633 := by
  unfold tailWord_5061056
  simp only [CollatzResearch.WordTrace]
  refine ⟨92295938576332973197365511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123061251435110630929820681 92295938576332973197365511)
  ·
    refine ⟨138443907864499459796048267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92295938576332973197365511 138443907864499459796048267)
    ·
      refine ⟨207665861796749189694072401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138443907864499459796048267 207665861796749189694072401)
      ·
        refine ⟨155749396347561892270554301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 207665861796749189694072401 155749396347561892270554301)
        ·
          refine ⟨58406023630335709601457863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 155749396347561892270554301 58406023630335709601457863)
          ·
            refine ⟨87609035445503564402186795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58406023630335709601457863 87609035445503564402186795)
            ·
              refine ⟨131413553168255346603280193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87609035445503564402186795 131413553168255346603280193)
              ·
                refine ⟨98560164876191509952460145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 131413553168255346603280193 98560164876191509952460145)
                ·
                  refine ⟨73920123657143632464345109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 98560164876191509952460145 73920123657143632464345109)
                  ·
                    refine ⟨3465005796428607771766177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 73920123657143632464345109 3465005796428607771766177)
                    ·
                      refine ⟨2598754347321455828824633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3465005796428607771766177 2598754347321455828824633)
                      ·
                        rfl

theorem cell23_5061056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 2, 2, 6, 2].length) (baseStart_5061056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5061056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5061056 prefixEnd_5061056 := by exact prefixLift 5061056
  have htrace : WordTrace (prefixWord ++ tailWord_5061056) baseStart_5061056 baseEnd_5061056 := by
    simpa [prefixWord, tailWord_5061056, baseEnd_5061056] using wordTrace_append hprefix tailTrace_5061056
  have hstable : (prefixWord ++ tailWord_5061056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5061056).length < 2 ^ (prefixWord ++ tailWord_5061056).sum := by decide
  have hdescent : baseEnd_5061056 < baseStart_5061056 := by decide
  rcases family_descends (prefixWord ++ tailWord_5061056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5061059 : List Nat := [1, 1, 1, 3, 1, 1, 3, 3, 3, 1, 5]
def baseStart_5061059 : Nat := 118140960795 + 5061059 * 2 ^ 59
def prefixEnd_5061059 : Nat := 4983230072969 + 3 ^ 40 * 5061059 * 2
def baseEnd_5061059 : Nat := 2598755887763419317087119

theorem tailTrace_5061059 : CollatzResearch.WordTrace tailWord_5061059 prefixEnd_5061059 2598755887763419317087119 := by
  unfold tailWord_5061059
  simp only [CollatzResearch.WordTrace]
  refine ⟨184591986571655077907090231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123061324381103385271393487 184591986571655077907090231)
  ·
    refine ⟨276887979857482616860635347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184591986571655077907090231 276887979857482616860635347)
    ·
      refine ⟨415331969786223925290953021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 276887979857482616860635347 415331969786223925290953021)
      ·
        refine ⟨155749488669833971984107383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 415331969786223925290953021 155749488669833971984107383)
        ·
          refine ⟨233624233004750957976161075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155749488669833971984107383 233624233004750957976161075)
          ·
            refine ⟨350436349507126436964241613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 233624233004750957976161075 350436349507126436964241613)
            ·
              refine ⟨131413631065172413861590605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 350436349507126436964241613 131413631065172413861590605)
              ·
                refine ⟨49280111649439655198096477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 131413631065172413861590605 49280111649439655198096477)
                ·
                  refine ⟨18480041868539870699286179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49280111649439655198096477 18480041868539870699286179)
                  ·
                    refine ⟨27720062802809806048929269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18480041868539870699286179 27720062802809806048929269)
                    ·
                      refine ⟨2598755887763419317087119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27720062802809806048929269 2598755887763419317087119)
                      ·
                        rfl

theorem cell23_5061059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 3, 3, 1, 5].length) (baseStart_5061059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5061059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5061059 prefixEnd_5061059 := by exact prefixLift 5061059
  have htrace : WordTrace (prefixWord ++ tailWord_5061059) baseStart_5061059 baseEnd_5061059 := by
    simpa [prefixWord, tailWord_5061059, baseEnd_5061059] using wordTrace_append hprefix tailTrace_5061059
  have hstable : (prefixWord ++ tailWord_5061059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5061059).length < 2 ^ (prefixWord ++ tailWord_5061059).sum := by decide
  have hdescent : baseEnd_5061059 < baseStart_5061059 := by decide
  rcases family_descends (prefixWord ++ tailWord_5061059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5061066 : List Nat := [3, 1, 2, 1, 2, 2, 4, 1, 1, 6]
def baseStart_5061066 : Nat := 118140960795 + 5061066 * 2 ^ 59
def prefixEnd_5061066 : Nat := 4983230072969 + 3 ^ 40 * 5061066 * 2
def baseEnd_5061066 : Nat := 866253160709333596566529

theorem tailTrace_5061066 : CollatzResearch.WordTrace tailWord_5061066 prefixEnd_5061066 866253160709333596566529 := by
  unfold tailWord_5061066
  simp only [CollatzResearch.WordTrace]
  refine ⟨46148060470657429525648763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123061494588419812068396701 46148060470657429525648763)
  ·
    refine ⟨69222090705986144288473145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46148060470657429525648763 69222090705986144288473145)
    ·
      refine ⟨51916568029489608216354859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69222090705986144288473145 51916568029489608216354859)
      ·
        refine ⟨77874852044234412324532289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51916568029489608216354859 77874852044234412324532289)
        ·
          refine ⟨58406139033175809243399217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77874852044234412324532289 58406139033175809243399217)
          ·
            refine ⟨43804604274881856932549413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58406139033175809243399217 43804604274881856932549413)
            ·
              refine ⟨8213363301540348174853015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43804604274881856932549413 8213363301540348174853015)
              ·
                refine ⟨12320044952310522262279523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8213363301540348174853015 12320044952310522262279523)
                ·
                  refine ⟨18480067428465783393419285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12320044952310522262279523 18480067428465783393419285)
                  ·
                    refine ⟨866253160709333596566529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18480067428465783393419285 866253160709333596566529)
                    ·
                      rfl

theorem cell23_5061066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 4, 1, 1, 6].length) (baseStart_5061066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5061066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5061066 prefixEnd_5061066 := by exact prefixLift 5061066
  have htrace : WordTrace (prefixWord ++ tailWord_5061066) baseStart_5061066 baseEnd_5061066 := by
    simpa [prefixWord, tailWord_5061066, baseEnd_5061066] using wordTrace_append hprefix tailTrace_5061066
  have hstable : (prefixWord ++ tailWord_5061066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5061066).length < 2 ^ (prefixWord ++ tailWord_5061066).sum := by decide
  have hdescent : baseEnd_5061066 < baseStart_5061066 := by decide
  rcases family_descends (prefixWord ++ tailWord_5061066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5061129 : List Nat := [1, 2, 1, 1, 3, 1, 2, 1, 1, 2, 8]
def baseStart_5061129 : Nat := 118140960795 + 5061129 * 2 ^ 59
def prefixEnd_5061129 : Nat := 4983230072969 + 3 ^ 40 * 5061129 * 2
def baseEnd_5061129 : Nat := 2598791831409234043211797

theorem tailTrace_5061129 : CollatzResearch.WordTrace tailWord_5061129 prefixEnd_5061129 2598791831409234043211797 := by
  unfold tailWord_5061129
  simp only [CollatzResearch.WordTrace]
  refine ⟨184594539681401479862138441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123063026454267653241425627 184594539681401479862138441)
  ·
    refine ⟨138445904761051109896603831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184594539681401479862138441 138445904761051109896603831)
    ·
      refine ⟨207668857141576664844905747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138445904761051109896603831 207668857141576664844905747)
      ·
        refine ⟨311503285712364997267358621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 207668857141576664844905747 311503285712364997267358621)
        ·
          refine ⟨116813732142136873975259483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 311503285712364997267358621 116813732142136873975259483)
          ·
            refine ⟨175220598213205310962889225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116813732142136873975259483 175220598213205310962889225)
            ·
              refine ⟨131415448659903983222166919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 175220598213205310962889225 131415448659903983222166919)
              ·
                refine ⟨197123172989855974833250379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 131415448659903983222166919 197123172989855974833250379)
                ·
                  refine ⟨295684759484783962249875569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 197123172989855974833250379 295684759484783962249875569)
                  ·
                    refine ⟨221763569613587971687406677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 295684759484783962249875569 221763569613587971687406677)
                    ·
                      refine ⟨2598791831409234043211797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 221763569613587971687406677 2598791831409234043211797)
                      ·
                        rfl

theorem cell23_5061129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 2, 8].length) (baseStart_5061129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5061129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5061129 prefixEnd_5061129 := by exact prefixLift 5061129
  have htrace : WordTrace (prefixWord ++ tailWord_5061129) baseStart_5061129 baseEnd_5061129 := by
    simpa [prefixWord, tailWord_5061129, baseEnd_5061129] using wordTrace_append hprefix tailTrace_5061129
  have hstable : (prefixWord ++ tailWord_5061129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5061129).length < 2 ^ (prefixWord ++ tailWord_5061129).sum := by decide
  have hdescent : baseEnd_5061129 < baseStart_5061129 := by decide
  rcases family_descends (prefixWord ++ tailWord_5061129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5061174 : List Nat := [5, 1, 2, 1, 2, 1, 4, 1, 2, 1, 3]
def baseStart_5061174 : Nat := 118140960795 + 5061174 * 2 ^ 59
def prefixEnd_5061174 : Nat := 4983230072969 + 3 ^ 40 * 5061174 * 2
def baseEnd_5061174 : Nat := 2598814938038686367149091

theorem tailTrace_5061174 : CollatzResearch.WordTrace tailWord_5061174 prefixEnd_5061174 2598814938038686367149091 := by
  unfold tailWord_5061174
  simp only [CollatzResearch.WordTrace]
  refine ⟨11537261310389903284220411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 123064120644158968365017717 11537261310389903284220411)
  ·
    refine ⟨17305891965584854926330617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11537261310389903284220411 17305891965584854926330617)
    ·
      refine ⟨12979418974188641194747963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17305891965584854926330617 12979418974188641194747963)
      ·
        refine ⟨19469128461282961792121945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12979418974188641194747963 19469128461282961792121945)
        ·
          refine ⟨14601846345962221344091459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19469128461282961792121945 14601846345962221344091459)
          ·
            refine ⟨21902769518943332016137189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14601846345962221344091459 21902769518943332016137189)
            ·
              refine ⟨4106769284801874753025723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21902769518943332016137189 4106769284801874753025723)
              ·
                refine ⟨6160153927202812129538585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4106769284801874753025723 6160153927202812129538585)
                ·
                  refine ⟨4620115445402109097153939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6160153927202812129538585 4620115445402109097153939)
                  ·
                    refine ⟨6930173168103163645730909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4620115445402109097153939 6930173168103163645730909)
                    ·
                      refine ⟨2598814938038686367149091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6930173168103163645730909 2598814938038686367149091)
                      ·
                        rfl

theorem cell23_5061174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 4, 1, 2, 1, 3].length) (baseStart_5061174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5061174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5061174 prefixEnd_5061174 := by exact prefixLift 5061174
  have htrace : WordTrace (prefixWord ++ tailWord_5061174) baseStart_5061174 baseEnd_5061174 := by
    simpa [prefixWord, tailWord_5061174, baseEnd_5061174] using wordTrace_append hprefix tailTrace_5061174
  have hstable : (prefixWord ++ tailWord_5061174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5061174).length < 2 ^ (prefixWord ++ tailWord_5061174).sum := by decide
  have hdescent : baseEnd_5061174 < baseStart_5061174 := by decide
  rcases family_descends (prefixWord ++ tailWord_5061174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5061176 : List Nat := [2, 1, 2, 1, 4, 1, 2, 1, 1, 4, 4]
def baseStart_5061176 : Nat := 118140960795 + 5061176 * 2 ^ 59
def prefixEnd_5061176 : Nat := 4983230072969 + 3 ^ 40 * 5061176 * 2
def baseEnd_5061176 : Nat := 2598815964999995359324081

theorem tailTrace_5061176 : CollatzResearch.WordTrace tailWord_5061176 prefixEnd_5061176 2598815964999995359324081 := by
  unfold tailWord_5061176
  simp only [CollatzResearch.WordTrace]
  refine ⟨92298126956115603444549691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123064169274820804592732921 92298126956115603444549691)
  ·
    refine ⟨138447190434173405166824537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92298126956115603444549691 138447190434173405166824537)
    ·
      refine ⟨103835392825630053875118403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138447190434173405166824537 103835392825630053875118403)
      ·
        refine ⟨155753089238445080812677605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103835392825630053875118403 155753089238445080812677605)
        ·
          refine ⟨29203704232208452652377051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 155753089238445080812677605 29203704232208452652377051)
          ·
            refine ⟨43805556348312678978565577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29203704232208452652377051 43805556348312678978565577)
            ·
              refine ⟨32854167261234509233924183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43805556348312678978565577 32854167261234509233924183)
              ·
                refine ⟨49281250891851763850886275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32854167261234509233924183 49281250891851763850886275)
                ·
                  refine ⟨73921876337777645776329413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49281250891851763850886275 73921876337777645776329413)
                  ·
                    refine ⟨13860351813333308583061765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 73921876337777645776329413 13860351813333308583061765)
                    ·
                      refine ⟨2598815964999995359324081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13860351813333308583061765 2598815964999995359324081)
                      ·
                        rfl

theorem cell23_5061176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 1, 1, 4, 4].length) (baseStart_5061176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5061176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5061176 prefixEnd_5061176 := by exact prefixLift 5061176
  have htrace : WordTrace (prefixWord ++ tailWord_5061176) baseStart_5061176 baseEnd_5061176 := by
    simpa [prefixWord, tailWord_5061176, baseEnd_5061176] using wordTrace_append hprefix tailTrace_5061176
  have hstable : (prefixWord ++ tailWord_5061176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5061176).length < 2 ^ (prefixWord ++ tailWord_5061176).sum := by decide
  have hdescent : baseEnd_5061176 < baseStart_5061176 := by decide
  rcases family_descends (prefixWord ++ tailWord_5061176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5061197 : List Nat := [1, 6, 1, 1, 2, 2, 1, 2, 1, 4, 2]
def baseStart_5061197 : Nat := 118140960795 + 5061197 * 2 ^ 59
def prefixEnd_5061197 : Nat := 4983230072969 + 3 ^ 40 * 5061197 * 2
def baseEnd_5061197 : Nat := 2598826748093739777161485

theorem tailTrace_5061197 : CollatzResearch.WordTrace tailWord_5061197 prefixEnd_5061197 2598826748093739777161485 := by
  unfold tailWord_5061197
  simp only [CollatzResearch.WordTrace]
  refine ⟨184597019845155127475613845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123064679896770084983742563 184597019845155127475613845)
  ·
    refine ⟨8652985305241646600419399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 184597019845155127475613845 8652985305241646600419399)
    ·
      refine ⟨12979477957862469900629099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8652985305241646600419399 12979477957862469900629099)
      ·
        refine ⟨19469216936793704850943649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12979477957862469900629099 19469216936793704850943649)
        ·
          refine ⟨14601912702595278638207737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19469216936793704850943649 14601912702595278638207737)
          ·
            refine ⟨10951434526946458978655803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14601912702595278638207737 10951434526946458978655803)
            ·
              refine ⟨16427151790419688467983705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10951434526946458978655803 16427151790419688467983705)
              ·
                refine ⟨12320363842814766350987779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16427151790419688467983705 12320363842814766350987779)
                ·
                  refine ⟨18480545764222149526481669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12320363842814766350987779 18480545764222149526481669)
                  ·
                    refine ⟨3465102330791653036215313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18480545764222149526481669 3465102330791653036215313)
                    ·
                      refine ⟨2598826748093739777161485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3465102330791653036215313 2598826748093739777161485)
                      ·
                        rfl

theorem cell23_5061197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 2, 1, 4, 2].length) (baseStart_5061197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5061197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5061197 prefixEnd_5061197 := by exact prefixLift 5061197
  have htrace : WordTrace (prefixWord ++ tailWord_5061197) baseStart_5061197 baseEnd_5061197 := by
    simpa [prefixWord, tailWord_5061197, baseEnd_5061197] using wordTrace_append hprefix tailTrace_5061197
  have hstable : (prefixWord ++ tailWord_5061197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5061197).length < 2 ^ (prefixWord ++ tailWord_5061197).sum := by decide
  have hdescent : baseEnd_5061197 < baseStart_5061197 := by decide
  rcases family_descends (prefixWord ++ tailWord_5061197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5061230 : List Nat := [4, 1, 2, 2, 2, 2, 1, 1, 2, 3, 3]
def baseStart_5061230 : Nat := 118140960795 + 5061230 * 2 ^ 59
def prefixEnd_5061230 : Nat := 4983230072969 + 3 ^ 40 * 5061230 * 2
def baseEnd_5061230 : Nat := 2598843692955338148048833

theorem tailTrace_5061230 : CollatzResearch.WordTrace tailWord_5061230 prefixEnd_5061230 2598843692955338148048833 := by
  unfold tailWord_5061230
  simp only [CollatzResearch.WordTrace]
  refine ⟨23074777931754446763945643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 123065482302690382741043429 23074777931754446763945643)
  ·
    refine ⟨34612166897631670145918465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23074777931754446763945643 34612166897631670145918465)
    ·
      refine ⟨25959125173223752609438849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34612166897631670145918465 25959125173223752609438849)
      ·
        refine ⟨19469343879917814457079137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25959125173223752609438849 19469343879917814457079137)
        ·
          refine ⟨14602007909938360842809353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19469343879917814457079137 14602007909938360842809353)
          ·
            refine ⟨10951505932453770632107015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14602007909938360842809353 10951505932453770632107015)
            ·
              refine ⟨16427258898680655948160523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10951505932453770632107015 16427258898680655948160523)
              ·
                refine ⟨24640888348020983922240785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16427258898680655948160523 24640888348020983922240785)
                ·
                  refine ⟨18480666261015737941680589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24640888348020983922240785 18480666261015737941680589)
                  ·
                    refine ⟨6930249847880901728130221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18480666261015737941680589 6930249847880901728130221)
                    ·
                      refine ⟨2598843692955338148048833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6930249847880901728130221 2598843692955338148048833)
                      ·
                        rfl

theorem cell23_5061230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 1, 2, 3, 3].length) (baseStart_5061230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5061230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5061230 prefixEnd_5061230 := by exact prefixLift 5061230
  have htrace : WordTrace (prefixWord ++ tailWord_5061230) baseStart_5061230 baseEnd_5061230 := by
    simpa [prefixWord, tailWord_5061230, baseEnd_5061230] using wordTrace_append hprefix tailTrace_5061230
  have hstable : (prefixWord ++ tailWord_5061230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5061230).length < 2 ^ (prefixWord ++ tailWord_5061230).sum := by decide
  have hdescent : baseEnd_5061230 < baseStart_5061230 := by decide
  rcases family_descends (prefixWord ++ tailWord_5061230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5061253 : List Nat := [1, 3, 1, 1, 4, 3, 1, 1, 1, 3, 4]
def baseStart_5061253 : Nat := 118140960795 + 5061253 * 2 ^ 59
def prefixEnd_5061253 : Nat := 4983230072969 + 3 ^ 40 * 5061253 * 2
def baseEnd_5061253 : Nat := 2598855503010391558061227

theorem tailTrace_5061253 : CollatzResearch.WordTrace tailWord_5061253 prefixEnd_5061253 2598855503010391558061227 := by
  unfold tailWord_5061253
  simp only [CollatzResearch.WordTrace]
  refine ⟨184599062332952249039652413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123066041555301499359768275 184599062332952249039652413)
  ·
    refine ⟨69224648374857093389869655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 184599062332952249039652413 69224648374857093389869655)
    ·
      refine ⟨103836972562285640084804483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69224648374857093389869655 103836972562285640084804483)
      ·
        refine ⟨155755458843428460127206725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103836972562285640084804483 155755458843428460127206725)
        ·
          refine ⟨29204148533142836273851261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 155755458843428460127206725 29204148533142836273851261)
          ·
            refine ⟨10951555699928563602694223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29204148533142836273851261 10951555699928563602694223)
            ·
              refine ⟨16427333549892845404041335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10951555699928563602694223 16427333549892845404041335)
              ·
                refine ⟨24641000324839268106062003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16427333549892845404041335 24641000324839268106062003)
                ·
                  refine ⟨36961500487258902159093005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24641000324839268106062003 36961500487258902159093005)
                  ·
                    refine ⟨13860562682722088309659877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36961500487258902159093005 13860562682722088309659877)
                    ·
                      refine ⟨2598855503010391558061227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13860562682722088309659877 2598855503010391558061227)
                      ·
                        rfl

theorem cell23_5061253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 1, 1, 3, 4].length) (baseStart_5061253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5061253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5061253 prefixEnd_5061253 := by exact prefixLift 5061253
  have htrace : WordTrace (prefixWord ++ tailWord_5061253) baseStart_5061253 baseEnd_5061253 := by
    simpa [prefixWord, tailWord_5061253, baseEnd_5061253] using wordTrace_append hprefix tailTrace_5061253
  have hstable : (prefixWord ++ tailWord_5061253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5061253).length < 2 ^ (prefixWord ++ tailWord_5061253).sum := by decide
  have hdescent : baseEnd_5061253 < baseStart_5061253 := by decide
  rcases family_descends (prefixWord ++ tailWord_5061253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5061273 : List Nat := [1, 2, 1, 2, 1, 2, 4, 1, 4, 2, 3]
def baseStart_5061273 : Nat := 118140960795 + 5061273 * 2 ^ 59
def prefixEnd_5061273 : Nat := 4983230072969 + 3 ^ 40 * 5061273 * 2
def baseEnd_5061273 : Nat := 2598865772623481479811135

theorem tailTrace_5061273 : CollatzResearch.WordTrace tailWord_5061273 prefixEnd_5061273 2598865772623481479811135 := by
  unfold tailWord_5061273
  simp only [CollatzResearch.WordTrace]
  refine ⟨184599791792879792455380473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123066527861919861636920315 184599791792879792455380473)
  ·
    refine ⟨138449843844659844341535355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184599791792879792455380473 138449843844659844341535355)
    ·
      refine ⟨207674765766989766512303033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138449843844659844341535355 207674765766989766512303033)
      ·
        refine ⟨155756074325242324884227275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 207674765766989766512303033 155756074325242324884227275)
        ·
          refine ⟨233634111487863487326340913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155756074325242324884227275 233634111487863487326340913)
          ·
            refine ⟨175225583615897615494755685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 233634111487863487326340913 175225583615897615494755685)
            ·
              refine ⟨32854796927980802905266691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 175225583615897615494755685 32854796927980802905266691)
              ·
                refine ⟨49282195391971204357900037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32854796927980802905266691 49282195391971204357900037)
                ·
                  refine ⟨9240411635994600817106257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49282195391971204357900037 9240411635994600817106257)
                  ·
                    refine ⟨6930308726995950612829693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9240411635994600817106257 6930308726995950612829693)
                    ·
                      refine ⟨2598865772623481479811135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6930308726995950612829693 2598865772623481479811135)
                      ·
                        rfl

theorem cell23_5061273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 1, 4, 2, 3].length) (baseStart_5061273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5061273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5061273 prefixEnd_5061273 := by exact prefixLift 5061273
  have htrace : WordTrace (prefixWord ++ tailWord_5061273) baseStart_5061273 baseEnd_5061273 := by
    simpa [prefixWord, tailWord_5061273, baseEnd_5061273] using wordTrace_append hprefix tailTrace_5061273
  have hstable : (prefixWord ++ tailWord_5061273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5061273).length < 2 ^ (prefixWord ++ tailWord_5061273).sum := by decide
  have hdescent : baseEnd_5061273 < baseStart_5061273 := by decide
  rcases family_descends (prefixWord ++ tailWord_5061273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5061296 : List Nat := [2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 6]
def baseStart_5061296 : Nat := 118140960795 + 5061296 * 2 ^ 59
def prefixEnd_5061296 : Nat := 4983230072969 + 3 ^ 40 * 5061296 * 2
def baseEnd_5061296 : Nat := 2598877582678534889823529

theorem tailTrace_5061296 : CollatzResearch.WordTrace tailWord_5061296 prefixEnd_5061296 2598877582678534889823529 := by
  unfold tailWord_5061296
  simp only [CollatzResearch.WordTrace]
  refine ⟨92300315335898233691733871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123067087114530978255645161 92300315335898233691733871)
  ·
    refine ⟨138450473003847350537600807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92300315335898233691733871 138450473003847350537600807)
    ·
      refine ⟨207675709505771025806401211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138450473003847350537600807 207675709505771025806401211)
      ·
        refine ⟨311513564258656538709601817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 207675709505771025806401211 311513564258656538709601817)
        ·
          refine ⟨233635173193992404032201363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 311513564258656538709601817 233635173193992404032201363)
          ·
            refine ⟨350452759790988606048302045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 233635173193992404032201363 350452759790988606048302045)
            ·
              refine ⟨131419784921620727268113267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 350452759790988606048302045 131419784921620727268113267)
              ·
                refine ⟨197129677382431090902169901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 131419784921620727268113267 197129677382431090902169901)
                ·
                  refine ⟨73923629018411659088313713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 197129677382431090902169901 73923629018411659088313713)
                  ·
                    refine ⟨55442721763808744316235285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 73923629018411659088313713 55442721763808744316235285)
                    ·
                      refine ⟨2598877582678534889823529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 55442721763808744316235285 2598877582678534889823529)
                      ·
                        rfl

theorem cell23_5061296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 6].length) (baseStart_5061296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5061296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5061296 prefixEnd_5061296 := by exact prefixLift 5061296
  have htrace : WordTrace (prefixWord ++ tailWord_5061296) baseStart_5061296 baseEnd_5061296 := by
    simpa [prefixWord, tailWord_5061296, baseEnd_5061296] using wordTrace_append hprefix tailTrace_5061296
  have hstable : (prefixWord ++ tailWord_5061296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5061296).length < 2 ^ (prefixWord ++ tailWord_5061296).sum := by decide
  have hdescent : baseEnd_5061296 < baseStart_5061296 := by decide
  rcases family_descends (prefixWord ++ tailWord_5061296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5061374 : List Nat := [4, 2, 2, 1, 2, 2, 3, 1, 1, 5]
def baseStart_5061374 : Nat := 118140960795 + 5061374 * 2 ^ 59
def prefixEnd_5061374 : Nat := 4983230072969 + 3 ^ 40 * 5061374 * 2
def baseEnd_5061374 : Nat := 866305878056528528216057

theorem tailTrace_5061374 : CollatzResearch.WordTrace tailWord_5061374 prefixEnd_5061374 866305878056528528216057 := by
  unfold tailWord_5061374
  simp only [CollatzResearch.WordTrace]
  refine ⟨23075434445689235838100897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 123068983710342591136538117 23075434445689235838100897)
  ·
    refine ⟨17306575834266926878575673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23075434445689235838100897 17306575834266926878575673)
    ·
      refine ⟨12979931875700195158931755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17306575834266926878575673 12979931875700195158931755)
      ·
        refine ⟨19469897813550292738397633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12979931875700195158931755 19469897813550292738397633)
        ·
          refine ⟨14602423360162719553798225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19469897813550292738397633 14602423360162719553798225)
          ·
            refine ⟨10951817520122039665348669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14602423360162719553798225 10951817520122039665348669)
            ·
              refine ⟨4106931570045764874505751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10951817520122039665348669 4106931570045764874505751)
              ·
                refine ⟨6160397355068647311758627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4106931570045764874505751 6160397355068647311758627)
                ·
                  refine ⟨9240596032602970967637941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6160397355068647311758627 9240596032602970967637941)
                  ·
                    refine ⟨866305878056528528216057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9240596032602970967637941 866305878056528528216057)
                    ·
                      rfl

theorem cell23_5061374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 3, 1, 1, 5].length) (baseStart_5061374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5061374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5061374 prefixEnd_5061374 := by exact prefixLift 5061374
  have htrace : WordTrace (prefixWord ++ tailWord_5061374) baseStart_5061374 baseEnd_5061374 := by
    simpa [prefixWord, tailWord_5061374, baseEnd_5061374] using wordTrace_append hprefix tailTrace_5061374
  have hstable : (prefixWord ++ tailWord_5061374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5061374).length < 2 ^ (prefixWord ++ tailWord_5061374).sum := by decide
  have hdescent : baseEnd_5061374 < baseStart_5061374 := by decide
  rcases family_descends (prefixWord ++ tailWord_5061374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5061383 : List Nat := [1, 1, 4, 4, 1, 12]
def baseStart_5061383 : Nat := 118140960795 + 5061383 * 2 ^ 59
def prefixEnd_5061383 : Nat := 4983230072969 + 3 ^ 40 * 5061383 * 2
def baseEnd_5061383 : Nat := 10695153314796197734303

theorem tailTrace_5061383 : CollatzResearch.WordTrace tailWord_5061383 prefixEnd_5061383 10695153314796197734303 := by
  unfold tailWord_5061383
  simp only [CollatzResearch.WordTrace]
  refine ⟨184603803822481281241884803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123069202548320854161256535 184603803822481281241884803)
  ·
    refine ⟨276905705733721921862827205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184603803822481281241884803 276905705733721921862827205)
    ·
      refine ⟨51919819825072860349280101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 276905705733721921862827205 51919819825072860349280101)
      ·
        refine ⟨9734966217201161315490019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51919819825072860349280101 9734966217201161315490019)
        ·
          refine ⟨14602449325801741973235029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9734966217201161315490019 14602449325801741973235029)
          ·
            refine ⟨10695153314796197734303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 14602449325801741973235029 10695153314796197734303)
            ·
              rfl

theorem cell23_5061383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 12].length) (baseStart_5061383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5061383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5061383 prefixEnd_5061383 := by exact prefixLift 5061383
  have htrace : WordTrace (prefixWord ++ tailWord_5061383) baseStart_5061383 baseEnd_5061383 := by
    simpa [prefixWord, tailWord_5061383, baseEnd_5061383] using wordTrace_append hprefix tailTrace_5061383
  have hstable : (prefixWord ++ tailWord_5061383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5061383).length < 2 ^ (prefixWord ++ tailWord_5061383).sum := by decide
  have hdescent : baseEnd_5061383 < baseStart_5061383 := by decide
  rcases family_descends (prefixWord ++ tailWord_5061383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5061413 : List Nat := [1, 3, 1, 2, 3, 1, 1, 2, 2, 7]
def baseStart_5061413 : Nat := 118140960795 + 5061413 * 2 ^ 59
def prefixEnd_5061413 : Nat := 4983230072969 + 3 ^ 40 * 5061413 * 2
def baseEnd_5061413 : Nat := 866312553305036977353497

theorem tailTrace_5061413 : CollatzResearch.WordTrace tailWord_5061413 prefixEnd_5061413 866312553305036977353497 := by
  unfold tailWord_5061413
  simp only [CollatzResearch.WordTrace]
  refine ⟨184604898012372596365476893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123069932008248397576984595 184604898012372596365476893)
  ·
    refine ⟨69226836754639723637053835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 184604898012372596365476893 69226836754639723637053835)
    ·
      refine ⟨103840255131959585455580753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69226836754639723637053835 103840255131959585455580753)
      ·
        refine ⟨77880191348969689091685565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103840255131959585455580753 77880191348969689091685565)
        ·
          refine ⟨29205071755863633409382087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77880191348969689091685565 29205071755863633409382087)
          ·
            refine ⟨43807607633795450114073131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29205071755863633409382087 43807607633795450114073131)
            ·
              refine ⟨65711411450693175171109697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43807607633795450114073131 65711411450693175171109697)
              ·
                refine ⟨49283558588019881378332273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65711411450693175171109697 49283558588019881378332273)
                ·
                  refine ⟨36962668941014911033749205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49283558588019881378332273 36962668941014911033749205)
                  ·
                    refine ⟨866312553305036977353497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36962668941014911033749205 866312553305036977353497)
                    ·
                      rfl

theorem cell23_5061413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 2, 2, 7].length) (baseStart_5061413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5061413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5061413 prefixEnd_5061413 := by exact prefixLift 5061413
  have htrace : WordTrace (prefixWord ++ tailWord_5061413) baseStart_5061413 baseEnd_5061413 := by
    simpa [prefixWord, tailWord_5061413, baseEnd_5061413] using wordTrace_append hprefix tailTrace_5061413
  have hstable : (prefixWord ++ tailWord_5061413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5061413).length < 2 ^ (prefixWord ++ tailWord_5061413).sum := by decide
  have hdescent : baseEnd_5061413 < baseStart_5061413 := by decide
  rcases family_descends (prefixWord ++ tailWord_5061413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5061428 : List Nat := [2, 5, 1, 1, 4, 1, 2, 1, 1, 1, 4]
def baseStart_5061428 : Nat := 118140960795 + 5061428 * 2 ^ 59
def prefixEnd_5061428 : Nat := 4983230072969 + 3 ^ 40 * 5061428 * 2
def baseEnd_5061428 : Nat := 2598945362124928373372923

theorem tailTrace_5061428 : CollatzResearch.WordTrace tailWord_5061428 prefixEnd_5061428 2598945362124928373372923 := by
  unfold tailWord_5061428
  simp only [CollatzResearch.WordTrace]
  refine ⟨92302722553659126963636469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123070296738212169284848625 92302722553659126963636469)
  ·
    refine ⟨8653380239405543152840919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 92302722553659126963636469 8653380239405543152840919)
    ·
      refine ⟨12980070359108314729261379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8653380239405543152840919 12980070359108314729261379)
      ·
        refine ⟨19470105538662472093892069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12980070359108314729261379 19470105538662472093892069)
        ·
          refine ⟨3650644788499213517604763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19470105538662472093892069 3650644788499213517604763)
          ·
            refine ⟨5475967182748820276407145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3650644788499213517604763 5475967182748820276407145)
            ·
              refine ⟨4106975387061615207305359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5475967182748820276407145 4106975387061615207305359)
              ·
                refine ⟨6160463080592422810958039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4106975387061615207305359 6160463080592422810958039)
                ·
                  refine ⟨9240694620888634216437059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6160463080592422810958039 9240694620888634216437059)
                  ·
                    refine ⟨13861041931332951324655589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9240694620888634216437059 13861041931332951324655589)
                    ·
                      refine ⟨2598945362124928373372923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13861041931332951324655589 2598945362124928373372923)
                      ·
                        rfl

theorem cell23_5061428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 2, 1, 1, 1, 4].length) (baseStart_5061428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5061428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5061428 prefixEnd_5061428 := by exact prefixLift 5061428
  have htrace : WordTrace (prefixWord ++ tailWord_5061428) baseStart_5061428 baseEnd_5061428 := by
    simpa [prefixWord, tailWord_5061428, baseEnd_5061428] using wordTrace_append hprefix tailTrace_5061428
  have hstable : (prefixWord ++ tailWord_5061428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5061428).length < 2 ^ (prefixWord ++ tailWord_5061428).sum := by decide
  have hdescent : baseEnd_5061428 < baseStart_5061428 := by decide
  rcases family_descends (prefixWord ++ tailWord_5061428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5061443 : List Nat := [1, 1, 1, 3, 1, 4, 1, 1, 4, 6]
def baseStart_5061443 : Nat := 118140960795 + 5061443 * 2 ^ 59
def prefixEnd_5061443 : Nat := 4983230072969 + 3 ^ 40 * 5061443 * 2
def baseEnd_5061443 : Nat := 866317688111581938228451

theorem tailTrace_5061443 : CollatzResearch.WordTrace tailWord_5061443 prefixEnd_5061443 866317688111581938228451 := by
  unfold tailWord_5061443
  simp only [CollatzResearch.WordTrace]
  refine ⟨184605992202263911489068983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123070661468175940992712655 184605992202263911489068983)
  ·
    refine ⟨276908988303395867233603475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184605992202263911489068983 276908988303395867233603475)
    ·
      refine ⟨415363482455093800850405213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 276908988303395867233603475 415363482455093800850405213)
      ·
        refine ⟨155761305920660175318901955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 415363482455093800850405213 155761305920660175318901955)
        ·
          refine ⟨233641958880990262978352933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155761305920660175318901955 233641958880990262978352933)
          ·
            refine ⟨43807867290185674308441175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 233641958880990262978352933 43807867290185674308441175)
            ·
              refine ⟨65711800935278511462661763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43807867290185674308441175 65711800935278511462661763)
              ·
                refine ⟨98567701402917767193992645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65711800935278511462661763 98567701402917767193992645)
                ·
                  refine ⟨18481444013047081348873621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 98567701402917767193992645 18481444013047081348873621)
                  ·
                    refine ⟨866317688111581938228451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18481444013047081348873621 866317688111581938228451)
                    ·
                      rfl

theorem cell23_5061443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 1, 4, 6].length) (baseStart_5061443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5061443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5061443 prefixEnd_5061443 := by exact prefixLift 5061443
  have htrace : WordTrace (prefixWord ++ tailWord_5061443) baseStart_5061443 baseEnd_5061443 := by
    simpa [prefixWord, tailWord_5061443, baseEnd_5061443] using wordTrace_append hprefix tailTrace_5061443
  have hstable : (prefixWord ++ tailWord_5061443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5061443).length < 2 ^ (prefixWord ++ tailWord_5061443).sum := by decide
  have hdescent : baseEnd_5061443 < baseStart_5061443 := by decide
  rcases family_descends (prefixWord ++ tailWord_5061443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5061473 : List Nat := [1, 2, 3, 1, 1, 1, 2, 3, 9]
def baseStart_5061473 : Nat := 118140960795 + 5061473 * 2 ^ 59
def prefixEnd_5061473 : Nat := 4983230072969 + 3 ^ 40 * 5061473 * 2
def baseEnd_5061473 : Nat := 288774274306042299701135

theorem tailTrace_5061473 : CollatzResearch.WordTrace tailWord_5061473 prefixEnd_5061473 288774274306042299701135 := by
  unfold tailWord_5061473
  simp only [CollatzResearch.WordTrace]
  refine ⟨184607086392155226612661073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123071390928103484408440715 184607086392155226612661073)
  ·
    refine ⟨138455314794116419959495805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184607086392155226612661073 138455314794116419959495805)
    ·
      refine ⟨51920743047793657484810927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 138455314794116419959495805 51920743047793657484810927)
      ·
        refine ⟨77881114571690486227216391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51920743047793657484810927 77881114571690486227216391)
        ·
          refine ⟨116821671857535729340824587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77881114571690486227216391 116821671857535729340824587)
          ·
            refine ⟨175232507786303594011236881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116821671857535729340824587 175232507786303594011236881)
            ·
              refine ⟨131424380839727695508427661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 175232507786303594011236881 131424380839727695508427661)
              ·
                refine ⟨49284142814897885815660373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 131424380839727695508427661 49284142814897885815660373)
                ·
                  refine ⟨288774274306042299701135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 49284142814897885815660373 288774274306042299701135)
                  ·
                    rfl

theorem cell23_5061473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 3, 9].length) (baseStart_5061473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5061473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5061473 prefixEnd_5061473 := by exact prefixLift 5061473
  have htrace : WordTrace (prefixWord ++ tailWord_5061473) baseStart_5061473 baseEnd_5061473 := by
    simpa [prefixWord, tailWord_5061473, baseEnd_5061473] using wordTrace_append hprefix tailTrace_5061473
  have hstable : (prefixWord ++ tailWord_5061473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5061473).length < 2 ^ (prefixWord ++ tailWord_5061473).sum := by decide
  have hdescent : baseEnd_5061473 < baseStart_5061473 := by decide
  rcases family_descends (prefixWord ++ tailWord_5061473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5061500 : List Nat := [2, 2, 2, 1, 1, 1, 1, 3, 4, 3, 3]
def baseStart_5061500 : Nat := 118140960795 + 5061500 * 2 ^ 59
def prefixEnd_5061500 : Nat := 4983230072969 + 3 ^ 40 * 5061500 * 2
def baseEnd_5061500 : Nat := 2598982332732052091672591

theorem tailTrace_5061500 : CollatzResearch.WordTrace tailWord_5061500 prefixEnd_5061500 2598982332732052091672591 := by
  unfold tailWord_5061500
  simp only [CollatzResearch.WordTrace]
  refine ⟨92304035581528705111946977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123072047442038273482595969 92304035581528705111946977)
  ·
    refine ⟨69228026686146528833960233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92304035581528705111946977 69228026686146528833960233)
    ·
      refine ⟨51921020014609896625470175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69228026686146528833960233 51921020014609896625470175)
      ·
        refine ⟨77881530021914844938205263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51921020014609896625470175 77881530021914844938205263)
        ·
          refine ⟨116822295032872267407307895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77881530021914844938205263 116822295032872267407307895)
          ·
            refine ⟨175233442549308401110961843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116822295032872267407307895 175233442549308401110961843)
            ·
              refine ⟨262850163823962601666442765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 175233442549308401110961843 262850163823962601666442765)
              ·
                refine ⟨98568811433985975624916037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 262850163823962601666442765 98568811433985975624916037)
                ·
                  refine ⟨18481652143872370429671757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 98568811433985975624916037 18481652143872370429671757)
                  ·
                    refine ⟨6930619553952138911126909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18481652143872370429671757 6930619553952138911126909)
                    ·
                      refine ⟨2598982332732052091672591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6930619553952138911126909 2598982332732052091672591)
                      ·
                        rfl

theorem cell23_5061500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 3, 4, 3, 3].length) (baseStart_5061500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5061500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5061500 prefixEnd_5061500 := by exact prefixLift 5061500
  have htrace : WordTrace (prefixWord ++ tailWord_5061500) baseStart_5061500 baseEnd_5061500 := by
    simpa [prefixWord, tailWord_5061500, baseEnd_5061500] using wordTrace_append hprefix tailTrace_5061500
  have hstable : (prefixWord ++ tailWord_5061500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5061500).length < 2 ^ (prefixWord ++ tailWord_5061500).sum := by decide
  have hdescent : baseEnd_5061500 < baseStart_5061500 := by decide
  rcases family_descends (prefixWord ++ tailWord_5061500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5061537 : List Nat := [1, 2, 3, 4, 1, 1, 1, 3, 2, 5]
def baseStart_5061537 : Nat := 118140960795 + 5061537 * 2 ^ 59
def prefixEnd_5061537 : Nat := 4983230072969 + 3 ^ 40 * 5061537 * 2
def baseEnd_5061537 : Nat := 866333777172089482303307

theorem tailTrace_5061537 : CollatzResearch.WordTrace tailWord_5061537 prefixEnd_5061537 866333777172089482303307 := by
  unfold tailWord_5061537
  simp only [CollatzResearch.WordTrace]
  refine ⟨184609420663923365542990865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123072947109282243695327243 184609420663923365542990865)
  ·
    refine ⟨138457065497942524157243149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184609420663923365542990865 138457065497942524157243149)
    ·
      refine ⟨51921399561728446558966181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 138457065497942524157243149 51921399561728446558966181)
      ·
        refine ⟨9735262417824083729806159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51921399561728446558966181 9735262417824083729806159)
        ·
          refine ⟨14602893626736125594709239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9735262417824083729806159 14602893626736125594709239)
          ·
            refine ⟨21904340440104188392063859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14602893626736125594709239 21904340440104188392063859)
            ·
              refine ⟨32856510660156282588095789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21904340440104188392063859 32856510660156282588095789)
              ·
                refine ⟨12321191497558605970535921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32856510660156282588095789 12321191497558605970535921)
                ·
                  refine ⟨9240893623168954477901941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12321191497558605970535921 9240893623168954477901941)
                  ·
                    refine ⟨866333777172089482303307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9240893623168954477901941 866333777172089482303307)
                    ·
                      rfl

theorem cell23_5061537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 3, 2, 5].length) (baseStart_5061537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5061537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5061537 prefixEnd_5061537 := by exact prefixLift 5061537
  have htrace : WordTrace (prefixWord ++ tailWord_5061537) baseStart_5061537 baseEnd_5061537 := by
    simpa [prefixWord, tailWord_5061537, baseEnd_5061537] using wordTrace_append hprefix tailTrace_5061537
  have hstable : (prefixWord ++ tailWord_5061537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5061537).length < 2 ^ (prefixWord ++ tailWord_5061537).sum := by decide
  have hdescent : baseEnd_5061537 < baseStart_5061537 := by decide
  rcases family_descends (prefixWord ++ tailWord_5061537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5061557 : List Nat := [1, 3, 3, 2, 1, 1, 1, 4, 2, 1, 4]
def baseStart_5061557 : Nat := 118140960795 + 5061557 * 2 ^ 59
def prefixEnd_5061557 : Nat := 4983230072969 + 3 ^ 40 * 5061557 * 2
def baseEnd_5061557 : Nat := 2599011601129358368659829

theorem tailTrace_5061557 : CollatzResearch.WordTrace tailWord_5061557 prefixEnd_5061557 2599011601129358368659829 := by
  unfold tailWord_5061557
  simp only [CollatzResearch.WordTrace]
  refine ⟨184610150123850908958718925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123073433415900605972479283 184610150123850908958718925)
  ·
    refine ⟨69228806296444090859519597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 184610150123850908958718925 69228806296444090859519597)
    ·
      refine ⟨25960802361166534072319849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69228806296444090859519597 25960802361166534072319849)
      ·
        refine ⟨19470601770874900554239887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25960802361166534072319849 19470601770874900554239887)
        ·
          refine ⟨29205902656312350831359831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19470601770874900554239887 29205902656312350831359831)
          ·
            refine ⟨43808853984468526247039747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29205902656312350831359831 43808853984468526247039747)
            ·
              refine ⟨65713280976702789370559621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43808853984468526247039747 65713280976702789370559621)
              ·
                refine ⟨12321240183131773006979929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 65713280976702789370559621 12321240183131773006979929)
                ·
                  refine ⟨9240930137348829755234947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12321240183131773006979929 9240930137348829755234947)
                  ·
                    refine ⟨13861395206023244632852421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9240930137348829755234947 13861395206023244632852421)
                    ·
                      refine ⟨2599011601129358368659829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13861395206023244632852421 2599011601129358368659829)
                      ·
                        rfl

theorem cell23_5061557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 4, 2, 1, 4].length) (baseStart_5061557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5061557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5061557 prefixEnd_5061557 := by exact prefixLift 5061557
  have htrace : WordTrace (prefixWord ++ tailWord_5061557) baseStart_5061557 baseEnd_5061557 := by
    simpa [prefixWord, tailWord_5061557, baseEnd_5061557] using wordTrace_append hprefix tailTrace_5061557
  have hstable : (prefixWord ++ tailWord_5061557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5061557).length < 2 ^ (prefixWord ++ tailWord_5061557).sum := by decide
  have hdescent : baseEnd_5061557 < baseStart_5061557 := by decide
  rcases family_descends (prefixWord ++ tailWord_5061557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5061594 : List Nat := [3, 1, 1, 2, 4, 1, 3, 1, 2, 2, 3]
def baseStart_5061594 : Nat := 118140960795 + 5061594 * 2 ^ 59
def prefixEnd_5061594 : Nat := 4983230072969 + 3 ^ 40 * 5061594 * 2
def baseEnd_5061594 : Nat := 2599030599913574723897159

theorem tailTrace_5061594 : CollatzResearch.WordTrace tailWord_5061594 prefixEnd_5061594 2599030599913574723897159 := by
  unfold tailWord_5061594
  simp only [CollatzResearch.WordTrace]
  refine ⟨46152874906179216069453959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123074333083144576185210557 46152874906179216069453959)
  ·
    refine ⟨69229312359268824104180939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46152874906179216069453959 69229312359268824104180939)
    ·
      refine ⟨103843968538903236156271409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69229312359268824104180939 103843968538903236156271409)
      ·
        refine ⟨77882976404177427117203557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103843968538903236156271409 77882976404177427117203557)
        ·
          refine ⟨14603058075783267584475667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 77882976404177427117203557 14603058075783267584475667)
          ·
            refine ⟨21904587113674901376713501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14603058075783267584475667 21904587113674901376713501)
            ·
              refine ⟨8214220167628088016267563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21904587113674901376713501 8214220167628088016267563)
              ·
                refine ⟨12321330251442132024401345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8214220167628088016267563 12321330251442132024401345)
                ·
                  refine ⟨9240997688581599018301009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12321330251442132024401345 9240997688581599018301009)
                  ·
                    refine ⟨6930748266436199263725757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9240997688581599018301009 6930748266436199263725757)
                    ·
                      refine ⟨2599030599913574723897159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6930748266436199263725757 2599030599913574723897159)
                      ·
                        rfl

theorem cell23_5061594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 3, 1, 2, 2, 3].length) (baseStart_5061594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5061594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5061594 prefixEnd_5061594 := by exact prefixLift 5061594
  have htrace : WordTrace (prefixWord ++ tailWord_5061594) baseStart_5061594 baseEnd_5061594 := by
    simpa [prefixWord, tailWord_5061594, baseEnd_5061594] using wordTrace_append hprefix tailTrace_5061594
  have hstable : (prefixWord ++ tailWord_5061594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5061594).length < 2 ^ (prefixWord ++ tailWord_5061594).sum := by decide
  have hdescent : baseEnd_5061594 < baseStart_5061594 := by decide
  rcases family_descends (prefixWord ++ tailWord_5061594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5061644 : List Nat := [2, 2, 1, 2, 3, 3, 2, 2, 1, 5]
def baseStart_5061644 : Nat := 118140960795 + 5061644 * 2 ^ 59
def prefixEnd_5061644 : Nat := 4983230072969 + 3 ^ 40 * 5061644 * 2
def baseEnd_5061644 : Nat := 866352091315433176090643

theorem tailTrace_5061644 : CollatzResearch.WordTrace tailWord_5061644 prefixEnd_5061644 866352091315433176090643 := by
  unfold tailWord_5061644
  simp only [CollatzResearch.WordTrace]
  refine ⟨92306661637267861408567993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123075548849690481878090657 92306661637267861408567993)
  ·
    refine ⟨69229996227950896056425995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92306661637267861408567993 69229996227950896056425995)
    ·
      refine ⟨103844994341926344084638993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69229996227950896056425995 103844994341926344084638993)
      ·
        refine ⟨77883745756444758063479245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103844994341926344084638993 77883745756444758063479245)
        ·
          refine ⟨29206404658666784273804717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77883745756444758063479245 29206404658666784273804717)
          ·
            refine ⟨10952401747000044102676769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29206404658666784273804717 10952401747000044102676769)
            ·
              refine ⟨8214301310250033077007577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10952401747000044102676769 8214301310250033077007577)
              ·
                refine ⟨6160725982687524807755683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8214301310250033077007577 6160725982687524807755683)
                ·
                  refine ⟨9241088974031287211633525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6160725982687524807755683 9241088974031287211633525)
                  ·
                    refine ⟨866352091315433176090643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9241088974031287211633525 866352091315433176090643)
                    ·
                      rfl

theorem cell23_5061644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 2, 2, 1, 5].length) (baseStart_5061644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5061644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5061644 prefixEnd_5061644 := by exact prefixLift 5061644
  have htrace : WordTrace (prefixWord ++ tailWord_5061644) baseStart_5061644 baseEnd_5061644 := by
    simpa [prefixWord, tailWord_5061644, baseEnd_5061644] using wordTrace_append hprefix tailTrace_5061644
  have hstable : (prefixWord ++ tailWord_5061644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5061644).length < 2 ^ (prefixWord ++ tailWord_5061644).sum := by decide
  have hdescent : baseEnd_5061644 < baseStart_5061644 := by decide
  rcases family_descends (prefixWord ++ tailWord_5061644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5061657 : List Nat := [1, 2, 1, 2, 1, 1, 5, 2, 4, 4]
def baseStart_5061657 : Nat := 118140960795 + 5061657 * 2 ^ 59
def prefixEnd_5061657 : Nat := 4983230072969 + 3 ^ 40 * 5061657 * 2
def baseEnd_5061657 : Nat := 866354316398269325803123

theorem tailTrace_5061657 : CollatzResearch.WordTrace tailWord_5061657 prefixEnd_5061657 866354316398269325803123 := by
  unfold tailWord_5061657
  simp only [CollatzResearch.WordTrace]
  refine ⟨184613797423488626037359225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123075864948992417358239483 184613797423488626037359225)
  ·
    refine ⟨138460348067616469528019419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184613797423488626037359225 138460348067616469528019419)
    ·
      refine ⟨207690522101424704292029129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138460348067616469528019419 207690522101424704292029129)
      ·
        refine ⟨155767891576068528219021847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 207690522101424704292029129 155767891576068528219021847)
        ·
          refine ⟨233651837364102792328532771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155767891576068528219021847 233651837364102792328532771)
          ·
            refine ⟨350477756046154188492799157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 233651837364102792328532771 350477756046154188492799157)
            ·
              refine ⟨32857289629326955171199921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 350477756046154188492799157 32857289629326955171199921)
              ·
                refine ⟨24642967221995216378399941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32857289629326955171199921 24642967221995216378399941)
                ·
                  refine ⟨4620556354124103070949989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24642967221995216378399941 4620556354124103070949989)
                  ·
                    refine ⟨866354316398269325803123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4620556354124103070949989 866354316398269325803123)
                    ·
                      rfl

theorem cell23_5061657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 2, 4, 4].length) (baseStart_5061657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5061657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5061657 prefixEnd_5061657 := by exact prefixLift 5061657
  have htrace : WordTrace (prefixWord ++ tailWord_5061657) baseStart_5061657 baseEnd_5061657 := by
    simpa [prefixWord, tailWord_5061657, baseEnd_5061657] using wordTrace_append hprefix tailTrace_5061657
  have hstable : (prefixWord ++ tailWord_5061657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5061657).length < 2 ^ (prefixWord ++ tailWord_5061657).sum := by decide
  have hdescent : baseEnd_5061657 < baseStart_5061657 := by decide
  rcases family_descends (prefixWord ++ tailWord_5061657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5061667 : List Nat := [1, 1, 1, 4, 3, 2, 1, 3, 1, 1, 5]
def baseStart_5061667 : Nat := 118140960795 + 5061667 * 2 ^ 59
def prefixEnd_5061667 : Nat := 4983230072969 + 3 ^ 40 * 5061667 * 2
def baseEnd_5061667 : Nat := 2599068084001352938284323

theorem tailTrace_5061667 : CollatzResearch.WordTrace tailWord_5061667 prefixEnd_5061667 2599068084001352938284323 := by
  unfold tailWord_5061667
  simp only [CollatzResearch.WordTrace]
  refine ⟨184614162153452397745223255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123076108102301598496815503 184614162153452397745223255)
  ·
    refine ⟨276921243230178596617834883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184614162153452397745223255 276921243230178596617834883)
    ·
      refine ⟨415381864845267894926752325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 276921243230178596617834883 415381864845267894926752325)
      ·
        refine ⟨77884099658487730298766061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 415381864845267894926752325 77884099658487730298766061)
        ·
          refine ⟨29206537371932898862037273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77884099658487730298766061 29206537371932898862037273)
          ·
            refine ⟨21904903028949674146527955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29206537371932898862037273 21904903028949674146527955)
            ·
              refine ⟨32857354543424511219791933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21904903028949674146527955 32857354543424511219791933)
              ·
                refine ⟨12321507953784191707421975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32857354543424511219791933 12321507953784191707421975)
                ·
                  refine ⟨18482261930676287561132963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12321507953784191707421975 18482261930676287561132963)
                  ·
                    refine ⟨27723392896014431341699445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18482261930676287561132963 27723392896014431341699445)
                    ·
                      refine ⟨2599068084001352938284323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27723392896014431341699445 2599068084001352938284323)
                      ·
                        rfl

theorem cell23_5061667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 3, 1, 1, 5].length) (baseStart_5061667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5061667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5061667 prefixEnd_5061667 := by exact prefixLift 5061667
  have htrace : WordTrace (prefixWord ++ tailWord_5061667) baseStart_5061667 baseEnd_5061667 := by
    simpa [prefixWord, tailWord_5061667, baseEnd_5061667] using wordTrace_append hprefix tailTrace_5061667
  have hstable : (prefixWord ++ tailWord_5061667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5061667).length < 2 ^ (prefixWord ++ tailWord_5061667).sum := by decide
  have hdescent : baseEnd_5061667 < baseStart_5061667 := by decide
  rcases family_descends (prefixWord ++ tailWord_5061667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5061694 : List Nat := [4, 2, 1, 3, 1, 1, 2, 1, 1, 1, 6]
def baseStart_5061694 : Nat := 118140960795 + 5061694 * 2 ^ 59
def prefixEnd_5061694 : Nat := 4983230072969 + 3 ^ 40 * 5061694 * 2
def baseEnd_5061694 : Nat := 2599081947979024332646699

theorem tailTrace_5061694 : CollatzResearch.WordTrace tailWord_5061694 prefixEnd_5061694 2599081947979024332646699 := by
  unfold tailWord_5061694
  simp only [CollatzResearch.WordTrace]
  refine ⟨23076893365544322669557017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 123076764616236387570970757 23076893365544322669557017)
  ·
    refine ⟨17307670024158242002167763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23076893365544322669557017 17307670024158242002167763)
    ·
      refine ⟨25961505036237363003251645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17307670024158242002167763 25961505036237363003251645)
      ·
        refine ⟨9735564388589011126219367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25961505036237363003251645 9735564388589011126219367)
        ·
          refine ⟨14603346582883516689329051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9735564388589011126219367 14603346582883516689329051)
          ·
            refine ⟨21905019874325275033993577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14603346582883516689329051 21905019874325275033993577)
            ·
              refine ⟨16428764905743956275495183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21905019874325275033993577 16428764905743956275495183)
              ·
                refine ⟨24643147358615934413242775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16428764905743956275495183 24643147358615934413242775)
                ·
                  refine ⟨36964721037923901619864163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24643147358615934413242775 36964721037923901619864163)
                  ·
                    refine ⟨55447081556885852429796245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36964721037923901619864163 55447081556885852429796245)
                    ·
                      refine ⟨2599081947979024332646699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 55447081556885852429796245 2599081947979024332646699)
                      ·
                        rfl

theorem cell23_5061694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_5061694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5061694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5061694 prefixEnd_5061694 := by exact prefixLift 5061694
  have htrace : WordTrace (prefixWord ++ tailWord_5061694) baseStart_5061694 baseEnd_5061694 := by
    simpa [prefixWord, tailWord_5061694, baseEnd_5061694] using wordTrace_append hprefix tailTrace_5061694
  have hstable : (prefixWord ++ tailWord_5061694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5061694).length < 2 ^ (prefixWord ++ tailWord_5061694).sum := by decide
  have hdescent : baseEnd_5061694 < baseStart_5061694 := by decide
  rcases family_descends (prefixWord ++ tailWord_5061694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5061714 : List Nat := [3, 2, 2, 1, 3, 1, 1, 1, 3, 3, 3]
def baseStart_5061714 : Nat := 118140960795 + 5061714 * 2 ^ 59
def prefixEnd_5061714 : Nat := 4983230072969 + 3 ^ 40 * 5061714 * 2
def baseEnd_5061714 : Nat := 2599092217592114254396607

theorem tailTrace_5061714 : CollatzResearch.WordTrace tailWord_5061714 prefixEnd_5061714 2599092217592114254396607 := by
  unfold tailWord_5061714
  simp only [CollatzResearch.WordTrace]
  refine ⟨46153969096070531193046049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123077250922854749848122797 46153969096070531193046049)
  ·
    refine ⟨34615476822052898394784537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46153969096070531193046049 34615476822052898394784537)
    ·
      refine ⟨25961607616539673796088403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34615476822052898394784537 25961607616539673796088403)
      ·
        refine ⟨38942411424809510694132605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25961607616539673796088403 38942411424809510694132605)
        ·
          refine ⟨14603404284303566510299727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38942411424809510694132605 14603404284303566510299727)
          ·
            refine ⟨21905106426455349765449591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14603404284303566510299727 21905106426455349765449591)
            ·
              refine ⟨32857659639683024648174387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21905106426455349765449591 32857659639683024648174387)
              ·
                refine ⟨49286489459524536972261581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32857659639683024648174387 49286489459524536972261581)
                ·
                  refine ⟨18482433547321701364598093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49286489459524536972261581 18482433547321701364598093)
                  ·
                    refine ⟨6930912580245638011724285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18482433547321701364598093 6930912580245638011724285)
                    ·
                      refine ⟨2599092217592114254396607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6930912580245638011724285 2599092217592114254396607)
                      ·
                        rfl

theorem cell23_5061714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 1, 3, 3, 3].length) (baseStart_5061714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5061714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5061714 prefixEnd_5061714 := by exact prefixLift 5061714
  have htrace : WordTrace (prefixWord ++ tailWord_5061714) baseStart_5061714 baseEnd_5061714 := by
    simpa [prefixWord, tailWord_5061714, baseEnd_5061714] using wordTrace_append hprefix tailTrace_5061714
  have hstable : (prefixWord ++ tailWord_5061714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5061714).length < 2 ^ (prefixWord ++ tailWord_5061714).sum := by decide
  have hdescent : baseEnd_5061714 < baseStart_5061714 := by decide
  rcases family_descends (prefixWord ++ tailWord_5061714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5061737 : List Nat := [1, 2, 1, 1, 1, 6, 1, 1, 2, 3, 4]
def baseStart_5061737 : Nat := 118140960795 + 5061737 * 2 ^ 59
def prefixEnd_5061737 : Nat := 4983230072969 + 3 ^ 40 * 5061737 * 2
def baseEnd_5061737 : Nat := 2599104027647167664409001

theorem tailTrace_5061737 : CollatzResearch.WordTrace tailWord_5061737 prefixEnd_5061737 2599104027647167664409001 := by
  unfold tailWord_5061737
  simp only [CollatzResearch.WordTrace]
  refine ⟨184616715263198799700271465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123077810175465866466847643 184616715263198799700271465)
  ·
    refine ⟨138462536447399099775203599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184616715263198799700271465 138462536447399099775203599)
    ·
      refine ⟨207693804671098649662805399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138462536447399099775203599 207693804671098649662805399)
      ·
        refine ⟨311540707006647974494208099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 207693804671098649662805399 311540707006647974494208099)
        ·
          refine ⟨467311060509971961741312149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 311540707006647974494208099 467311060509971961741312149)
          ·
            refine ⟨21905205961404935706624007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 467311060509971961741312149 21905205961404935706624007)
            ·
              refine ⟨32857808942107403559936011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21905205961404935706624007 32857808942107403559936011)
              ·
                refine ⟨49286713413161105339904017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32857808942107403559936011 49286713413161105339904017)
                ·
                  refine ⟨36965035059870829004928013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49286713413161105339904017 36965035059870829004928013)
                  ·
                    refine ⟨13861888147451560876848005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36965035059870829004928013 13861888147451560876848005)
                    ·
                      refine ⟨2599104027647167664409001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13861888147451560876848005 2599104027647167664409001)
                      ·
                        rfl

theorem cell23_5061737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 1, 2, 3, 4].length) (baseStart_5061737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5061737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5061737 prefixEnd_5061737 := by exact prefixLift 5061737
  have htrace : WordTrace (prefixWord ++ tailWord_5061737) baseStart_5061737 baseEnd_5061737 := by
    simpa [prefixWord, tailWord_5061737, baseEnd_5061737] using wordTrace_append hprefix tailTrace_5061737
  have hstable : (prefixWord ++ tailWord_5061737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5061737).length < 2 ^ (prefixWord ++ tailWord_5061737).sum := by decide
  have hdescent : baseEnd_5061737 < baseStart_5061737 := by decide
  rcases family_descends (prefixWord ++ tailWord_5061737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5061741 : List Nat := [1, 5, 1, 1, 2, 2, 1, 2, 3, 3, 2]
def baseStart_5061741 : Nat := 118140960795 + 5061741 * 2 ^ 59
def prefixEnd_5061741 : Nat := 4983230072969 + 3 ^ 40 * 5061741 * 2
def baseEnd_5061741 : Nat := 2599106081569785648758983

theorem tailTrace_5061741 : CollatzResearch.WordTrace tailWord_5061741 prefixEnd_5061741 2599106081569785648758983 := by
  unfold tailWord_5061741
  simp only [CollatzResearch.WordTrace]
  refine ⟨184616861155184308383417077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123077907436789538922278051 184616861155184308383417077)
  ·
    refine ⟨17307830733298528910945351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 184616861155184308383417077 17307830733298528910945351)
    ·
      refine ⟨25961746099947793366418027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17307830733298528910945351 25961746099947793366418027)
      ·
        refine ⟨38942619149921690049627041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25961746099947793366418027 38942619149921690049627041)
        ·
          refine ⟨29206964362441267537220281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38942619149921690049627041 29206964362441267537220281)
          ·
            refine ⟨21905223271830950652915211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29206964362441267537220281 21905223271830950652915211)
            ·
              refine ⟨32857834907746425979372817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21905223271830950652915211 32857834907746425979372817)
              ·
                refine ⟨24643376180809819484529613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32857834907746425979372817 24643376180809819484529613)
                ·
                  refine ⟨9241266067803682306698605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24643376180809819484529613 9241266067803682306698605)
                  ·
                    refine ⟨3465474775426380865011977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9241266067803682306698605 3465474775426380865011977)
                    ·
                      refine ⟨2599106081569785648758983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3465474775426380865011977 2599106081569785648758983)
                      ·
                        rfl

theorem cell23_5061741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 2, 3, 3, 2].length) (baseStart_5061741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5061741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5061741 prefixEnd_5061741 := by exact prefixLift 5061741
  have htrace : WordTrace (prefixWord ++ tailWord_5061741) baseStart_5061741 baseEnd_5061741 := by
    simpa [prefixWord, tailWord_5061741, baseEnd_5061741] using wordTrace_append hprefix tailTrace_5061741
  have hstable : (prefixWord ++ tailWord_5061741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5061741).length < 2 ^ (prefixWord ++ tailWord_5061741).sum := by decide
  have hdescent : baseEnd_5061741 < baseStart_5061741 := by decide
  rcases family_descends (prefixWord ++ tailWord_5061741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5061767 : List Nat := [1, 1, 4, 2, 1, 1, 1, 1, 3, 4, 4]
def baseStart_5061767 : Nat := 118140960795 + 5061767 * 2 ^ 59
def prefixEnd_5061767 : Nat := 4983230072969 + 3 ^ 40 * 5061767 * 2
def baseEnd_5061767 : Nat := 2599119432066802547033863

theorem tailTrace_5061767 : CollatzResearch.WordTrace tailWord_5061767 prefixEnd_5061767 2599119432066802547033863 := by
  unfold tailWord_5061767
  simp only [CollatzResearch.WordTrace]
  refine ⟨184617809453090114823863555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123078539635393409882575703 184617809453090114823863555)
  ·
    refine ⟨276926714179635172235795333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184617809453090114823863555 276926714179635172235795333)
    ·
      refine ⟨51923758908681594794211625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 276926714179635172235795333 51923758908681594794211625)
      ·
        refine ⟨38942819181511196095658719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51923758908681594794211625 38942819181511196095658719)
        ·
          refine ⟨58414228772266794143488079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38942819181511196095658719 58414228772266794143488079)
          ·
            refine ⟨87621343158400191215232119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58414228772266794143488079 87621343158400191215232119)
            ·
              refine ⟨131432014737600286822848179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87621343158400191215232119 131432014737600286822848179)
              ·
                refine ⟨197148022106400430234272269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 131432014737600286822848179 197148022106400430234272269)
                ·
                  refine ⟨73930508289900161337852101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 197148022106400430234272269 73930508289900161337852101)
                  ·
                    refine ⟨13861970304356280250847269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 73930508289900161337852101 13861970304356280250847269)
                    ·
                      refine ⟨2599119432066802547033863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13861970304356280250847269 2599119432066802547033863)
                      ·
                        rfl

theorem cell23_5061767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 1, 3, 4, 4].length) (baseStart_5061767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5061767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5061767 prefixEnd_5061767 := by exact prefixLift 5061767
  have htrace : WordTrace (prefixWord ++ tailWord_5061767) baseStart_5061767 baseEnd_5061767 := by
    simpa [prefixWord, tailWord_5061767, baseEnd_5061767] using wordTrace_append hprefix tailTrace_5061767
  have hstable : (prefixWord ++ tailWord_5061767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5061767).length < 2 ^ (prefixWord ++ tailWord_5061767).sum := by decide
  have hdescent : baseEnd_5061767 < baseStart_5061767 := by decide
  rcases family_descends (prefixWord ++ tailWord_5061767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5061784 : List Nat := [2, 1, 2, 4, 2, 1, 1, 2, 2, 2, 4]
def baseStart_5061784 : Nat := 118140960795 + 5061784 * 2 ^ 59
def prefixEnd_5061784 : Nat := 4983230072969 + 3 ^ 40 * 5061784 * 2
def baseEnd_5061784 : Nat := 2599128161237928980521285

theorem tailTrace_5061784 : CollatzResearch.WordTrace tailWord_5061784 prefixEnd_5061784 2599128161237928980521285 := by
  unfold tailWord_5061784
  simp only [CollatzResearch.WordTrace]
  refine ⟨92309214747014263363616203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123078952996019017818154937 92309214747014263363616203)
  ·
    refine ⟨138463822120521395045424305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92309214747014263363616203 138463822120521395045424305)
    ·
      refine ⟨103847866590391046284068229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138463822120521395045424305 103847866590391046284068229)
      ·
        refine ⟨19471474985698321178262793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 103847866590391046284068229 19471474985698321178262793)
        ·
          refine ⟨14603606239273740883697095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19471474985698321178262793 14603606239273740883697095)
          ·
            refine ⟨21905409358910611325545643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14603606239273740883697095 21905409358910611325545643)
            ·
              refine ⟨32858114038365916988318465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21905409358910611325545643 32858114038365916988318465)
              ·
                refine ⟨24643585528774437741238849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32858114038365916988318465 24643585528774437741238849)
                ·
                  refine ⟨18482689146580828305929137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24643585528774437741238849 18482689146580828305929137)
                  ·
                    refine ⟨13862016859935621229446853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18482689146580828305929137 13862016859935621229446853)
                    ·
                      refine ⟨2599128161237928980521285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13862016859935621229446853 2599128161237928980521285)
                      ·
                        rfl

theorem cell23_5061784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 2, 2, 2, 4].length) (baseStart_5061784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5061784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5061784 prefixEnd_5061784 := by exact prefixLift 5061784
  have htrace : WordTrace (prefixWord ++ tailWord_5061784) baseStart_5061784 baseEnd_5061784 := by
    simpa [prefixWord, tailWord_5061784, baseEnd_5061784] using wordTrace_append hprefix tailTrace_5061784
  have hstable : (prefixWord ++ tailWord_5061784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5061784).length < 2 ^ (prefixWord ++ tailWord_5061784).sum := by decide
  have hdescent : baseEnd_5061784 < baseStart_5061784 := by decide
  rcases family_descends (prefixWord ++ tailWord_5061784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5061788 : List Nat := [2, 2, 3, 2, 1, 3, 1, 1, 4, 2, 2]
def baseStart_5061788 : Nat := 118140960795 + 5061788 * 2 ^ 59
def prefixEnd_5061788 : Nat := 4983230072969 + 3 ^ 40 * 5061788 * 2
def baseEnd_5061788 : Nat := 2599130215160546964871267

theorem tailTrace_5061788 : CollatzResearch.WordTrace tailWord_5061788 prefixEnd_5061788 2599130215160546964871267 := by
  unfold tailWord_5061788
  simp only [CollatzResearch.WordTrace]
  refine ⟨92309287693007017705189009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123079050257342690273585345 92309287693007017705189009)
  ·
    refine ⟨69231965769755263278891757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92309287693007017705189009 69231965769755263278891757)
    ·
      refine ⟨25961987163658223729584409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69231965769755263278891757 25961987163658223729584409)
      ·
        refine ⟨19471490372743667797188307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25961987163658223729584409 19471490372743667797188307)
        ·
          refine ⟨29207235559115501695782461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19471490372743667797188307 29207235559115501695782461)
          ·
            refine ⟨10952713334668313135918423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29207235559115501695782461 10952713334668313135918423)
            ·
              refine ⟨16429070002002469703877635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10952713334668313135918423 16429070002002469703877635)
              ·
                refine ⟨24643605003003704555816453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16429070002002469703877635 24643605003003704555816453)
                ·
                  refine ⟨4620675938063194604215585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24643605003003704555816453 4620675938063194604215585)
                  ·
                    refine ⟨3465506953547395953161689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4620675938063194604215585 3465506953547395953161689)
                    ·
                      refine ⟨2599130215160546964871267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3465506953547395953161689 2599130215160546964871267)
                      ·
                        rfl

theorem cell23_5061788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 1, 4, 2, 2].length) (baseStart_5061788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5061788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5061788 prefixEnd_5061788 := by exact prefixLift 5061788
  have htrace : WordTrace (prefixWord ++ tailWord_5061788) baseStart_5061788 baseEnd_5061788 := by
    simpa [prefixWord, tailWord_5061788, baseEnd_5061788] using wordTrace_append hprefix tailTrace_5061788
  have hstable : (prefixWord ++ tailWord_5061788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5061788).length < 2 ^ (prefixWord ++ tailWord_5061788).sum := by decide
  have hdescent : baseEnd_5061788 < baseStart_5061788 := by decide
  rcases family_descends (prefixWord ++ tailWord_5061788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5061805 : List Nat := [1, 5, 2, 1, 3, 2, 1, 1, 1, 4, 2]
def baseStart_5061805 : Nat := 118140960795 + 5061805 * 2 ^ 59
def prefixEnd_5061805 : Nat := 4983230072969 + 3 ^ 40 * 5061805 * 2
def baseEnd_5061805 : Nat := 2599138944331673398358689

theorem tailTrace_5061805 : CollatzResearch.WordTrace tailWord_5061805 prefixEnd_5061805 2599138944331673398358689 := by
  unfold tailWord_5061805
  simp only [CollatzResearch.WordTrace]
  refine ⟨184619195426952447313746869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123079463617968298209164579 184619195426952447313746869)
  ·
    refine ⟨17308049571276791935663769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 184619195426952447313746869 17308049571276791935663769)
    ·
      refine ⟨12981037178457593951747827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17308049571276791935663769 12981037178457593951747827)
      ·
        refine ⟨19471555767686390927621741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12981037178457593951747827 19471555767686390927621741)
        ·
          refine ⟨7301833412882396597858153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19471555767686390927621741 7301833412882396597858153)
          ·
            refine ⟨5476375059661797448393615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7301833412882396597858153 5476375059661797448393615)
            ·
              refine ⟨8214562589492696172590423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5476375059661797448393615 8214562589492696172590423)
              ·
                refine ⟨12321843884239044258885635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8214562589492696172590423 12321843884239044258885635)
                ·
                  refine ⟨18482765826358566388328453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12321843884239044258885635 18482765826358566388328453)
                  ·
                    refine ⟨3465518592442231197811585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18482765826358566388328453 3465518592442231197811585)
                    ·
                      refine ⟨2599138944331673398358689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3465518592442231197811585 2599138944331673398358689)
                      ·
                        rfl

theorem cell23_5061805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 1, 1, 1, 4, 2].length) (baseStart_5061805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5061805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5061805 prefixEnd_5061805 := by exact prefixLift 5061805
  have htrace : WordTrace (prefixWord ++ tailWord_5061805) baseStart_5061805 baseEnd_5061805 := by
    simpa [prefixWord, tailWord_5061805, baseEnd_5061805] using wordTrace_append hprefix tailTrace_5061805
  have hstable : (prefixWord ++ tailWord_5061805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5061805).length < 2 ^ (prefixWord ++ tailWord_5061805).sum := by decide
  have hdescent : baseEnd_5061805 < baseStart_5061805 := by decide
  rcases family_descends (prefixWord ++ tailWord_5061805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5061807 : List Nat := [1, 1, 2, 1, 2, 3, 3, 2, 1, 7]
def baseStart_5061807 : Nat := 118140960795 + 5061807 * 2 ^ 59
def prefixEnd_5061807 : Nat := 4983230072969 + 3 ^ 40 * 5061807 * 2
def baseEnd_5061807 : Nat := 866379990430994130177893

theorem tailTrace_5061807 : CollatzResearch.WordTrace tailWord_5061807 prefixEnd_5061807 866379990430994130177893 := by
  unfold tailWord_5061807
  simp only [CollatzResearch.WordTrace]
  refine ⟨184619268372945201655319675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123079512248630134436879783 184619268372945201655319675)
  ·
    refine ⟨276928902559417802482979513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184619268372945201655319675 276928902559417802482979513)
    ·
      refine ⟨207696676919563351862234635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 276928902559417802482979513 207696676919563351862234635)
      ·
        refine ⟨311545015379345027793351953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 207696676919563351862234635 311545015379345027793351953)
        ·
          refine ⟨233658761534508770845013965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 311545015379345027793351953 233658761534508770845013965)
          ·
            refine ⟨87622035575440789066880237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 233658761534508770845013965 87622035575440789066880237)
            ·
              refine ⟨32858263340790295900080089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 87622035575440789066880237 32858263340790295900080089)
              ·
                refine ⟨24643697505592721925060067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32858263340790295900080089 24643697505592721925060067)
                ·
                  refine ⟨36965546258389082887590101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24643697505592721925060067 36965546258389082887590101)
                  ·
                    refine ⟨866379990430994130177893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36965546258389082887590101 866379990430994130177893)
                    ·
                      rfl

theorem cell23_5061807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 2, 1, 7].length) (baseStart_5061807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5061807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5061807 prefixEnd_5061807 := by exact prefixLift 5061807
  have htrace : WordTrace (prefixWord ++ tailWord_5061807) baseStart_5061807 baseEnd_5061807 := by
    simpa [prefixWord, tailWord_5061807, baseEnd_5061807] using wordTrace_append hprefix tailTrace_5061807
  have hstable : (prefixWord ++ tailWord_5061807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5061807).length < 2 ^ (prefixWord ++ tailWord_5061807).sum := by decide
  have hdescent : baseEnd_5061807 < baseStart_5061807 := by decide
  rcases family_descends (prefixWord ++ tailWord_5061807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5061881 : List Nat := [1, 2, 1, 3, 1, 1, 6, 1, 2, 2, 3]
def baseStart_5061881 : Nat := 118140960795 + 5061881 * 2 ^ 59
def prefixEnd_5061881 : Nat := 4983230072969 + 3 ^ 40 * 5061881 * 2
def baseEnd_5061881 : Nat := 2599177968861415101008339

theorem tailTrace_5061881 : CollatzResearch.WordTrace tailWord_5061881 prefixEnd_5061881 2599177968861415101008339 := by
  unfold tailWord_5061881
  simp only [CollatzResearch.WordTrace]
  refine ⟨184621967374677112293513497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123081311583118074862342331 184621967374677112293513497)
  ·
    refine ⟨138466475531007834220135123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184621967374677112293513497 138466475531007834220135123)
    ·
      refine ⟨207699713296511751330202685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138466475531007834220135123 207699713296511751330202685)
      ·
        refine ⟨77887392486191906748826007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 207699713296511751330202685 77887392486191906748826007)
        ·
          refine ⟨116831088729287860123239011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77887392486191906748826007 116831088729287860123239011)
          ·
            refine ⟨175246633093931790184858517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116831088729287860123239011 175246633093931790184858517)
            ·
              refine ⟨8214685926278052664915243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 175246633093931790184858517 8214685926278052664915243)
              ·
                refine ⟨12322028889417078997372865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8214685926278052664915243 12322028889417078997372865)
                ·
                  refine ⟨9241521667062809248029649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12322028889417078997372865 9241521667062809248029649)
                  ·
                    refine ⟨6931141250297106936022237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9241521667062809248029649 6931141250297106936022237)
                    ·
                      refine ⟨2599177968861415101008339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6931141250297106936022237 2599177968861415101008339)
                      ·
                        rfl

theorem cell23_5061881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 6, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 6, 1, 2, 2, 3].length) (baseStart_5061881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5061881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5061881 prefixEnd_5061881 := by exact prefixLift 5061881
  have htrace : WordTrace (prefixWord ++ tailWord_5061881) baseStart_5061881 baseEnd_5061881 := by
    simpa [prefixWord, tailWord_5061881, baseEnd_5061881] using wordTrace_append hprefix tailTrace_5061881
  have hstable : (prefixWord ++ tailWord_5061881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5061881).length < 2 ^ (prefixWord ++ tailWord_5061881).sum := by decide
  have hdescent : baseEnd_5061881 < baseStart_5061881 := by decide
  rcases family_descends (prefixWord ++ tailWord_5061881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5061921 : List Nat := [1, 2, 3, 2, 1, 1, 1, 4, 1, 5, 2]
def baseStart_5061921 : Nat := 118140960795 + 5061921 * 2 ^ 59
def prefixEnd_5061921 : Nat := 4983230072969 + 3 ^ 40 * 5061921 * 2
def baseEnd_5061921 : Nat := 2599198508087594944508155

theorem tailTrace_5061921 : CollatzResearch.WordTrace tailWord_5061921 prefixEnd_5061921 2599198508087594944508155 := by
  unfold tailWord_5061921
  simp only [CollatzResearch.WordTrace]
  refine ⟨184623426294532199124969617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123082284196354799416646411 184623426294532199124969617)
  ·
    refine ⟨138467569720899149343727213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184623426294532199124969617 138467569720899149343727213)
    ·
      refine ⟨51925338645337181003897705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 138467569720899149343727213 51925338645337181003897705)
      ·
        refine ⟨38944003984002885752923279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51925338645337181003897705 38944003984002885752923279)
        ·
          refine ⟨58416005976004328629384919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38944003984002885752923279 58416005976004328629384919)
          ·
            refine ⟨87624008964006492944077379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58416005976004328629384919 87624008964006492944077379)
            ·
              refine ⟨131436013446009739416116069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87624008964006492944077379 131436013446009739416116069)
              ·
                refine ⟨24644252521126826140521763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 131436013446009739416116069 24644252521126826140521763)
                ·
                  refine ⟨36966378781690239210782645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24644252521126826140521763 36966378781690239210782645)
                  ·
                    refine ⟨3465598010783459926010873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 36966378781690239210782645 3465598010783459926010873)
                    ·
                      refine ⟨2599198508087594944508155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3465598010783459926010873 2599198508087594944508155)
                      ·
                        rfl

theorem cell23_5061921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 4, 1, 5, 2].length) (baseStart_5061921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5061921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5061921 prefixEnd_5061921 := by exact prefixLift 5061921
  have htrace : WordTrace (prefixWord ++ tailWord_5061921) baseStart_5061921 baseEnd_5061921 := by
    simpa [prefixWord, tailWord_5061921, baseEnd_5061921] using wordTrace_append hprefix tailTrace_5061921
  have hstable : (prefixWord ++ tailWord_5061921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5061921).length < 2 ^ (prefixWord ++ tailWord_5061921).sum := by decide
  have hdescent : baseEnd_5061921 < baseStart_5061921 := by decide
  rcases family_descends (prefixWord ++ tailWord_5061921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5061924 : List Nat := [2, 3, 1, 3, 1, 1, 1, 1, 2, 1, 7]
def baseStart_5061924 : Nat := 118140960795 + 5061924 * 2 ^ 59
def prefixEnd_5061924 : Nat := 4983230072969 + 3 ^ 40 * 5061924 * 2
def baseEnd_5061924 : Nat := 2599200048529558432770641

theorem tailTrace_5061924 : CollatzResearch.WordTrace tailWord_5061924 prefixEnd_5061924 2599200048529558432770641 := by
  unfold tailWord_5061924
  simp only [CollatzResearch.WordTrace]
  refine ⟨92311767856760665318664413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123082357142347553758219217 92311767856760665318664413)
  ·
    refine ⟨34616912946285249494499155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92311767856760665318664413 34616912946285249494499155)
    ·
      refine ⟨51925369419427874241748733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34616912946285249494499155 51925369419427874241748733)
      ·
        refine ⟨19472013532285452840655775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51925369419427874241748733 19472013532285452840655775)
        ·
          refine ⟨29208020298428179260983663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19472013532285452840655775 29208020298428179260983663)
          ·
            refine ⟨43812030447642268891475495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29208020298428179260983663 43812030447642268891475495)
            ·
              refine ⟨65718045671463403337213243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43812030447642268891475495 65718045671463403337213243)
              ·
                refine ⟨98577068507195105005819865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65718045671463403337213243 98577068507195105005819865)
                ·
                  refine ⟨73932801380396328754364899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 98577068507195105005819865 73932801380396328754364899)
                  ·
                    refine ⟨110899202070594493131547349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 73932801380396328754364899 110899202070594493131547349)
                    ·
                      refine ⟨2599200048529558432770641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 110899202070594493131547349 2599200048529558432770641)
                      ·
                        rfl

theorem cell23_5061924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 1, 2, 1, 7].length) (baseStart_5061924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5061924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5061924 prefixEnd_5061924 := by exact prefixLift 5061924
  have htrace : WordTrace (prefixWord ++ tailWord_5061924) baseStart_5061924 baseEnd_5061924 := by
    simpa [prefixWord, tailWord_5061924, baseEnd_5061924] using wordTrace_append hprefix tailTrace_5061924
  have hstable : (prefixWord ++ tailWord_5061924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5061924).length < 2 ^ (prefixWord ++ tailWord_5061924).sum := by decide
  have hdescent : baseEnd_5061924 < baseStart_5061924 := by decide
  rcases family_descends (prefixWord ++ tailWord_5061924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5061928 : List Nat := [2, 1, 5, 1, 2, 1, 1, 1, 5, 1, 3]
def baseStart_5061928 : Nat := 118140960795 + 5061928 * 2 ^ 59
def prefixEnd_5061928 : Nat := 4983230072969 + 3 ^ 40 * 5061928 * 2
def baseEnd_5061928 : Nat := 2599202102452176417120623

theorem tailTrace_5061928 : CollatzResearch.WordTrace tailWord_5061928 prefixEnd_5061928 2599202102452176417120623 := by
  unfold tailWord_5061928
  simp only [CollatzResearch.WordTrace]
  refine ⟨92311840802753419660237219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123082454403671226213649625 92311840802753419660237219)
  ·
    refine ⟨138467761204130129490355829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92311840802753419660237219 138467761204130129490355829)
    ·
      refine ⟨12981352612887199639720859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 138467761204130129490355829 12981352612887199639720859)
      ·
        refine ⟨19472028919330799459581289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12981352612887199639720859 19472028919330799459581289)
        ·
          refine ⟨14604021689498099594685967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19472028919330799459581289 14604021689498099594685967)
          ·
            refine ⟨21906032534247149392028951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14604021689498099594685967 21906032534247149392028951)
            ·
              refine ⟨32859048801370724088043427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21906032534247149392028951 32859048801370724088043427)
              ·
                refine ⟨49288573202056086132065141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32859048801370724088043427 49288573202056086132065141)
                ·
                  refine ⟨4620803737692758074881107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 49288573202056086132065141 4620803737692758074881107)
                  ·
                    refine ⟨6931205606539137112321661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4620803737692758074881107 6931205606539137112321661)
                    ·
                      refine ⟨2599202102452176417120623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6931205606539137112321661 2599202102452176417120623)
                      ·
                        rfl

theorem cell23_5061928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 1, 5, 1, 3].length) (baseStart_5061928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5061928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5061928 prefixEnd_5061928 := by exact prefixLift 5061928
  have htrace : WordTrace (prefixWord ++ tailWord_5061928) baseStart_5061928 baseEnd_5061928 := by
    simpa [prefixWord, tailWord_5061928, baseEnd_5061928] using wordTrace_append hprefix tailTrace_5061928
  have hstable : (prefixWord ++ tailWord_5061928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5061928).length < 2 ^ (prefixWord ++ tailWord_5061928).sum := by decide
  have hdescent : baseEnd_5061928 < baseStart_5061928 := by decide
  rcases family_descends (prefixWord ++ tailWord_5061928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5061938 : List Nat := [3, 2, 1, 1, 4, 2, 1, 1, 1, 5, 2]
def baseStart_5061938 : Nat := 118140960795 + 5061938 * 2 ^ 59
def prefixEnd_5061938 : Nat := 4983230072969 + 3 ^ 40 * 5061938 * 2
def baseEnd_5061938 : Nat := 2599207237258721377995577

theorem tailTrace_5061938 : CollatzResearch.WordTrace tailWord_5061938 prefixEnd_5061938 2599207237258721377995577 := by
  unfold tailWord_5061938
  simp only [CollatzResearch.WordTrace]
  refine ⟨46156011583867652757084617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123082697556980407352225645 46156011583867652757084617)
  ·
    refine ⟨34617008687900739567813463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46156011583867652757084617 34617008687900739567813463)
    ·
      refine ⟨51925513031851109351720195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34617008687900739567813463 51925513031851109351720195)
      ·
        refine ⟨77888269547776664027580293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51925513031851109351720195 77888269547776664027580293)
        ·
          refine ⟨14604050540208124505171305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 77888269547776664027580293 14604050540208124505171305)
          ·
            refine ⟨10953037905156093378878479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14604050540208124505171305 10953037905156093378878479)
            ·
              refine ⟨16429556857734140068317719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10953037905156093378878479 16429556857734140068317719)
              ·
                refine ⟨24644335286601210102476579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16429556857734140068317719 24644335286601210102476579)
                ·
                  refine ⟨36966502929901815153714869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24644335286601210102476579 36966502929901815153714869)
                  ·
                    refine ⟨3465609649678295170660769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 36966502929901815153714869 3465609649678295170660769)
                    ·
                      refine ⟨2599207237258721377995577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3465609649678295170660769 2599207237258721377995577)
                      ·
                        rfl

theorem cell23_5061938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 1, 1, 5, 2].length) (baseStart_5061938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5061938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5061938 prefixEnd_5061938 := by exact prefixLift 5061938
  have htrace : WordTrace (prefixWord ++ tailWord_5061938) baseStart_5061938 baseEnd_5061938 := by
    simpa [prefixWord, tailWord_5061938, baseEnd_5061938] using wordTrace_append hprefix tailTrace_5061938
  have hstable : (prefixWord ++ tailWord_5061938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5061938).length < 2 ^ (prefixWord ++ tailWord_5061938).sum := by decide
  have hdescent : baseEnd_5061938 < baseStart_5061938 := by decide
  rcases family_descends (prefixWord ++ tailWord_5061938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5061948 : List Nat := [2, 2, 2, 2, 1, 3, 4, 1, 1, 5]
def baseStart_5061948 : Nat := 118140960795 + 5061948 * 2 ^ 59
def prefixEnd_5061948 : Nat := 4983230072969 + 3 ^ 40 * 5061948 * 2
def baseEnd_5061948 : Nat := 866404124021755446290177

theorem tailTrace_5061948 : CollatzResearch.WordTrace tailWord_5061948 prefixEnd_5061948 866404124021755446290177 := by
  unfold tailWord_5061948
  simp only [CollatzResearch.WordTrace]
  refine ⟨92312205532717191368101249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123082940710289588490801665 92312205532717191368101249)
  ·
    refine ⟨69234154149537893526075937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92312205532717191368101249 69234154149537893526075937)
    ·
      refine ⟨51925615612153420144556953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69234154149537893526075937 51925615612153420144556953)
      ·
        refine ⟨38944211709115065108417715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51925615612153420144556953 38944211709115065108417715)
        ·
          refine ⟨58416317563672597662626573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38944211709115065108417715 58416317563672597662626573)
          ·
            refine ⟨21906119086377224123484965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58416317563672597662626573 21906119086377224123484965)
            ·
              refine ⟨4107397328695729523153431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21906119086377224123484965 4107397328695729523153431)
              ·
                refine ⟨6161095993043594284730147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4107397328695729523153431 6161095993043594284730147)
                ·
                  refine ⟨9241643989565391427095221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6161095993043594284730147 9241643989565391427095221)
                  ·
                    refine ⟨866404124021755446290177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9241643989565391427095221 866404124021755446290177)
                    ·
                      rfl

theorem cell23_5061948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 4, 1, 1, 5].length) (baseStart_5061948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5061948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5061948 prefixEnd_5061948 := by exact prefixLift 5061948
  have htrace : WordTrace (prefixWord ++ tailWord_5061948) baseStart_5061948 baseEnd_5061948 := by
    simpa [prefixWord, tailWord_5061948, baseEnd_5061948] using wordTrace_append hprefix tailTrace_5061948
  have hstable : (prefixWord ++ tailWord_5061948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5061948).length < 2 ^ (prefixWord ++ tailWord_5061948).sum := by decide
  have hdescent : baseEnd_5061948 < baseStart_5061948 := by decide
  rcases family_descends (prefixWord ++ tailWord_5061948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5061988 : List Nat := [2, 3, 1, 1, 3, 2, 1, 4, 1, 2, 3]
def baseStart_5061988 : Nat := 118140960795 + 5061988 * 2 ^ 59
def prefixEnd_5061988 : Nat := 4983230072969 + 3 ^ 40 * 5061988 * 2
def baseEnd_5061988 : Nat := 2599232911291446182370347

theorem tailTrace_5061988 : CollatzResearch.WordTrace tailWord_5061988 prefixEnd_5061988 2599232911291446182370347 := by
  unfold tailWord_5061988
  simp only [CollatzResearch.WordTrace]
  refine ⟨92312934992644734783829309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123083913323526313045105745 92312934992644734783829309)
  ·
    refine ⟨34617350622241775543935991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92312934992644734783829309 34617350622241775543935991)
    ·
      refine ⟨51926025933362663315903987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34617350622241775543935991 51926025933362663315903987)
      ·
        refine ⟨77889038900043994973855981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51926025933362663315903987 77889038900043994973855981)
        ·
          refine ⟨29208389587516498115195993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77889038900043994973855981 29208389587516498115195993)
          ·
            refine ⟨21906292190637373586396995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29208389587516498115195993 21906292190637373586396995)
            ·
              refine ⟨32859438285956060379595493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21906292190637373586396995 32859438285956060379595493)
              ·
                refine ⟨6161144678616761321174155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32859438285956060379595493 6161144678616761321174155)
                ·
                  refine ⟨9241717017925141981761233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6161144678616761321174155 9241717017925141981761233)
                  ·
                    refine ⟨6931287763443856486320925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9241717017925141981761233 6931287763443856486320925)
                    ·
                      refine ⟨2599232911291446182370347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6931287763443856486320925 2599232911291446182370347)
                      ·
                        rfl

theorem cell23_5061988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 4, 1, 2, 3].length) (baseStart_5061988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5061988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5061988 prefixEnd_5061988 := by exact prefixLift 5061988
  have htrace : WordTrace (prefixWord ++ tailWord_5061988) baseStart_5061988 baseEnd_5061988 := by
    simpa [prefixWord, tailWord_5061988, baseEnd_5061988] using wordTrace_append hprefix tailTrace_5061988
  have hstable : (prefixWord ++ tailWord_5061988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5061988).length < 2 ^ (prefixWord ++ tailWord_5061988).sum := by decide
  have hdescent : baseEnd_5061988 < baseStart_5061988 := by decide
  rcases family_descends (prefixWord ++ tailWord_5061988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5061991 : List Nat := [1, 1, 5, 1, 4, 1, 1, 9]
def baseStart_5061991 : Nat := 118140960795 + 5061991 * 2 ^ 59
def prefixEnd_5061991 : Nat := 4983230072969 + 3 ^ 40 * 5061991 * 2
def baseEnd_5061991 : Nat := 96267942656792950764179

theorem tailTrace_5061991 : CollatzResearch.WordTrace tailWord_5061991 prefixEnd_5061991 96267942656792950764179 := by
  unfold tailWord_5061991
  simp only [CollatzResearch.WordTrace]
  refine ⟨184625979404278601080017827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123083986269519067386678551 184625979404278601080017827)
  ·
    refine ⟨276938969106417901620026741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184625979404278601080017827 276938969106417901620026741)
    ·
      refine ⟨25963028353726678276877507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 276938969106417901620026741 25963028353726678276877507)
      ·
        refine ⟨38944542530590017415316261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25963028353726678276877507 38944542530590017415316261)
        ·
          refine ⟨7302101724485628265371799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38944542530590017415316261 7302101724485628265371799)
          ·
            refine ⟨10953152586728442398057699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7302101724485628265371799 10953152586728442398057699)
            ·
              refine ⟨16429728880092663597086549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10953152586728442398057699 16429728880092663597086549)
              ·
                refine ⟨96267942656792950764179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 16429728880092663597086549 96267942656792950764179)
                ·
                  rfl

theorem cell23_5061991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 9].length) (baseStart_5061991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5061991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5061991 prefixEnd_5061991 := by exact prefixLift 5061991
  have htrace : WordTrace (prefixWord ++ tailWord_5061991) baseStart_5061991 baseEnd_5061991 := by
    simpa [prefixWord, tailWord_5061991, baseEnd_5061991] using wordTrace_append hprefix tailTrace_5061991
  have hstable : (prefixWord ++ tailWord_5061991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5061991).length < 2 ^ (prefixWord ++ tailWord_5061991).sum := by decide
  have hdescent : baseEnd_5061991 < baseStart_5061991 := by decide
  rcases family_descends (prefixWord ++ tailWord_5061991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5062001 : List Nat := [1, 2, 2, 2, 1, 2, 2, 4, 1, 3, 3]
def baseStart_5062001 : Nat := 118140960795 + 5062001 * 2 ^ 59
def prefixEnd_5062001 : Nat := 4983230072969 + 3 ^ 40 * 5062001 * 2
def baseEnd_5062001 : Nat := 2599239586539954631507787

theorem tailTrace_5062001 : CollatzResearch.WordTrace tailWord_5062001 prefixEnd_5062001 2599239586539954631507787 := by
  unfold tailWord_5062001
  simp only [CollatzResearch.WordTrace]
  refine ⟨184626344134242372787881857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123084229422828248525254571 184626344134242372787881857)
  ·
    refine ⟨138469758100681779590911393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184626344134242372787881857 138469758100681779590911393)
    ·
      refine ⟨103852318575511334693183545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138469758100681779590911393 103852318575511334693183545)
      ·
        refine ⟨77889238931633501019887659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103852318575511334693183545 77889238931633501019887659)
        ·
          refine ⟨116833858397450251529831489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77889238931633501019887659 116833858397450251529831489)
          ·
            refine ⟨87625393798087688647373617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 116833858397450251529831489 87625393798087688647373617)
            ·
              refine ⟨65719045348565766485530213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87625393798087688647373617 65719045348565766485530213)
              ·
                refine ⟨12322321002856081216036915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 65719045348565766485530213 12322321002856081216036915)
                ·
                  refine ⟨18483481504284121824055373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12322321002856081216036915 18483481504284121824055373)
                  ·
                    refine ⟨6931305564106545684020765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18483481504284121824055373 6931305564106545684020765)
                    ·
                      refine ⟨2599239586539954631507787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6931305564106545684020765 2599239586539954631507787)
                      ·
                        rfl

theorem cell23_5062001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 4, 1, 3, 3].length) (baseStart_5062001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5062001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5062001 prefixEnd_5062001 := by exact prefixLift 5062001
  have htrace : WordTrace (prefixWord ++ tailWord_5062001) baseStart_5062001 baseEnd_5062001 := by
    simpa [prefixWord, tailWord_5062001, baseEnd_5062001] using wordTrace_append hprefix tailTrace_5062001
  have hstable : (prefixWord ++ tailWord_5062001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5062001).length < 2 ^ (prefixWord ++ tailWord_5062001).sum := by decide
  have hdescent : baseEnd_5062001 < baseStart_5062001 := by decide
  rcases family_descends (prefixWord ++ tailWord_5062001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5062019 : List Nat := [1, 1, 1, 3, 5, 2, 3, 2, 1, 2, 2]
def baseStart_5062019 : Nat := 118140960795 + 5062019 * 2 ^ 59
def prefixEnd_5062019 : Nat := 4983230072969 + 3 ^ 40 * 5062019 * 2
def baseEnd_5062019 : Nat := 2599248829191735561082705

theorem tailTrace_5062019 : CollatzResearch.WordTrace tailWord_5062019 prefixEnd_5062019 2599248829191735561082705 := by
  unfold tailWord_5062019
  simp only [CollatzResearch.WordTrace]
  refine ⟨184627000648177161862037111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123084667098784774574691407 184627000648177161862037111)
  ·
    refine ⟨276940500972265742793055667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184627000648177161862037111 276940500972265742793055667)
    ·
      refine ⟨415410751458398614189583501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 276940500972265742793055667 415410751458398614189583501)
      ·
        refine ⟨155779031796899480321093813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 415410751458398614189583501 155779031796899480321093813)
        ·
          refine ⟨14604284230959326280102545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 155779031796899480321093813 14604284230959326280102545)
          ·
            refine ⟨10953213173219494710076909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14604284230959326280102545 10953213173219494710076909)
            ·
              refine ⟨4107454939957310516278841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10953213173219494710076909 4107454939957310516278841)
              ·
                refine ⟨3080591204967982887209131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4107454939957310516278841 3080591204967982887209131)
                ·
                  refine ⟨4620886807451974330813697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3080591204967982887209131 4620886807451974330813697)
                  ·
                    refine ⟨3465665105588980748110273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4620886807451974330813697 3465665105588980748110273)
                    ·
                      refine ⟨2599248829191735561082705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3465665105588980748110273 2599248829191735561082705)
                      ·
                        rfl

theorem cell23_5062019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 3, 2, 1, 2, 2].length) (baseStart_5062019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5062019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5062019 prefixEnd_5062019 := by exact prefixLift 5062019
  have htrace : WordTrace (prefixWord ++ tailWord_5062019) baseStart_5062019 baseEnd_5062019 := by
    simpa [prefixWord, tailWord_5062019, baseEnd_5062019] using wordTrace_append hprefix tailTrace_5062019
  have hstable : (prefixWord ++ tailWord_5062019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5062019).length < 2 ^ (prefixWord ++ tailWord_5062019).sum := by decide
  have hdescent : baseEnd_5062019 < baseStart_5062019 := by decide
  rcases family_descends (prefixWord ++ tailWord_5062019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5062028 : List Nat := [2, 2, 1, 2, 1, 3, 2, 2, 3, 3, 2]
def baseStart_5062028 : Nat := 118140960795 + 5062028 * 2 ^ 59
def prefixEnd_5062028 : Nat := 4983230072969 + 3 ^ 40 * 5062028 * 2
def baseEnd_5062028 : Nat := 2599253450517626025870163

theorem tailTrace_5062028 : CollatzResearch.WordTrace tailWord_5062028 prefixEnd_5062028 2599253450517626025870163 := by
  unfold tailWord_5062028
  simp only [CollatzResearch.WordTrace]
  refine ⟨92313664452572278199557369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123084885936763037599409825 92313664452572278199557369)
  ·
    refine ⟨69235248339429208649668027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92313664452572278199557369 69235248339429208649668027)
    ·
      refine ⟨103852872509143812974502041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69235248339429208649668027 103852872509143812974502041)
      ·
        refine ⟨77889654381857859730876531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103852872509143812974502041 77889654381857859730876531)
        ·
          refine ⟨116834481572786789596314797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77889654381857859730876531 116834481572786789596314797)
          ·
            refine ⟨43812930589795046098618049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 116834481572786789596314797 43812930589795046098618049)
            ·
              refine ⟨32859697942346284573963537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43812930589795046098618049 32859697942346284573963537)
              ·
                refine ⟨24644773456759713430472653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32859697942346284573963537 24644773456759713430472653)
                ·
                  refine ⟨9241790046284892536427245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24644773456759713430472653 9241790046284892536427245)
                  ·
                    refine ⟨3465671267356834701160217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9241790046284892536427245 3465671267356834701160217)
                    ·
                      refine ⟨2599253450517626025870163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3465671267356834701160217 2599253450517626025870163)
                      ·
                        rfl

theorem cell23_5062028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 2, 3, 3, 2].length) (baseStart_5062028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5062028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5062028 prefixEnd_5062028 := by exact prefixLift 5062028
  have htrace : WordTrace (prefixWord ++ tailWord_5062028) baseStart_5062028 baseEnd_5062028 := by
    simpa [prefixWord, tailWord_5062028, baseEnd_5062028] using wordTrace_append hprefix tailTrace_5062028
  have hstable : (prefixWord ++ tailWord_5062028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5062028).length < 2 ^ (prefixWord ++ tailWord_5062028).sum := by decide
  have hdescent : baseEnd_5062028 < baseStart_5062028 := by decide
  rcases family_descends (prefixWord ++ tailWord_5062028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5062045 : List Nat := [1, 4, 2, 1, 3, 2, 1, 1, 3, 3, 2]
def baseStart_5062045 : Nat := 118140960795 + 5062045 * 2 ^ 59
def prefixEnd_5062045 : Nat := 4983230072969 + 3 ^ 40 * 5062045 * 2
def baseEnd_5062045 : Nat := 2599262179688752459357585

theorem tailTrace_5062045 : CollatzResearch.WordTrace tailWord_5062045 prefixEnd_5062045 2599262179688752459357585 := by
  unfold tailWord_5062045
  simp only [CollatzResearch.WordTrace]
  refine ⟨184627948946082968302483589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123085299297388645534989059 184627948946082968302483589)
  ·
    refine ⟨34617740427390556556715673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 184627948946082968302483589 34617740427390556556715673)
    ·
      refine ⟨25963305320542917417536755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34617740427390556556715673 25963305320542917417536755)
      ·
        refine ⟨38944957980814376126305133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25963305320542917417536755 38944957980814376126305133)
        ·
          refine ⟨14604359242805391047364425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38944957980814376126305133 14604359242805391047364425)
          ·
            refine ⟨10953269432104043285523319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14604359242805391047364425 10953269432104043285523319)
            ·
              refine ⟨16429904148156064928284979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10953269432104043285523319 16429904148156064928284979)
              ·
                refine ⟨24644856222234097392427469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16429904148156064928284979 24644856222234097392427469)
                ·
                  refine ⟨9241821083337786522160301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24644856222234097392427469 9241821083337786522160301)
                  ·
                    refine ⟨3465682906251669945810113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9241821083337786522160301 3465682906251669945810113)
                    ·
                      refine ⟨2599262179688752459357585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3465682906251669945810113 2599262179688752459357585)
                      ·
                        rfl

theorem cell23_5062045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 1, 3, 3, 2].length) (baseStart_5062045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5062045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5062045 prefixEnd_5062045 := by exact prefixLift 5062045
  have htrace : WordTrace (prefixWord ++ tailWord_5062045) baseStart_5062045 baseEnd_5062045 := by
    simpa [prefixWord, tailWord_5062045, baseEnd_5062045] using wordTrace_append hprefix tailTrace_5062045
  have hstable : (prefixWord ++ tailWord_5062045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5062045).length < 2 ^ (prefixWord ++ tailWord_5062045).sum := by decide
  have hdescent : baseEnd_5062045 < baseStart_5062045 := by decide
  rcases family_descends (prefixWord ++ tailWord_5062045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5062064 : List Nat := [2, 1, 1, 1, 2, 1, 1, 3, 11]
def baseStart_5062064 : Nat := 118140960795 + 5062064 * 2 ^ 59
def prefixEnd_5062064 : Nat := 4983230072969 + 3 ^ 40 * 5062064 * 2
def baseEnd_5062064 : Nat := 288807992869020876113333

theorem tailTrace_5062064 : CollatzResearch.WordTrace tailWord_5062064 prefixEnd_5062064 288807992869020876113333 := by
  unfold tailWord_5062064
  simp only [CollatzResearch.WordTrace]
  refine ⟨92314320966507067273712623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123085761288676089698283497 92314320966507067273712623)
  ·
    refine ⟨138471481449760600910568935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92314320966507067273712623 138471481449760600910568935)
    ·
      refine ⟨207707222174640901365853403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138471481449760600910568935 207707222174640901365853403)
      ·
        refine ⟨311560833261961352048780105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 207707222174640901365853403 311560833261961352048780105)
        ·
          refine ⟨233670624946471014036585079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 311560833261961352048780105 233670624946471014036585079)
          ·
            refine ⟨350505937419706521054877619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 233670624946471014036585079 350505937419706521054877619)
            ·
              refine ⟨525758906129559781582316429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 350505937419706521054877619 525758906129559781582316429)
              ·
                refine ⟨197159589798584918093368661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 525758906129559781582316429 197159589798584918093368661)
                ·
                  refine ⟨288807992869020876113333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 197159589798584918093368661 288807992869020876113333)
                  ·
                    rfl

theorem cell23_5062064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 11].length) (baseStart_5062064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5062064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5062064 prefixEnd_5062064 := by exact prefixLift 5062064
  have htrace : WordTrace (prefixWord ++ tailWord_5062064) baseStart_5062064 baseEnd_5062064 := by
    simpa [prefixWord, tailWord_5062064, baseEnd_5062064] using wordTrace_append hprefix tailTrace_5062064
  have hstable : (prefixWord ++ tailWord_5062064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5062064).length < 2 ^ (prefixWord ++ tailWord_5062064).sum := by decide
  have hdescent : baseEnd_5062064 < baseStart_5062064 := by decide
  rcases family_descends (prefixWord ++ tailWord_5062064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5062071 : List Nat := [1, 1, 3, 1, 3, 2, 2, 2, 2, 2, 4]
def baseStart_5062071 : Nat := 118140960795 + 5062071 * 2 ^ 59
def prefixEnd_5062071 : Nat := 4983230072969 + 3 ^ 40 * 5062071 * 2
def baseEnd_5062071 : Nat := 2599275530185769357632465

theorem tailTrace_5062071 : CollatzResearch.WordTrace tailWord_5062071 prefixEnd_5062071 2599275530185769357632465 := by
  unfold tailWord_5062071
  simp only [CollatzResearch.WordTrace]
  refine ⟨184628897243988774742930067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123085931495992516495286711 184628897243988774742930067)
  ·
    refine ⟨276943345865983162114395101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184628897243988774742930067 276943345865983162114395101)
    ·
      refine ⟨103853754699743685792898163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 276943345865983162114395101 103853754699743685792898163)
      ·
        refine ⟨155780632049615528689347245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103853754699743685792898163 155780632049615528689347245)
        ·
          refine ⟨58417737018605823258505217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 155780632049615528689347245 58417737018605823258505217)
          ·
            refine ⟨43813302763954367443878913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58417737018605823258505217 43813302763954367443878913)
            ·
              refine ⟨32859977072965775582909185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43813302763954367443878913 32859977072965775582909185)
              ·
                refine ⟨24644982804724331687181889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32859977072965775582909185 24644982804724331687181889)
                ·
                  refine ⟨18483737103543248765386417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24644982804724331687181889 18483737103543248765386417)
                  ·
                    refine ⟨13862802827657436574039813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18483737103543248765386417 13862802827657436574039813)
                    ·
                      refine ⟨2599275530185769357632465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13862802827657436574039813 2599275530185769357632465)
                      ·
                        rfl

theorem cell23_5062071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 2, 2, 2, 4].length) (baseStart_5062071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5062071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5062071 prefixEnd_5062071 := by exact prefixLift 5062071
  have htrace : WordTrace (prefixWord ++ tailWord_5062071) baseStart_5062071 baseEnd_5062071 := by
    simpa [prefixWord, tailWord_5062071, baseEnd_5062071] using wordTrace_append hprefix tailTrace_5062071
  have hstable : (prefixWord ++ tailWord_5062071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5062071).length < 2 ^ (prefixWord ++ tailWord_5062071).sum := by decide
  have hdescent : baseEnd_5062071 < baseStart_5062071 := by decide
  rcases family_descends (prefixWord ++ tailWord_5062071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5062091 : List Nat := [1, 1, 1, 1, 3, 3, 3, 1, 1, 5, 3]
def baseStart_5062091 : Nat := 118140960795 + 5062091 * 2 ^ 59
def prefixEnd_5062091 : Nat := 4983230072969 + 3 ^ 40 * 5062091 * 2
def baseEnd_5062091 : Nat := 2599285799798859279382373

theorem tailTrace_5062091 : CollatzResearch.WordTrace tailWord_5062091 prefixEnd_5062091 2599285799798859279382373 := by
  unfold tailWord_5062091
  simp only [CollatzResearch.WordTrace]
  refine ⟨184629626703916318158658127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123086417802610878772438751 184629626703916318158658127)
  ·
    refine ⟨276944440055874477237987191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184629626703916318158658127 276944440055874477237987191)
    ·
      refine ⟨415416660083811715856980787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 276944440055874477237987191 415416660083811715856980787)
      ·
        refine ⟨623124990125717573785471181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 415416660083811715856980787 623124990125717573785471181)
        ·
          refine ⟨233671871297144090169551693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 623124990125717573785471181 233671871297144090169551693)
          ·
            refine ⟨87626951736429033813581885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 233671871297144090169551693 87626951736429033813581885)
            ·
              refine ⟨32860106901160887680093207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 87626951736429033813581885 32860106901160887680093207)
              ·
                refine ⟨49290160351741331520139811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32860106901160887680093207 49290160351741331520139811)
                ·
                  refine ⟨73935240527611997280209717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49290160351741331520139811 73935240527611997280209717)
                  ·
                    refine ⟨6931428799463624745019661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 73935240527611997280209717 6931428799463624745019661)
                    ·
                      refine ⟨2599285799798859279382373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6931428799463624745019661 2599285799798859279382373)
                      ·
                        rfl

theorem cell23_5062091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 1, 1, 5, 3].length) (baseStart_5062091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5062091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5062091 prefixEnd_5062091 := by exact prefixLift 5062091
  have htrace : WordTrace (prefixWord ++ tailWord_5062091) baseStart_5062091 baseEnd_5062091 := by
    simpa [prefixWord, tailWord_5062091, baseEnd_5062091] using wordTrace_append hprefix tailTrace_5062091
  have hstable : (prefixWord ++ tailWord_5062091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5062091).length < 2 ^ (prefixWord ++ tailWord_5062091).sum := by decide
  have hdescent : baseEnd_5062091 < baseStart_5062091 := by decide
  rcases family_descends (prefixWord ++ tailWord_5062091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5062092 : List Nat := [2, 2, 1, 4, 2, 1, 2, 3, 2, 2, 2]
def baseStart_5062092 : Nat := 118140960795 + 5062092 * 2 ^ 59
def prefixEnd_5062092 : Nat := 4983230072969 + 3 ^ 40 * 5062092 * 2
def baseEnd_5062092 : Nat := 2599286313279513775469869

theorem tailTrace_5062092 : CollatzResearch.WordTrace tailWord_5062092 prefixEnd_5062092 2599286313279513775469869 := by
  unfold tailWord_5062092
  simp only [CollatzResearch.WordTrace]
  refine ⟨92314831588456347664722265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123086442117941796886296353 92314831588456347664722265)
  ·
    refine ⟨69236123691342260748541699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92314831588456347664722265 69236123691342260748541699)
    ·
      refine ⟨103854185537013391122812549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69236123691342260748541699 103854185537013391122812549)
      ·
        refine ⟨19472659788190010835527353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 103854185537013391122812549 19472659788190010835527353)
        ·
          refine ⟨14604494841142508126645515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19472659788190010835527353 14604494841142508126645515)
          ·
            refine ⟨21906742261713762189968273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14604494841142508126645515 21906742261713762189968273)
            ·
              refine ⟨16430056696285321642476205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21906742261713762189968273 16430056696285321642476205)
              ·
                refine ⟨6161271261106995615928577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16430056696285321642476205 6161271261106995615928577)
                ·
                  refine ⟨4620953445830246711946433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6161271261106995615928577 4620953445830246711946433)
                  ·
                    refine ⟨3465715084372685033959825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4620953445830246711946433 3465715084372685033959825)
                    ·
                      refine ⟨2599286313279513775469869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3465715084372685033959825 2599286313279513775469869)
                      ·
                        rfl

theorem cell23_5062092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 3, 2, 2, 2].length) (baseStart_5062092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5062092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5062092 prefixEnd_5062092 := by exact prefixLift 5062092
  have htrace : WordTrace (prefixWord ++ tailWord_5062092) baseStart_5062092 baseEnd_5062092 := by
    simpa [prefixWord, tailWord_5062092, baseEnd_5062092] using wordTrace_append hprefix tailTrace_5062092
  have hstable : (prefixWord ++ tailWord_5062092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5062092).length < 2 ^ (prefixWord ++ tailWord_5062092).sum := by decide
  have hdescent : baseEnd_5062092 < baseStart_5062092 := by decide
  rcases family_descends (prefixWord ++ tailWord_5062092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5062111 : List Nat := [1, 1, 2, 3, 3, 1, 3, 1, 1, 7]
def baseStart_5062111 : Nat := 118140960795 + 5062111 * 2 ^ 59
def prefixEnd_5062111 : Nat := 4983230072969 + 3 ^ 40 * 5062111 * 2
def baseEnd_5062111 : Nat := 866432023137316400377427

theorem tailTrace_5062111 : CollatzResearch.WordTrace tailWord_5062111 prefixEnd_5062111 866432023137316400377427 := by
  unfold tailWord_5062111
  simp only [CollatzResearch.WordTrace]
  refine ⟨184630356163843861574386187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123086904109229241049590791 184630356163843861574386187)
  ·
    refine ⟨276945534245765792361579281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184630356163843861574386187 276945534245765792361579281)
    ·
      refine ⟨207709150684324344271184461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 276945534245765792361579281 207709150684324344271184461)
      ·
        refine ⟨77890931506621629101694173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 207709150684324344271184461 77890931506621629101694173)
        ·
          refine ⟨29209099314983110913135315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77890931506621629101694173 29209099314983110913135315)
          ·
            refine ⟨43813648972474666369702973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29209099314983110913135315 43813648972474666369702973)
            ·
              refine ⟨16430118364677999888638615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43813648972474666369702973 16430118364677999888638615)
              ·
                refine ⟨24645177547016999832957923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16430118364677999888638615 24645177547016999832957923)
                ·
                  refine ⟨36967766320525499749436885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24645177547016999832957923 36967766320525499749436885)
                  ·
                    refine ⟨866432023137316400377427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36967766320525499749436885 866432023137316400377427)
                    ·
                      rfl

theorem cell23_5062111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 1, 1, 7].length) (baseStart_5062111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5062111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5062111 prefixEnd_5062111 := by exact prefixLift 5062111
  have htrace : WordTrace (prefixWord ++ tailWord_5062111) baseStart_5062111 baseEnd_5062111 := by
    simpa [prefixWord, tailWord_5062111, baseEnd_5062111] using wordTrace_append hprefix tailTrace_5062111
  have hstable : (prefixWord ++ tailWord_5062111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5062111).length < 2 ^ (prefixWord ++ tailWord_5062111).sum := by decide
  have hdescent : baseEnd_5062111 < baseStart_5062111 := by decide
  rcases family_descends (prefixWord ++ tailWord_5062111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5062115 : List Nat := [1, 1, 1, 6, 2, 2, 2, 3, 5]
def baseStart_5062115 : Nat := 118140960795 + 5062115 * 2 ^ 59
def prefixEnd_5062115 : Nat := 4983230072969 + 3 ^ 40 * 5062115 * 2
def baseEnd_5062115 : Nat := 288810902592729687275807

theorem tailTrace_5062115 : CollatzResearch.WordTrace tailWord_5062115 prefixEnd_5062115 288810902592729687275807 := by
  unfold tailWord_5062115
  simp only [CollatzResearch.WordTrace]
  refine ⟨184630502055829370257531799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123087001370552913505021199 184630502055829370257531799)
  ·
    refine ⟨276945753083744055386297699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184630502055829370257531799 276945753083744055386297699)
    ·
      refine ⟨415418629625616083079446549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 276945753083744055386297699 415418629625616083079446549)
      ·
        refine ⟨19472748263700753894349057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 415418629625616083079446549 19472748263700753894349057)
        ·
          refine ⟨14604561197775565420761793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19472748263700753894349057 14604561197775565420761793)
          ·
            refine ⟨10953420898331674065571345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14604561197775565420761793 10953420898331674065571345)
            ·
              refine ⟨8215065673748755549178509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10953420898331674065571345 8215065673748755549178509)
              ·
                refine ⟨3080649627655783330941941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8215065673748755549178509 3080649627655783330941941)
                ·
                  refine ⟨288810902592729687275807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3080649627655783330941941 288810902592729687275807)
                  ·
                    rfl

theorem cell23_5062115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 2, 3, 5].length) (baseStart_5062115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5062115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5062115 prefixEnd_5062115 := by exact prefixLift 5062115
  have htrace : WordTrace (prefixWord ++ tailWord_5062115) baseStart_5062115 baseEnd_5062115 := by
    simpa [prefixWord, tailWord_5062115, baseEnd_5062115] using wordTrace_append hprefix tailTrace_5062115
  have hstable : (prefixWord ++ tailWord_5062115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5062115).length < 2 ^ (prefixWord ++ tailWord_5062115).sum := by decide
  have hdescent : baseEnd_5062115 < baseStart_5062115 := by decide
  rcases family_descends (prefixWord ++ tailWord_5062115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5062161 : List Nat := [1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 4]
def baseStart_5062161 : Nat := 118140960795 + 5062161 * 2 ^ 59
def prefixEnd_5062161 : Nat := 4983230072969 + 3 ^ 40 * 5062161 * 2
def baseEnd_5062161 : Nat := 2599321743444674005507051

theorem tailTrace_5062161 : CollatzResearch.WordTrace tailWord_5062161 prefixEnd_5062161 2599321743444674005507051 := by
  unfold tailWord_5062161
  simp only [CollatzResearch.WordTrace]
  refine ⟨184632179813662720113706337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123088119875775146742470891 184632179813662720113706337)
  ·
    refine ⟨138474134860247040085279753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184632179813662720113706337 138474134860247040085279753)
    ·
      refine ⟨103855601145185280063959815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138474134860247040085279753 103855601145185280063959815)
      ·
        refine ⟨155783401717777920095939723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103855601145185280063959815 155783401717777920095939723)
        ·
          refine ⟨233675102576666880143909585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155783401717777920095939723 233675102576666880143909585)
          ·
            refine ⟨175256326932500160107932189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 233675102576666880143909585 175256326932500160107932189)
            ·
              refine ⟨65721122599687560040474571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 175256326932500160107932189 65721122599687560040474571)
              ·
                refine ⟨98581683899531340060711857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65721122599687560040474571 98581683899531340060711857)
                ·
                  refine ⟨73936262924648505045533893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 98581683899531340060711857 73936262924648505045533893)
                  ·
                    refine ⟨13863049298371594696037605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 73936262924648505045533893 13863049298371594696037605)
                    ·
                      refine ⟨2599321743444674005507051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13863049298371594696037605 2599321743444674005507051)
                      ·
                        rfl

theorem cell23_5062161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 4].length) (baseStart_5062161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5062161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5062161 prefixEnd_5062161 := by exact prefixLift 5062161
  have htrace : WordTrace (prefixWord ++ tailWord_5062161) baseStart_5062161 baseEnd_5062161 := by
    simpa [prefixWord, tailWord_5062161, baseEnd_5062161] using wordTrace_append hprefix tailTrace_5062161
  have hstable : (prefixWord ++ tailWord_5062161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5062161).length < 2 ^ (prefixWord ++ tailWord_5062161).sum := by decide
  have hdescent : baseEnd_5062161 < baseStart_5062161 := by decide
  rcases family_descends (prefixWord ++ tailWord_5062161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5062205 : List Nat := [1, 4, 1, 3, 3, 1, 1, 3, 6]
def baseStart_5062205 : Nat := 118140960795 + 5062205 * 2 ^ 59
def prefixEnd_5062205 : Nat := 4983230072969 + 3 ^ 40 * 5062205 * 2
def baseEnd_5062205 : Nat := 288816037399274648150761

theorem tailTrace_5062205 : CollatzResearch.WordTrace tailWord_5062205 prefixEnd_5062205 288816037399274648150761 := by
  unfold tailWord_5062205
  simp only [CollatzResearch.WordTrace]
  refine ⟨184633784625503315628308069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123089189750335543752205379 184633784625503315628308069)
  ·
    refine ⟨34618834617281871680307763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 184633784625503315628308069 34618834617281871680307763)
    ·
      refine ⟨51928251925922807520461645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34618834617281871680307763 51928251925922807520461645)
      ·
        refine ⟨19473094472221052820173117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51928251925922807520461645 19473094472221052820173117)
        ·
          refine ⟨7302410427082894807564919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19473094472221052820173117 7302410427082894807564919)
          ·
            refine ⟨10953615640624342211347379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7302410427082894807564919 10953615640624342211347379)
            ·
              refine ⟨16430423460936513317021069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10953615640624342211347379 16430423460936513317021069)
              ·
                refine ⟨6161408797851192493882901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16430423460936513317021069 6161408797851192493882901)
                ·
                  refine ⟨288816037399274648150761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6161408797851192493882901 288816037399274648150761)
                  ·
                    rfl

theorem cell23_5062205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 3, 6].length) (baseStart_5062205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5062205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5062205 prefixEnd_5062205 := by exact prefixLift 5062205
  have htrace : WordTrace (prefixWord ++ tailWord_5062205) baseStart_5062205 baseEnd_5062205 := by
    simpa [prefixWord, tailWord_5062205, baseEnd_5062205] using wordTrace_append hprefix tailTrace_5062205
  have hstable : (prefixWord ++ tailWord_5062205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5062205).length < 2 ^ (prefixWord ++ tailWord_5062205).sum := by decide
  have hdescent : baseEnd_5062205 < baseStart_5062205 := by decide
  rcases family_descends (prefixWord ++ tailWord_5062205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5062218 : List Nat := [3, 1, 2, 1, 1, 3, 3, 1, 3, 5]
def baseStart_5062218 : Nat := 118140960795 + 5062218 * 2 ^ 59
def prefixEnd_5062218 : Nat := 4983230072969 + 3 ^ 40 * 5062218 * 2
def baseEnd_5062218 : Nat := 866450337280660094164763

theorem tailTrace_5062218 : CollatzResearch.WordTrace tailWord_5062218 prefixEnd_5062218 866450337280660094164763 := by
  unfold tailWord_5062218
  simp only [CollatzResearch.WordTrace]
  refine ⟨46158564693614054712132827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123089505849637479232354205 46158564693614054712132827)
  ·
    refine ⟨69237847040421082068199241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46158564693614054712132827 69237847040421082068199241)
    ·
      refine ⟨51928385280315811551149431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69237847040421082068199241 51928385280315811551149431)
      ·
        refine ⟨77892577920473717326724147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51928385280315811551149431 77892577920473717326724147)
        ·
          refine ⟨116838866880710575990086221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77892577920473717326724147 116838866880710575990086221)
          ·
            refine ⟨43814575080266465996282333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 116838866880710575990086221 43814575080266465996282333)
            ·
              refine ⟨16430465655099924748605875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43814575080266465996282333 16430465655099924748605875)
              ·
                refine ⟨24645698482649887122908813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16430465655099924748605875 24645698482649887122908813)
                ·
                  refine ⟨9242136930993707671090805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24645698482649887122908813 9242136930993707671090805)
                  ·
                    refine ⟨866450337280660094164763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9242136930993707671090805 866450337280660094164763)
                    ·
                      rfl

theorem cell23_5062218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 1, 3, 5].length) (baseStart_5062218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5062218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5062218 prefixEnd_5062218 := by exact prefixLift 5062218
  have htrace : WordTrace (prefixWord ++ tailWord_5062218) baseStart_5062218 baseEnd_5062218 := by
    simpa [prefixWord, tailWord_5062218, baseEnd_5062218] using wordTrace_append hprefix tailTrace_5062218
  have hstable : (prefixWord ++ tailWord_5062218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5062218).length < 2 ^ (prefixWord ++ tailWord_5062218).sum := by decide
  have hdescent : baseEnd_5062218 < baseStart_5062218 := by decide
  rcases family_descends (prefixWord ++ tailWord_5062218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5062232 : List Nat := [2, 1, 2, 2, 1, 2, 1, 7, 1, 1, 3]
def baseStart_5062232 : Nat := 118140960795 + 5062232 * 2 ^ 59
def prefixEnd_5062232 : Nat := 4983230072969 + 3 ^ 40 * 5062232 * 2
def baseEnd_5062232 : Nat := 2599358200571143227719225

theorem tailTrace_5062232 : CollatzResearch.WordTrace tailWord_5062232 prefixEnd_5062232 2599358200571143227719225 := by
  unfold tailWord_5062232
  simp only [CollatzResearch.WordTrace]
  refine ⟨92317384698202749619770475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123089846264270332826360633 92317384698202749619770475)
  ·
    refine ⟨138476077047304124429655713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92317384698202749619770475 138476077047304124429655713)
    ·
      refine ⟨103857057785478093322241785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138476077047304124429655713 103857057785478093322241785)
      ·
        refine ⟨77892793339108569991681339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103857057785478093322241785 77892793339108569991681339)
        ·
          refine ⟨116839190008662854987522009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77892793339108569991681339 116839190008662854987522009)
          ·
            refine ⟨87629392506497141240641507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 116839190008662854987522009 87629392506497141240641507)
            ·
              refine ⟨131444088759745711860962261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87629392506497141240641507 131444088759745711860962261)
              ·
                refine ⟨3080720830306540121741303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 131444088759745711860962261 3080720830306540121741303)
                ·
                  refine ⟨4621081245459810182611955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3080720830306540121741303 4621081245459810182611955)
                  ·
                    refine ⟨6931621868189715273917933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4621081245459810182611955 6931621868189715273917933)
                    ·
                      refine ⟨2599358200571143227719225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6931621868189715273917933 2599358200571143227719225)
                      ·
                        rfl

theorem cell23_5062232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 7, 1, 1, 3].length) (baseStart_5062232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5062232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5062232 prefixEnd_5062232 := by exact prefixLift 5062232
  have htrace : WordTrace (prefixWord ++ tailWord_5062232) baseStart_5062232 baseEnd_5062232 := by
    simpa [prefixWord, tailWord_5062232, baseEnd_5062232] using wordTrace_append hprefix tailTrace_5062232
  have hstable : (prefixWord ++ tailWord_5062232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5062232).length < 2 ^ (prefixWord ++ tailWord_5062232).sum := by decide
  have hdescent : baseEnd_5062232 < baseStart_5062232 := by decide
  rcases family_descends (prefixWord ++ tailWord_5062232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5062249 : List Nat := [1, 2, 1, 1, 1, 4, 6, 2, 1, 1, 3]
def baseStart_5062249 : Nat := 118140960795 + 5062249 * 2 ^ 59
def prefixEnd_5062249 : Nat := 4983230072969 + 3 ^ 40 * 5062249 * 2
def baseEnd_5062249 : Nat := 2599366929742269661206647

theorem tailTrace_5062249 : CollatzResearch.WordTrace tailWord_5062249 prefixEnd_5062249 2599366929742269661206647 := by
  unfold tailWord_5062249
  simp only [CollatzResearch.WordTrace]
  refine ⟨184635389437343911142909801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123090259624895940761939867 184635389437343911142909801)
  ·
    refine ⟨138476542078007933357182351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184635389437343911142909801 138476542078007933357182351)
    ·
      refine ⟨207714813117011900035773527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138476542078007933357182351 207714813117011900035773527)
      ·
        refine ⟨311572219675517850053660291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 207714813117011900035773527 311572219675517850053660291)
        ·
          refine ⟨467358329513276775080490437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 311572219675517850053660291 467358329513276775080490437)
          ·
            refine ⟨87629686783739395327591957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 467358329513276775080490437 87629686783739395327591957)
            ·
              refine ⟨4107641567987784155980873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 87629686783739395327591957 4107641567987784155980873)
              ·
                refine ⟨3080731175990838116985655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4107641567987784155980873 3080731175990838116985655)
                ·
                  refine ⟨4621096763986257175478483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3080731175990838116985655 4621096763986257175478483)
                  ·
                    refine ⟨6931645145979385763217725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4621096763986257175478483 6931645145979385763217725)
                    ·
                      refine ⟨2599366929742269661206647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6931645145979385763217725 2599366929742269661206647)
                      ·
                        rfl

theorem cell23_5062249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 6, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 6, 2, 1, 1, 3].length) (baseStart_5062249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5062249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5062249 prefixEnd_5062249 := by exact prefixLift 5062249
  have htrace : WordTrace (prefixWord ++ tailWord_5062249) baseStart_5062249 baseEnd_5062249 := by
    simpa [prefixWord, tailWord_5062249, baseEnd_5062249] using wordTrace_append hprefix tailTrace_5062249
  have hstable : (prefixWord ++ tailWord_5062249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5062249).length < 2 ^ (prefixWord ++ tailWord_5062249).sum := by decide
  have hdescent : baseEnd_5062249 < baseStart_5062249 := by decide
  rcases family_descends (prefixWord ++ tailWord_5062249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5062265 : List Nat := [1, 2, 1, 3, 3, 1, 1, 5, 2, 4]
def baseStart_5062265 : Nat := 118140960795 + 5062265 * 2 ^ 59
def prefixEnd_5062265 : Nat := 4983230072969 + 3 ^ 40 * 5062265 * 2
def baseEnd_5062265 : Nat := 866458381810913866202191

theorem tailTrace_5062265 : CollatzResearch.WordTrace tailWord_5062265 prefixEnd_5062265 866458381810913866202191 := by
  unfold tailWord_5062265
  simp only [CollatzResearch.WordTrace]
  refine ⟨184635973005285945875492249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123090648670190630583661499 184635973005285945875492249)
  ·
    refine ⟨138476979753964459406619187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184635973005285945875492249 138476979753964459406619187)
    ·
      refine ⟨207715469630946689109928781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138476979753964459406619187 207715469630946689109928781)
      ·
        refine ⟨77893301111605008416223293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 207715469630946689109928781 77893301111605008416223293)
        ·
          refine ⟨29209987916851878156083735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77893301111605008416223293 29209987916851878156083735)
          ·
            refine ⟨43814981875277817234125603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29209987916851878156083735 43814981875277817234125603)
            ·
              refine ⟨65722472812916725851188405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43814981875277817234125603 65722472812916725851188405)
              ·
                refine ⟨6161481826210943048548913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 65722472812916725851188405 6161481826210943048548913)
                ·
                  refine ⟨4621111369658207286411685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6161481826210943048548913 4621111369658207286411685)
                  ·
                    refine ⟨866458381810913866202191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4621111369658207286411685 866458381810913866202191)
                    ·
                      rfl

theorem cell23_5062265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 5, 2, 4].length) (baseStart_5062265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5062265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5062265 prefixEnd_5062265 := by exact prefixLift 5062265
  have htrace : WordTrace (prefixWord ++ tailWord_5062265) baseStart_5062265 baseEnd_5062265 := by
    simpa [prefixWord, tailWord_5062265, baseEnd_5062265] using wordTrace_append hprefix tailTrace_5062265
  have hstable : (prefixWord ++ tailWord_5062265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5062265).length < 2 ^ (prefixWord ++ tailWord_5062265).sum := by decide
  have hdescent : baseEnd_5062265 < baseStart_5062265 := by decide
  rcases family_descends (prefixWord ++ tailWord_5062265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5062272 : List Nat := [2, 1, 1, 2, 1, 4, 3, 2, 3, 2, 2]
def baseStart_5062272 : Nat := 118140960795 + 5062272 * 2 ^ 59
def prefixEnd_5062272 : Nat := 4983230072969 + 3 ^ 40 * 5062272 * 2
def baseEnd_5062272 : Nat := 2599378739797323071219041

theorem tailTrace_5062272 : CollatzResearch.WordTrace tailWord_5062272 prefixEnd_5062272 2599378739797323071219041 := by
  unfold tailWord_5062272
  simp only [CollatzResearch.WordTrace]
  refine ⟨92318114158130293035498535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123090818877507057380664713 92318114158130293035498535)
  ·
    refine ⟨138477171237195439553247803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92318114158130293035498535 138477171237195439553247803)
    ·
      refine ⟨207715756855793159329871705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138477171237195439553247803 207715756855793159329871705)
      ·
        refine ⟨155786817641844869497403779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 207715756855793159329871705 155786817641844869497403779)
        ·
          refine ⟨233680226462767304246105669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155786817641844869497403779 233680226462767304246105669)
          ·
            refine ⟨43815042461768869546144813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 233680226462767304246105669 43815042461768869546144813)
            ·
              refine ⟨16430640923163326079804305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43815042461768869546144813 16430640923163326079804305)
              ·
                refine ⟨12322980692372494559853229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16430640923163326079804305 12322980692372494559853229)
                ·
                  refine ⟨4621117759639685459944961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12322980692372494559853229 4621117759639685459944961)
                  ·
                    refine ⟨3465838319729764094958721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4621117759639685459944961 3465838319729764094958721)
                    ·
                      refine ⟨2599378739797323071219041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3465838319729764094958721 2599378739797323071219041)
                      ·
                        rfl

theorem cell23_5062272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 2, 3, 2, 2].length) (baseStart_5062272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5062272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5062272 prefixEnd_5062272 := by exact prefixLift 5062272
  have htrace : WordTrace (prefixWord ++ tailWord_5062272) baseStart_5062272 baseEnd_5062272 := by
    simpa [prefixWord, tailWord_5062272, baseEnd_5062272] using wordTrace_append hprefix tailTrace_5062272
  have hstable : (prefixWord ++ tailWord_5062272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5062272).length < 2 ^ (prefixWord ++ tailWord_5062272).sum := by decide
  have hdescent : baseEnd_5062272 < baseStart_5062272 := by decide
  rcases family_descends (prefixWord ++ tailWord_5062272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5062275 : List Nat := [1, 1, 1, 3, 3, 1, 1, 6, 1, 2, 3]
def baseStart_5062275 : Nat := 118140960795 + 5062275 * 2 ^ 59
def prefixEnd_5062275 : Nat := 4983230072969 + 3 ^ 40 * 5062275 * 2
def baseEnd_5062275 : Nat := 2599380280239286559481527

theorem tailTrace_5062275 : CollatzResearch.WordTrace tailWord_5062275 prefixEnd_5062275 2599380280239286559481527 := by
  unfold tailWord_5062275
  simp only [CollatzResearch.WordTrace]
  refine ⟨184636337735249717583356279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123090891823499811722237519 184636337735249717583356279)
  ·
    refine ⟨276954506602874576375034419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184636337735249717583356279 276954506602874576375034419)
    ·
      refine ⟨415431759904311864562551629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 276954506602874576375034419 415431759904311864562551629)
      ·
        refine ⟨155786909964116949210956861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 415431759904311864562551629 155786909964116949210956861)
        ·
          refine ⟨58420091236543855954108823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 155786909964116949210956861 58420091236543855954108823)
          ·
            refine ⟨87630136854815783931163235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58420091236543855954108823 87630136854815783931163235)
            ·
              refine ⟨131445205282223675896744853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87630136854815783931163235 131445205282223675896744853)
              ·
                refine ⟨6161493997604234807659915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 131445205282223675896744853 6161493997604234807659915)
                ·
                  refine ⟨9242240996406352211489873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6161493997604234807659915 9242240996406352211489873)
                  ·
                    refine ⟨6931680747304764158617405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9242240996406352211489873 6931680747304764158617405)
                    ·
                      refine ⟨2599380280239286559481527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6931680747304764158617405 2599380280239286559481527)
                      ·
                        rfl

theorem cell23_5062275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 6, 1, 2, 3].length) (baseStart_5062275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5062275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5062275 prefixEnd_5062275 := by exact prefixLift 5062275
  have htrace : WordTrace (prefixWord ++ tailWord_5062275) baseStart_5062275 baseEnd_5062275 := by
    simpa [prefixWord, tailWord_5062275, baseEnd_5062275] using wordTrace_append hprefix tailTrace_5062275
  have hstable : (prefixWord ++ tailWord_5062275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5062275).length < 2 ^ (prefixWord ++ tailWord_5062275).sum := by decide
  have hdescent : baseEnd_5062275 < baseStart_5062275 := by decide
  rcases family_descends (prefixWord ++ tailWord_5062275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5062276 : List Nat := [2, 3, 2, 1, 5, 1, 1, 1, 2, 3, 2]
def baseStart_5062276 : Nat := 118140960795 + 5062276 * 2 ^ 59
def prefixEnd_5062276 : Nat := 4983230072969 + 3 ^ 40 * 5062276 * 2
def baseEnd_5062276 : Nat := 2599380793719941055569023

theorem tailTrace_5062276 : CollatzResearch.WordTrace tailWord_5062276 prefixEnd_5062276 2599380793719941055569023 := by
  unfold tailWord_5062276
  simp only [CollatzResearch.WordTrace]
  refine ⟨92318187104123047377071341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123090916138830729836095121 92318187104123047377071341)
  ·
    refine ⟨34619320164046142766401753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92318187104123047377071341 34619320164046142766401753)
    ·
      refine ⟨25964490123034607074801315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34619320164046142766401753 25964490123034607074801315)
      ·
        refine ⟨38946735184551910612201973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25964490123034607074801315 38946735184551910612201973)
        ·
          refine ⟨3651256423551741619893935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 38946735184551910612201973 3651256423551741619893935)
          ·
            refine ⟨5476884635327612429840903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3651256423551741619893935 5476884635327612429840903)
            ·
              refine ⟨8215326952991418644761355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5476884635327612429840903 8215326952991418644761355)
              ·
                refine ⟨12322990429487127967142033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8215326952991418644761355 12322990429487127967142033)
                ·
                  refine ⟨9242242822115345975356525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12322990429487127967142033 9242242822115345975356525)
                  ·
                    refine ⟨3465841058293254740758697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9242242822115345975356525 3465841058293254740758697)
                    ·
                      refine ⟨2599380793719941055569023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3465841058293254740758697 2599380793719941055569023)
                      ·
                        rfl

theorem cell23_5062276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 1, 1, 2, 3, 2].length) (baseStart_5062276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5062276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5062276 prefixEnd_5062276 := by exact prefixLift 5062276
  have htrace : WordTrace (prefixWord ++ tailWord_5062276) baseStart_5062276 baseEnd_5062276 := by
    simpa [prefixWord, tailWord_5062276, baseEnd_5062276] using wordTrace_append hprefix tailTrace_5062276
  have hstable : (prefixWord ++ tailWord_5062276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5062276).length < 2 ^ (prefixWord ++ tailWord_5062276).sum := by decide
  have hdescent : baseEnd_5062276 < baseStart_5062276 := by decide
  rcases family_descends (prefixWord ++ tailWord_5062276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5062322 : List Nat := [3, 2, 1, 1, 1, 2, 2, 5, 2, 1, 3]
def baseStart_5062322 : Nat := 118140960795 + 5062322 * 2 ^ 59
def prefixEnd_5062322 : Nat := 4983230072969 + 3 ^ 40 * 5062322 * 2
def baseEnd_5062322 : Nat := 2599404413830047875593811

theorem tailTrace_5062322 : CollatzResearch.WordTrace tailWord_5062322 prefixEnd_5062322 2599404413830047875593811 := by
  unfold tailWord_5062322
  simp only [CollatzResearch.WordTrace]
  refine ⟨46159512991519861152579305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123092034644052963073544813 46159512991519861152579305)
  ·
    refine ⟨34619634743639895864434479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46159512991519861152579305 34619634743639895864434479)
    ·
      refine ⟨51929452115459843796651719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34619634743639895864434479 51929452115459843796651719)
      ·
        refine ⟨77894178173189765694977579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51929452115459843796651719 77894178173189765694977579)
        ·
          refine ⟨116841267259784648542466369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77894178173189765694977579 116841267259784648542466369)
          ·
            refine ⟨87630950444838486406849777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 116841267259784648542466369 87630950444838486406849777)
            ·
              refine ⟨65723212833628864805137333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87630950444838486406849777 65723212833628864805137333)
              ·
                refine ⟨6161551203152706075481625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 65723212833628864805137333 6161551203152706075481625)
                ·
                  refine ⟨4621163402364529556611219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6161551203152706075481625 4621163402364529556611219)
                  ·
                    refine ⟨6931745103546794334916829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4621163402364529556611219 6931745103546794334916829)
                    ·
                      refine ⟨2599404413830047875593811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6931745103546794334916829 2599404413830047875593811)
                      ·
                        rfl

theorem cell23_5062322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 5, 2, 1, 3].length) (baseStart_5062322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5062322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5062322 prefixEnd_5062322 := by exact prefixLift 5062322
  have htrace : WordTrace (prefixWord ++ tailWord_5062322) baseStart_5062322 baseEnd_5062322 := by
    simpa [prefixWord, tailWord_5062322, baseEnd_5062322] using wordTrace_append hprefix tailTrace_5062322
  have hstable : (prefixWord ++ tailWord_5062322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5062322).length < 2 ^ (prefixWord ++ tailWord_5062322).sum := by decide
  have hdescent : baseEnd_5062322 < baseStart_5062322 := by decide
  rcases family_descends (prefixWord ++ tailWord_5062322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5062326 : List Nat := [5, 1, 3, 1, 1, 2, 2, 2, 1, 2, 3]
def baseStart_5062326 : Nat := 118140960795 + 5062326 * 2 ^ 59
def prefixEnd_5062326 : Nat := 4983230072969 + 3 ^ 40 * 5062326 * 2
def baseEnd_5062326 : Nat := 2599406467752665859943793

theorem tailTrace_5062326 : CollatzResearch.WordTrace tailWord_5062326 prefixEnd_5062326 2599406467752665859943793 := by
  unfold tailWord_5062326
  simp only [CollatzResearch.WordTrace]
  refine ⟨11539887366129059580841427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 123092131905376635528975221 11539887366129059580841427)
  ·
    refine ⟨17309831049193589371262141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11539887366129059580841427 17309831049193589371262141)
    ·
      refine ⟨6491186643447596014223303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17309831049193589371262141 6491186643447596014223303)
      ·
        refine ⟨9736779965171394021334955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6491186643447596014223303 9736779965171394021334955)
        ·
          refine ⟨14605169947757091032002433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9736779965171394021334955 14605169947757091032002433)
          ·
            refine ⟨10953877460817818274001825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14605169947757091032002433 10953877460817818274001825)
            ·
              refine ⟨8215408095613363705501369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10953877460817818274001825 8215408095613363705501369)
              ·
                refine ⟨6161556071710022779126027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8215408095613363705501369 6161556071710022779126027)
                ·
                  refine ⟨9242334107565034168689041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6161556071710022779126027 9242334107565034168689041)
                  ·
                    refine ⟨6931750580673775626516781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9242334107565034168689041 6931750580673775626516781)
                    ·
                      refine ⟨2599406467752665859943793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6931750580673775626516781 2599406467752665859943793)
                      ·
                        rfl

theorem cell23_5062326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 2, 2, 1, 2, 3].length) (baseStart_5062326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5062326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5062326 prefixEnd_5062326 := by exact prefixLift 5062326
  have htrace : WordTrace (prefixWord ++ tailWord_5062326) baseStart_5062326 baseEnd_5062326 := by
    simpa [prefixWord, tailWord_5062326, baseEnd_5062326] using wordTrace_append hprefix tailTrace_5062326
  have hstable : (prefixWord ++ tailWord_5062326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5062326).length < 2 ^ (prefixWord ++ tailWord_5062326).sum := by decide
  have hdescent : baseEnd_5062326 < baseStart_5062326 := by decide
  rcases family_descends (prefixWord ++ tailWord_5062326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5062328 : List Nat := [2, 1, 2, 1, 2, 1, 1, 4, 2, 3, 4]
def baseStart_5062328 : Nat := 118140960795 + 5062328 * 2 ^ 59
def prefixEnd_5062328 : Nat := 4983230072969 + 3 ^ 40 * 5062328 * 2
def baseEnd_5062328 : Nat := 2599407494713974852118783

theorem tailTrace_5062328 : CollatzResearch.WordTrace tailWord_5062328 prefixEnd_5062328 2599407494713974852118783 := by
  unfold tailWord_5062328
  simp only [CollatzResearch.WordTrace]
  refine ⟨92319135402028853817517819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123092180536038471756690425 92319135402028853817517819)
  ·
    refine ⟨138478703103043280726276729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92319135402028853817517819 138478703103043280726276729)
    ·
      refine ⟨103859027327282460544707547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138478703103043280726276729 103859027327282460544707547)
      ·
        refine ⟨155788540990923690817061321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103859027327282460544707547 155788540990923690817061321)
        ·
          refine ⟨116841405743192768112795991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 155788540990923690817061321 116841405743192768112795991)
          ·
            refine ⟨175262108614789152169193987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116841405743192768112795991 175262108614789152169193987)
            ·
              refine ⟨262893162922183728253790981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 175262108614789152169193987 262893162922183728253790981)
              ·
                refine ⟨49292468047909449047585809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 262893162922183728253790981 49292468047909449047585809)
                ·
                  refine ⟨36969351035932086785689357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49292468047909449047585809 36969351035932086785689357)
                  ·
                    refine ⟨13863506638474532544633509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36969351035932086785689357 13863506638474532544633509)
                    ·
                      refine ⟨2599407494713974852118783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13863506638474532544633509 2599407494713974852118783)
                      ·
                        rfl

theorem cell23_5062328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 4, 2, 3, 4].length) (baseStart_5062328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5062328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5062328 prefixEnd_5062328 := by exact prefixLift 5062328
  have htrace : WordTrace (prefixWord ++ tailWord_5062328) baseStart_5062328 baseEnd_5062328 := by
    simpa [prefixWord, tailWord_5062328, baseEnd_5062328] using wordTrace_append hprefix tailTrace_5062328
  have hstable : (prefixWord ++ tailWord_5062328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5062328).length < 2 ^ (prefixWord ++ tailWord_5062328).sum := by decide
  have hdescent : baseEnd_5062328 < baseStart_5062328 := by decide
  rcases family_descends (prefixWord ++ tailWord_5062328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5062435 : List Nat := [1, 1, 1, 4, 2, 1, 2, 2, 4, 1, 4]
def baseStart_5062435 : Nat := 118140960795 + 5062435 * 2 ^ 59
def prefixEnd_5062435 : Nat := 4983230072969 + 3 ^ 40 * 5062435 * 2
def baseEnd_5062435 : Nat := 2599462437144005933480791

theorem tailTrace_5062435 : CollatzResearch.WordTrace tailWord_5062435 prefixEnd_5062435 2599462437144005933480791 := by
  unfold tailWord_5062435
  simp only [CollatzResearch.WordTrace]
  refine ⟨184642173414670064909180759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123094782276446709939453839 184642173414670064909180759)
  ·
    refine ⟨276963260122005097363771139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184642173414670064909180759 276963260122005097363771139)
    ·
      refine ⟨415444890183007646045656709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 276963260122005097363771139 415444890183007646045656709)
      ·
        refine ⟨77895916909313933633560633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 415444890183007646045656709 77895916909313933633560633)
        ·
          refine ⟨58421937681985450225170475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77895916909313933633560633 58421937681985450225170475)
          ·
            refine ⟨87632906522978175337755713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58421937681985450225170475 87632906522978175337755713)
            ·
              refine ⟨65724679892233631503316785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87632906522978175337755713 65724679892233631503316785)
              ·
                refine ⟨49293509919175223627487589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65724679892233631503316785 49293509919175223627487589)
                ·
                  refine ⟨9242533109845354430153923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49293509919175223627487589 9242533109845354430153923)
                  ·
                    refine ⟨13863799664768031645230885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9242533109845354430153923 13863799664768031645230885)
                    ·
                      refine ⟨2599462437144005933480791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13863799664768031645230885 2599462437144005933480791)
                      ·
                        rfl

theorem cell23_5062435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 2, 4, 1, 4].length) (baseStart_5062435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5062435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5062435 prefixEnd_5062435 := by exact prefixLift 5062435
  have htrace : WordTrace (prefixWord ++ tailWord_5062435) baseStart_5062435 baseEnd_5062435 := by
    simpa [prefixWord, tailWord_5062435, baseEnd_5062435] using wordTrace_append hprefix tailTrace_5062435
  have hstable : (prefixWord ++ tailWord_5062435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5062435).length < 2 ^ (prefixWord ++ tailWord_5062435).sum := by decide
  have hdescent : baseEnd_5062435 < baseStart_5062435 := by decide
  rcases family_descends (prefixWord ++ tailWord_5062435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5062505 : List Nat := [1, 2, 1, 1, 1, 3, 1, 5, 3, 5]
def baseStart_5062505 : Nat := 118140960795 + 5062505 * 2 ^ 59
def prefixEnd_5062505 : Nat := 4983230072969 + 3 ^ 40 * 5062505 * 2
def baseEnd_5062505 : Nat := 866499460263273553201823

theorem tailTrace_5062505 : CollatzResearch.WordTrace tailWord_5062505 prefixEnd_5062505 866499460263273553201823 := by
  unfold tailWord_5062505
  simp only [CollatzResearch.WordTrace]
  refine ⟨184644726524416466864228969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123096484349610977909485979 184644726524416466864228969)
  ·
    refine ⟨138483544893312350148171727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184644726524416466864228969 138483544893312350148171727)
    ·
      refine ⟨207725317339968525222257591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138483544893312350148171727 207725317339968525222257591)
      ·
        refine ⟨311587976009952787833386387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 207725317339968525222257591 311587976009952787833386387)
        ·
          refine ⟨467381964014929181750079581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 311587976009952787833386387 467381964014929181750079581)
          ·
            refine ⟨175268236505598443156279843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 467381964014929181750079581 175268236505598443156279843)
            ·
              refine ⟨262902354758397664734419765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 175268236505598443156279843 262902354758397664734419765)
              ·
                refine ⟨24647095758599781068851853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 262902354758397664734419765 24647095758599781068851853)
                ·
                  refine ⟨9242660909474917900819445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24647095758599781068851853 9242660909474917900819445)
                  ·
                    refine ⟨866499460263273553201823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9242660909474917900819445 866499460263273553201823)
                    ·
                      rfl

theorem cell23_5062505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 5, 3, 5].length) (baseStart_5062505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5062505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5062505 prefixEnd_5062505 := by exact prefixLift 5062505
  have htrace : WordTrace (prefixWord ++ tailWord_5062505) baseStart_5062505 baseEnd_5062505 := by
    simpa [prefixWord, tailWord_5062505, baseEnd_5062505] using wordTrace_append hprefix tailTrace_5062505
  have hstable : (prefixWord ++ tailWord_5062505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5062505).length < 2 ^ (prefixWord ++ tailWord_5062505).sum := by decide
  have hdescent : baseEnd_5062505 < baseStart_5062505 := by decide
  rcases family_descends (prefixWord ++ tailWord_5062505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5062522 : List Nat := [3, 1, 1, 1, 1, 1, 6, 3, 1, 5]
def baseStart_5062522 : Nat := 118140960795 + 5062522 * 2 ^ 59
def prefixEnd_5062522 : Nat := 4983230072969 + 3 ^ 40 * 5062522 * 2
def baseEnd_5062522 : Nat := 866502369986982364364297

theorem tailTrace_5062522 : CollatzResearch.WordTrace tailWord_5062522 prefixEnd_5062522 866502369986982364364297 := by
  unfold tailWord_5062522
  simp only [CollatzResearch.WordTrace]
  refine ⟨46161336641338719691899455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123096897710236585845065213 46161336641338719691899455)
  ·
    refine ⟨69242004962008079537849183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46161336641338719691899455 69242004962008079537849183)
    ·
      refine ⟨103863007443012119306773775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69242004962008079537849183 103863007443012119306773775)
      ·
        refine ⟨155794511164518178960160663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103863007443012119306773775 155794511164518178960160663)
        ·
          refine ⟨233691766746777268440240995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155794511164518178960160663 233691766746777268440240995)
          ·
            refine ⟨350537650120165902660361493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 233691766746777268440240995 350537650120165902660361493)
            ·
              refine ⟨16431452349382776687204445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 350537650120165902660361493 16431452349382776687204445)
              ·
                refine ⟨6161794631018541257701667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16431452349382776687204445 6161794631018541257701667)
                ·
                  refine ⟨9242691946527811886552501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6161794631018541257701667 9242691946527811886552501)
                  ·
                    refine ⟨866502369986982364364297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9242691946527811886552501 866502369986982364364297)
                    ·
                      rfl

theorem cell23_5062522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 3, 1, 5].length) (baseStart_5062522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5062522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5062522 prefixEnd_5062522 := by exact prefixLift 5062522
  have htrace : WordTrace (prefixWord ++ tailWord_5062522) baseStart_5062522 baseEnd_5062522 := by
    simpa [prefixWord, tailWord_5062522, baseEnd_5062522] using wordTrace_append hprefix tailTrace_5062522
  have hstable : (prefixWord ++ tailWord_5062522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5062522).length < 2 ^ (prefixWord ++ tailWord_5062522).sum := by decide
  have hdescent : baseEnd_5062522 < baseStart_5062522 := by decide
  rcases family_descends (prefixWord ++ tailWord_5062522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5062556 : List Nat := [2, 2, 3, 3, 1, 3, 1, 2, 1, 5]
def baseStart_5062556 : Nat := 118140960795 + 5062556 * 2 ^ 59
def prefixEnd_5062556 : Nat := 4983230072969 + 3 ^ 40 * 5062556 * 2
def baseEnd_5062556 : Nat := 866508189434399986689245

theorem tailTrace_5062556 : CollatzResearch.WordTrace tailWord_5062556 prefixEnd_5062556 866508189434399986689245 := by
  unfold tailWord_5062556
  simp only [CollatzResearch.WordTrace]
  refine ⟨92323293323615851287167761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123097724431487801716223681 92323293323615851287167761)
  ·
    refine ⟨69242469992711888465375821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92323293323615851287167761 69242469992711888465375821)
    ·
      refine ⟨25965926247266958174515933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69242469992711888465375821 25965926247266958174515933)
      ·
        refine ⟨9737222342725109315443475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25965926247266958174515933 9737222342725109315443475)
        ·
          refine ⟨14605833514087663973165213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9737222342725109315443475 14605833514087663973165213)
          ·
            refine ⟨5477187567782873989936955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14605833514087663973165213 5477187567782873989936955)
            ·
              refine ⟨8215781351674310984905433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5477187567782873989936955 8215781351674310984905433)
              ·
                refine ⟨6161836013755733238679075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8215781351674310984905433 6161836013755733238679075)
                ·
                  refine ⟨9242754020633599858018613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6161836013755733238679075 9242754020633599858018613)
                  ·
                    refine ⟨866508189434399986689245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9242754020633599858018613 866508189434399986689245)
                    ·
                      rfl

theorem cell23_5062556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 1, 2, 1, 5].length) (baseStart_5062556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5062556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5062556 prefixEnd_5062556 := by exact prefixLift 5062556
  have htrace : WordTrace (prefixWord ++ tailWord_5062556) baseStart_5062556 baseEnd_5062556 := by
    simpa [prefixWord, tailWord_5062556, baseEnd_5062556] using wordTrace_append hprefix tailTrace_5062556
  have hstable : (prefixWord ++ tailWord_5062556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5062556).length < 2 ^ (prefixWord ++ tailWord_5062556).sum := by decide
  have hdescent : baseEnd_5062556 < baseStart_5062556 := by decide
  rcases family_descends (prefixWord ++ tailWord_5062556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5062559 : List Nat := [1, 1, 2, 5, 3, 1, 1, 1, 3, 1, 4]
def baseStart_5062559 : Nat := 118140960795 + 5062559 * 2 ^ 59
def prefixEnd_5062559 : Nat := 4983230072969 + 3 ^ 40 * 5062559 * 2
def baseEnd_5062559 : Nat := 2599526108745163448330221

theorem tailTrace_5062559 : CollatzResearch.WordTrace tailWord_5062559 prefixEnd_5062559 2599526108745163448330221 := by
  unfold tailWord_5062559
  simp only [CollatzResearch.WordTrace]
  refine ⟨184646696066220834086694731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123097797377480556057796487 184646696066220834086694731)
  ·
    refine ⟨276970044099331251130042097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184646696066220834086694731 276970044099331251130042097)
    ·
      refine ⟨207727533074498438347531573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 276970044099331251130042097 207727533074498438347531573)
      ·
        refine ⟨19474456225734228595081085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 207727533074498438347531573 19474456225734228595081085)
        ·
          refine ⟨7302921084650335723155407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19474456225734228595081085 7302921084650335723155407)
          ·
            refine ⟨10954381626975503584733111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7302921084650335723155407 10954381626975503584733111)
            ·
              refine ⟨16431572440463255377099667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10954381626975503584733111 16431572440463255377099667)
              ·
                refine ⟨24647358660694883065649501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16431572440463255377099667 24647358660694883065649501)
                ·
                  refine ⟨9242759497760581149618563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24647358660694883065649501 9242759497760581149618563)
                  ·
                    refine ⟨13864139246640871724427845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9242759497760581149618563 13864139246640871724427845)
                    ·
                      refine ⟨2599526108745163448330221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13864139246640871724427845 2599526108745163448330221)
                      ·
                        rfl

theorem cell23_5062559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 1, 3, 1, 4].length) (baseStart_5062559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5062559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5062559 prefixEnd_5062559 := by exact prefixLift 5062559
  have htrace : WordTrace (prefixWord ++ tailWord_5062559) baseStart_5062559 baseEnd_5062559 := by
    simpa [prefixWord, tailWord_5062559, baseEnd_5062559] using wordTrace_append hprefix tailTrace_5062559
  have hstable : (prefixWord ++ tailWord_5062559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5062559).length < 2 ^ (prefixWord ++ tailWord_5062559).sum := by decide
  have hdescent : baseEnd_5062559 < baseStart_5062559 := by decide
  rcases family_descends (prefixWord ++ tailWord_5062559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5062592 : List Nat := [2, 1, 1, 2, 3, 2, 1, 2, 3, 3, 3]
def baseStart_5062592 : Nat := 118140960795 + 5062592 * 2 ^ 59
def prefixEnd_5062592 : Nat := 4983230072969 + 3 ^ 40 * 5062592 * 2
def baseEnd_5062592 : Nat := 2599543053606761819217569

theorem tailTrace_5062592 : CollatzResearch.WordTrace tailWord_5062592 prefixEnd_5062592 2599543053606761819217569 := by
  unfold tailWord_5062592
  simp only [CollatzResearch.WordTrace]
  refine ⟨92323949837550640361323015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123098599783400853815097353 92323949837550640361323015)
  ·
    refine ⟨138485924756325960541984523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92323949837550640361323015 138485924756325960541984523)
    ·
      refine ⟨207728887134488940812976785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138485924756325960541984523 207728887134488940812976785)
      ·
        refine ⟨155796665350866705609732589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 207728887134488940812976785 155796665350866705609732589)
        ·
          refine ⟨58423749506575014603649721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 155796665350866705609732589 58423749506575014603649721)
          ·
            refine ⟨43817812129931260952737291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58423749506575014603649721 43817812129931260952737291)
            ·
              refine ⟨65726718194896891429105937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43817812129931260952737291 65726718194896891429105937)
              ·
                refine ⟨49295038646172668571829453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65726718194896891429105937 49295038646172668571829453)
                ·
                  refine ⟨18485639492314750714436045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49295038646172668571829453 18485639492314750714436045)
                  ·
                    refine ⟨6932114809618031517913517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18485639492314750714436045 6932114809618031517913517)
                    ·
                      refine ⟨2599543053606761819217569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6932114809618031517913517 2599543053606761819217569)
                      ·
                        rfl

theorem cell23_5062592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 2, 3, 3, 3].length) (baseStart_5062592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5062592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5062592 prefixEnd_5062592 := by exact prefixLift 5062592
  have htrace : WordTrace (prefixWord ++ tailWord_5062592) baseStart_5062592 baseEnd_5062592 := by
    simpa [prefixWord, tailWord_5062592, baseEnd_5062592] using wordTrace_append hprefix tailTrace_5062592
  have hstable : (prefixWord ++ tailWord_5062592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5062592).length < 2 ^ (prefixWord ++ tailWord_5062592).sum := by decide
  have hdescent : baseEnd_5062592 < baseStart_5062592 := by decide
  rcases family_descends (prefixWord ++ tailWord_5062592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5062612 : List Nat := [2, 4, 1, 2, 1, 1, 1, 2, 2, 7]
def baseStart_5062612 : Nat := 118140960795 + 5062612 * 2 ^ 59
def prefixEnd_5062612 : Nat := 4983230072969 + 3 ^ 40 * 5062612 * 2
def baseEnd_5062612 : Nat := 866517774406617246989159

theorem tailTrace_5062612 : CollatzResearch.WordTrace tailWord_5062612 prefixEnd_5062612 866517774406617246989159 := by
  unfold tailWord_5062612
  simp only [CollatzResearch.WordTrace]
  refine ⟨92324314567514412069187045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123099086090019216092249393 92324314567514412069187045)
  ·
    refine ⟨17310808981408952262972571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 92324314567514412069187045 17310808981408952262972571)
    ·
      refine ⟨25966213472113428394458857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17310808981408952262972571 25966213472113428394458857)
      ·
        refine ⟨19474660104085071295844143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25966213472113428394458857 19474660104085071295844143)
        ·
          refine ⟨29211990156127606943766215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19474660104085071295844143 29211990156127606943766215)
          ·
            refine ⟨43817985234191410415649323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29211990156127606943766215 43817985234191410415649323)
            ·
              refine ⟨65726977851287115623473985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43817985234191410415649323 65726977851287115623473985)
              ·
                refine ⟨49295233388465336717605489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65726977851287115623473985 49295233388465336717605489)
                ·
                  refine ⟨36971425041349002538204117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49295233388465336717605489 36971425041349002538204117)
                  ·
                    refine ⟨866517774406617246989159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36971425041349002538204117 866517774406617246989159)
                    ·
                      rfl

theorem cell23_5062612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 2, 2, 7].length) (baseStart_5062612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5062612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5062612 prefixEnd_5062612 := by exact prefixLift 5062612
  have htrace : WordTrace (prefixWord ++ tailWord_5062612) baseStart_5062612 baseEnd_5062612 := by
    simpa [prefixWord, tailWord_5062612, baseEnd_5062612] using wordTrace_append hprefix tailTrace_5062612
  have hstable : (prefixWord ++ tailWord_5062612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5062612).length < 2 ^ (prefixWord ++ tailWord_5062612).sum := by decide
  have hdescent : baseEnd_5062612 < baseStart_5062612 := by decide
  rcases family_descends (prefixWord ++ tailWord_5062612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5062660 : List Nat := [2, 3, 2, 4, 2, 1, 1, 1, 1, 3, 3]
def baseStart_5062660 : Nat := 118140960795 + 5062660 * 2 ^ 59
def prefixEnd_5062660 : Nat := 4983230072969 + 3 ^ 40 * 5062660 * 2
def baseEnd_5062660 : Nat := 2599577970291267553167257

theorem tailTrace_5062660 : CollatzResearch.WordTrace tailWord_5062660 prefixEnd_5062660 2599577970291267553167257 := by
  unfold tailWord_5062660
  simp only [CollatzResearch.WordTrace]
  refine ⟨92325189919427464168060717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123100253225903285557414289 92325189919427464168060717)
  ·
    refine ⟨34621946219785299063022769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92325189919427464168060717 34621946219785299063022769)
    ·
      refine ⟨25966459664838974297267077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34621946219785299063022769 25966459664838974297267077)
      ·
        refine ⟨4868711187157307680737577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25966459664838974297267077 4868711187157307680737577)
        ·
          refine ⟨3651533390367980760553183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4868711187157307680737577 3651533390367980760553183)
          ·
            refine ⟨5477300085551971140829775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3651533390367980760553183 5477300085551971140829775)
            ·
              refine ⟨8215950128327956711244663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5477300085551971140829775 8215950128327956711244663)
              ·
                refine ⟨12323925192491935066866995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8215950128327956711244663 12323925192491935066866995)
                ·
                  refine ⟨18485887788737902600300493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12323925192491935066866995 18485887788737902600300493)
                  ·
                    refine ⟨6932207920776713475112685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18485887788737902600300493 6932207920776713475112685)
                    ·
                      refine ⟨2599577970291267553167257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6932207920776713475112685 2599577970291267553167257)
                      ·
                        rfl

theorem cell23_5062660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 1, 1, 1, 3, 3].length) (baseStart_5062660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5062660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5062660 prefixEnd_5062660 := by exact prefixLift 5062660
  have htrace : WordTrace (prefixWord ++ tailWord_5062660) baseStart_5062660 baseEnd_5062660 := by
    simpa [prefixWord, tailWord_5062660, baseEnd_5062660] using wordTrace_append hprefix tailTrace_5062660
  have hstable : (prefixWord ++ tailWord_5062660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5062660).length < 2 ^ (prefixWord ++ tailWord_5062660).sum := by decide
  have hdescent : baseEnd_5062660 < baseStart_5062660 := by decide
  rcases family_descends (prefixWord ++ tailWord_5062660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5062732 : List Nat := [2, 2, 1, 3, 1, 1, 2, 1, 2, 8]
def baseStart_5062732 : Nat := 118140960795 + 5062732 * 2 ^ 59
def prefixEnd_5062732 : Nat := 4983230072969 + 3 ^ 40 * 5062732 * 2
def baseEnd_5062732 : Nat := 866538313632797090488975

theorem tailTrace_5062732 : CollatzResearch.WordTrace tailWord_5062732 prefixEnd_5062732 866538313632797090488975 := by
  unfold tailWord_5062732
  simp only [CollatzResearch.WordTrace]
  refine ⟨92326502947297042316371225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123102003929729389755161633 92326502947297042316371225)
  ·
    refine ⟨69244877210472781737278419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92326502947297042316371225 69244877210472781737278419)
    ·
      refine ⟨103867315815709172605917629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69244877210472781737278419 103867315815709172605917629)
      ·
        refine ⟨38950243430890939727219111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 103867315815709172605917629 38950243430890939727219111)
        ·
          refine ⟨58425365146336409590828667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38950243430890939727219111 58425365146336409590828667)
          ·
            refine ⟨87638047719504614386243001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58425365146336409590828667 87638047719504614386243001)
            ·
              refine ⟨65728535789628460789682251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87638047719504614386243001 65728535789628460789682251)
              ·
                refine ⟨98592803684442691184523377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65728535789628460789682251 98592803684442691184523377)
                ·
                  refine ⟨73944602763332018388392533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 98592803684442691184523377 73944602763332018388392533)
                  ·
                    refine ⟨866538313632797090488975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 73944602763332018388392533 866538313632797090488975)
                    ·
                      rfl

theorem cell23_5062732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 1, 2, 8].length) (baseStart_5062732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5062732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5062732 prefixEnd_5062732 := by exact prefixLift 5062732
  have htrace : WordTrace (prefixWord ++ tailWord_5062732) baseStart_5062732 baseEnd_5062732 := by
    simpa [prefixWord, tailWord_5062732, baseEnd_5062732] using wordTrace_append hprefix tailTrace_5062732
  have hstable : (prefixWord ++ tailWord_5062732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5062732).length < 2 ^ (prefixWord ++ tailWord_5062732).sum := by decide
  have hdescent : baseEnd_5062732 < baseStart_5062732 := by decide
  rcases family_descends (prefixWord ++ tailWord_5062732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5062766 : List Nat := [4, 1, 2, 2, 1, 1, 2, 3, 3, 4]
def baseStart_5062766 : Nat := 118140960795 + 5062766 * 2 ^ 59
def prefixEnd_5062766 : Nat := 4983230072969 + 3 ^ 40 * 5062766 * 2
def baseEnd_5062766 : Nat := 866544133080214712813923

theorem tailTrace_5062766 : CollatzResearch.WordTrace tailWord_5062766 prefixEnd_5062766 866544133080214712813923 := by
  unfold tailWord_5062766
  simp only [CollatzResearch.WordTrace]
  refine ⟨23081780747058863554935019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 123102830650980605626320101 23081780747058863554935019)
  ·
    refine ⟨34622671120588295332402529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23081780747058863554935019 34622671120588295332402529)
    ·
      refine ⟨25967003340441221499301897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34622671120588295332402529 25967003340441221499301897)
      ·
        refine ⟨19475252505330916124476423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25967003340441221499301897 19475252505330916124476423)
        ·
          refine ⟨29212878757996374186714635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19475252505330916124476423 29212878757996374186714635)
          ·
            refine ⟨43819318136994561280071953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29212878757996374186714635 43819318136994561280071953)
            ·
              refine ⟨32864488602745920960053965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43819318136994561280071953 32864488602745920960053965)
              ·
                refine ⟨12324183226029720360020237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32864488602745920960053965 12324183226029720360020237)
                ·
                  refine ⟨4621568709761145135007589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12324183226029720360020237 4621568709761145135007589)
                  ·
                    refine ⟨866544133080214712813923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4621568709761145135007589 866544133080214712813923)
                    ·
                      rfl

theorem cell23_5062766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 3, 3, 4].length) (baseStart_5062766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5062766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5062766 prefixEnd_5062766 := by exact prefixLift 5062766
  have htrace : WordTrace (prefixWord ++ tailWord_5062766) baseStart_5062766 baseEnd_5062766 := by
    simpa [prefixWord, tailWord_5062766, baseEnd_5062766] using wordTrace_append hprefix tailTrace_5062766
  have hstable : (prefixWord ++ tailWord_5062766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5062766).length < 2 ^ (prefixWord ++ tailWord_5062766).sum := by decide
  have hdescent : baseEnd_5062766 < baseStart_5062766 := by decide
  rcases family_descends (prefixWord ++ tailWord_5062766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5062859 : List Nat := [1, 1, 1, 1, 3, 2, 4, 1, 3, 2, 4]
def baseStart_5062859 : Nat := 118140960795 + 5062859 * 2 ^ 59
def prefixEnd_5062859 : Nat := 4983230072969 + 3 ^ 40 * 5062859 * 2
def baseEnd_5062859 : Nat := 2599680152941512274578841

theorem tailTrace_5062859 : CollatzResearch.WordTrace tailWord_5062859 prefixEnd_5062859 2599680152941512274578841 := by
  unfold tailWord_5062859
  simp only [CollatzResearch.WordTrace]
  refine ⟨184657637965133985322615631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123105091976755990215077087 184657637965133985322615631)
  ·
    refine ⟨276986456947700977983923447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184657637965133985322615631 276986456947700977983923447)
    ·
      refine ⟨415479685421551466975885171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 276986456947700977983923447 415479685421551466975885171)
      ·
        refine ⟨623219528132327200463827757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 415479685421551466975885171 623219528132327200463827757)
        ·
          refine ⟨233707323049622700173935409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 623219528132327200463827757 233707323049622700173935409)
          ·
            refine ⟨175280492287217025130451557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 233707323049622700173935409 175280492287217025130451557)
            ·
              refine ⟨32865092303853192211959667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 175280492287217025130451557 32865092303853192211959667)
              ·
                refine ⟨49297638455779788317939501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32865092303853192211959667 49297638455779788317939501)
                ·
                  refine ⟨18486614420917420619227313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49297638455779788317939501 18486614420917420619227313)
                  ·
                    refine ⟨13864960815688065464420485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18486614420917420619227313 13864960815688065464420485)
                    ·
                      refine ⟨2599680152941512274578841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13864960815688065464420485 2599680152941512274578841)
                      ·
                        rfl

theorem cell23_5062859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 1, 3, 2, 4].length) (baseStart_5062859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5062859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5062859 prefixEnd_5062859 := by exact prefixLift 5062859
  have htrace : WordTrace (prefixWord ++ tailWord_5062859) baseStart_5062859 baseEnd_5062859 := by
    simpa [prefixWord, tailWord_5062859, baseEnd_5062859] using wordTrace_append hprefix tailTrace_5062859
  have hstable : (prefixWord ++ tailWord_5062859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5062859).length < 2 ^ (prefixWord ++ tailWord_5062859).sum := by decide
  have hdescent : baseEnd_5062859 < baseStart_5062859 := by decide
  rcases family_descends (prefixWord ++ tailWord_5062859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5062866 : List Nat := [3, 2, 2, 2, 1, 2, 1, 3, 1, 1, 5]
def baseStart_5062866 : Nat := 118140960795 + 5062866 * 2 ^ 59
def prefixEnd_5062866 : Nat := 4983230072969 + 3 ^ 40 * 5062866 * 2
def baseEnd_5062866 : Nat := 2599683747306093747191309

theorem tailTrace_5062866 : CollatzResearch.WordTrace tailWord_5062866 prefixEnd_5062866 2599683747306093747191309 := by
  unfold tailWord_5062866
  simp only [CollatzResearch.WordTrace]
  refine ⟨46164473319027156379530113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123105262184072417012080301 46164473319027156379530113)
  ·
    refine ⟨34623354989270367284647585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46164473319027156379530113 34623354989270367284647585)
    ·
      refine ⟨25967516241952775463485689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34623354989270367284647585 25967516241952775463485689)
      ·
        refine ⟨19475637181464581597614267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25967516241952775463485689 19475637181464581597614267)
        ·
          refine ⟨29213455772196872396421401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19475637181464581597614267 29213455772196872396421401)
          ·
            refine ⟨21910091829147654297316051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29213455772196872396421401 21910091829147654297316051)
            ·
              refine ⟨32865137743721481445974077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21910091829147654297316051 32865137743721481445974077)
              ·
                refine ⟨12324426653895555542240279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32865137743721481445974077 12324426653895555542240279)
                ·
                  refine ⟨18486639980843333313360419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12324426653895555542240279 18486639980843333313360419)
                  ·
                    refine ⟨27729959971264999970040629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18486639980843333313360419 27729959971264999970040629)
                    ·
                      refine ⟨2599683747306093747191309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27729959971264999970040629 2599683747306093747191309)
                      ·
                        rfl

theorem cell23_5062866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 3, 1, 1, 5].length) (baseStart_5062866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5062866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5062866 prefixEnd_5062866 := by exact prefixLift 5062866
  have htrace : WordTrace (prefixWord ++ tailWord_5062866) baseStart_5062866 baseEnd_5062866 := by
    simpa [prefixWord, tailWord_5062866, baseEnd_5062866] using wordTrace_append hprefix tailTrace_5062866
  have hstable : (prefixWord ++ tailWord_5062866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5062866).length < 2 ^ (prefixWord ++ tailWord_5062866).sum := by decide
  have hdescent : baseEnd_5062866 < baseStart_5062866 := by decide
  rcases family_descends (prefixWord ++ tailWord_5062866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5062909 : List Nat := [1, 4, 1, 1, 1, 1, 1, 3, 1, 4, 5]
def baseStart_5062909 : Nat := 118140960795 + 5062909 * 2 ^ 59
def prefixEnd_5062909 : Nat := 4983230072969 + 3 ^ 40 * 5062909 * 2
def baseEnd_5062909 : Nat := 2599705826974237078953611

theorem tailTrace_5062909 : CollatzResearch.WordTrace tailWord_5062909 prefixEnd_5062909 2599705826974237078953611 := by
  unfold tailWord_5062909
  simp only [CollatzResearch.WordTrace]
  refine ⟨184659461614952843861935781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123106307743301895907957187 184659461614952843861935781)
  ·
    refine ⟨34623649052803658224112959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 184659461614952843861935781 34623649052803658224112959)
    ·
      refine ⟨51935473579205487336169439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34623649052803658224112959 51935473579205487336169439)
      ·
        refine ⟨77903210368808231004254159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51935473579205487336169439 77903210368808231004254159)
        ·
          refine ⟨116854815553212346506381239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77903210368808231004254159 116854815553212346506381239)
          ·
            refine ⟨175282223329818519759571859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116854815553212346506381239 175282223329818519759571859)
            ·
              refine ⟨262923334994727779639357789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 175282223329818519759571859 262923334994727779639357789)
              ·
                refine ⟨98596250623022917364759171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 262923334994727779639357789 98596250623022917364759171)
                ·
                  refine ⟨147894375934534376047138757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 98596250623022917364759171 147894375934534376047138757)
                  ·
                    refine ⟨27730195487725195508838517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 147894375934534376047138757 27730195487725195508838517)
                    ·
                      refine ⟨2599705826974237078953611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27730195487725195508838517 2599705826974237078953611)
                      ·
                        rfl

theorem cell23_5062909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 3, 1, 4, 5].length) (baseStart_5062909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5062909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5062909 prefixEnd_5062909 := by exact prefixLift 5062909
  have htrace : WordTrace (prefixWord ++ tailWord_5062909) baseStart_5062909 baseEnd_5062909 := by
    simpa [prefixWord, tailWord_5062909, baseEnd_5062909] using wordTrace_append hprefix tailTrace_5062909
  have hstable : (prefixWord ++ tailWord_5062909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5062909).length < 2 ^ (prefixWord ++ tailWord_5062909).sum := by decide
  have hdescent : baseEnd_5062909 < baseStart_5062909 := by decide
  rcases family_descends (prefixWord ++ tailWord_5062909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5062939 : List Nat := [1, 1, 1, 1, 1, 1, 6, 2, 1, 3, 5]
def baseStart_5062939 : Nat := 118140960795 + 5062939 * 2 ^ 59
def prefixEnd_5062939 : Nat := 4983230072969 + 3 ^ 40 * 5062939 * 2
def baseEnd_5062939 : Nat := 2599721231393871961578473

theorem tailTrace_5062939 : CollatzResearch.WordTrace tailWord_5062939 prefixEnd_5062939 2599721231393871961578473 := by
  unfold tailWord_5062939
  simp only [CollatzResearch.WordTrace]
  refine ⟨184660555804844158985527871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123107037203229439323685247 184660555804844158985527871)
  ·
    refine ⟨276990833707266238478291807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184660555804844158985527871 276990833707266238478291807)
    ·
      refine ⟨415486250560899357717437711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 276990833707266238478291807 415486250560899357717437711)
      ·
        refine ⟨623229375841349036576156567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 415486250560899357717437711 623229375841349036576156567)
        ·
          refine ⟨934844063762023554864234851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 623229375841349036576156567 934844063762023554864234851)
          ·
            refine ⟨1402266095643035332296352277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 934844063762023554864234851 1402266095643035332296352277)
            ·
              refine ⟨65731223233267281201391513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1402266095643035332296352277 65731223233267281201391513)
              ·
                refine ⟨49298417424950460901043635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65731223233267281201391513 49298417424950460901043635)
                ·
                  refine ⟨73947626137425691351565453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49298417424950460901043635 73947626137425691351565453)
                  ·
                    refine ⟨27730359801534634256837045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 73947626137425691351565453 27730359801534634256837045)
                    ·
                      refine ⟨2599721231393871961578473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27730359801534634256837045 2599721231393871961578473)
                      ·
                        rfl

theorem cell23_5062939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 2, 1, 3, 5].length) (baseStart_5062939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5062939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5062939 prefixEnd_5062939 := by exact prefixLift 5062939
  have htrace : WordTrace (prefixWord ++ tailWord_5062939) baseStart_5062939 baseEnd_5062939 := by
    simpa [prefixWord, tailWord_5062939, baseEnd_5062939] using wordTrace_append hprefix tailTrace_5062939
  have hstable : (prefixWord ++ tailWord_5062939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5062939).length < 2 ^ (prefixWord ++ tailWord_5062939).sum := by decide
  have hdescent : baseEnd_5062939 < baseStart_5062939 := by decide
  rcases family_descends (prefixWord ++ tailWord_5062939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5062946 : List Nat := [3, 3, 1, 1, 3, 1, 1, 1, 1, 8]
def baseStart_5062946 : Nat := 118140960795 + 5062946 * 2 ^ 59
def prefixEnd_5062946 : Nat := 4983230072969 + 3 ^ 40 * 5062946 * 2
def baseEnd_5062946 : Nat := 866574941919484478063647

theorem tailTrace_5062946 : CollatzResearch.WordTrace tailWord_5062946 prefixEnd_5062946 866574941919484478063647 := by
  unfold tailWord_5062946
  simp only [CollatzResearch.WordTrace]
  refine ⟨46165202778954699795258173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123107207410545866120688461 46165202778954699795258173)
  ·
    refine ⟨17311951042108012423221815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46165202778954699795258173 17311951042108012423221815)
    ·
      refine ⟨25967926563162018634832723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17311951042108012423221815 25967926563162018634832723)
      ·
        refine ⟨38951889844743027952249085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25967926563162018634832723 38951889844743027952249085)
        ·
          refine ⟨14606958691778635482093407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38951889844743027952249085 14606958691778635482093407)
          ·
            refine ⟨21910438037667953223140111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14606958691778635482093407 21910438037667953223140111)
            ·
              refine ⟨32865657056501929834710167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21910438037667953223140111 32865657056501929834710167)
              ·
                refine ⟨49298485584752894752065251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32865657056501929834710167 49298485584752894752065251)
                ·
                  refine ⟨73947728377129342128097877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49298485584752894752065251 73947728377129342128097877)
                  ·
                    refine ⟨866574941919484478063647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 73947728377129342128097877 866574941919484478063647)
                    ·
                      rfl

theorem cell23_5062946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 1, 1, 8].length) (baseStart_5062946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5062946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5062946 prefixEnd_5062946 := by exact prefixLift 5062946
  have htrace : WordTrace (prefixWord ++ tailWord_5062946) baseStart_5062946 baseEnd_5062946 := by
    simpa [prefixWord, tailWord_5062946, baseEnd_5062946] using wordTrace_append hprefix tailTrace_5062946
  have hstable : (prefixWord ++ tailWord_5062946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5062946).length < 2 ^ (prefixWord ++ tailWord_5062946).sum := by decide
  have hdescent : baseEnd_5062946 < baseStart_5062946 := by decide
  rcases family_descends (prefixWord ++ tailWord_5062946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5062959 : List Nat := [1, 1, 2, 1, 2, 1, 5, 1, 9]
def baseStart_5062959 : Nat := 118140960795 + 5062959 * 2 ^ 59
def prefixEnd_5062959 : Nat := 4983230072969 + 3 ^ 40 * 5062959 * 2
def baseEnd_5062959 : Nat := 288859055667440209258709

theorem tailTrace_5062959 : CollatzResearch.WordTrace tailWord_5062959 prefixEnd_5062959 288859055667440209258709 := by
  unfold tailWord_5062959
  simp only [CollatzResearch.WordTrace]
  refine ⟨184661285264771702401255931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123107523509847801600837287 184661285264771702401255931)
  ·
    refine ⟨276991927897157553601883897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184661285264771702401255931 276991927897157553601883897)
    ·
      refine ⟨207743945922868165201412923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 276991927897157553601883897 207743945922868165201412923)
      ·
        refine ⟨311615918884302247802119385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 207743945922868165201412923 311615918884302247802119385)
        ·
          refine ⟨233711939163226685851589539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 311615918884302247802119385 233711939163226685851589539)
          ·
            refine ⟨350567908744840028777384309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 233711939163226685851589539 350567908744840028777384309)
            ·
              refine ⟨32865741444828752697879779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 350567908744840028777384309 32865741444828752697879779)
              ·
                refine ⟨49298612167243129046819669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32865741444828752697879779 49298612167243129046819669)
                ·
                  refine ⟨288859055667440209258709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 49298612167243129046819669 288859055667440209258709)
                  ·
                    rfl

theorem cell23_5062959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 1, 9].length) (baseStart_5062959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5062959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5062959 prefixEnd_5062959 := by exact prefixLift 5062959
  have htrace : WordTrace (prefixWord ++ tailWord_5062959) baseStart_5062959 baseEnd_5062959 := by
    simpa [prefixWord, tailWord_5062959, baseEnd_5062959] using wordTrace_append hprefix tailTrace_5062959
  have hstable : (prefixWord ++ tailWord_5062959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5062959).length < 2 ^ (prefixWord ++ tailWord_5062959).sum := by decide
  have hdescent : baseEnd_5062959 < baseStart_5062959 := by decide
  rcases family_descends (prefixWord ++ tailWord_5062959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5062974 : List Nat := [4, 2, 1, 2, 1, 4, 2, 1, 1, 3, 2]
def baseStart_5062974 : Nat := 118140960795 + 5062974 * 2 ^ 59
def prefixEnd_5062974 : Nat := 4983230072969 + 3 ^ 40 * 5062974 * 2
def baseEnd_5062974 : Nat := 2599739203216779324640813

theorem tailTrace_5062974 : CollatzResearch.WordTrace tailWord_5062974 prefixEnd_5062974 2599739203216779324640813 := by
  unfold tailWord_5062974
  simp only [CollatzResearch.WordTrace]
  refine ⟨23082729044964669995381497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 123107888239811573308701317 23082729044964669995381497)
  ·
    refine ⟨17312046783723502496536123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23082729044964669995381497 17312046783723502496536123)
    ·
      refine ⟨25968070175585253744804185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17312046783723502496536123 25968070175585253744804185)
      ·
        refine ⟨19476052631688940308603139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25968070175585253744804185 19476052631688940308603139)
        ·
          refine ⟨29214078947533410462904709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19476052631688940308603139 29214078947533410462904709)
          ·
            refine ⟨5477639802662514461794633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29214078947533410462904709 5477639802662514461794633)
            ·
              refine ⟨4108229851996885846345975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5477639802662514461794633 4108229851996885846345975)
              ·
                refine ⟨6162344777995328769518963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4108229851996885846345975 6162344777995328769518963)
                ·
                  refine ⟨9243517166992993154278445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6162344777995328769518963 9243517166992993154278445)
                  ·
                    refine ⟨3466318937622372432854417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9243517166992993154278445 3466318937622372432854417)
                    ·
                      refine ⟨2599739203216779324640813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3466318937622372432854417 2599739203216779324640813)
                      ·
                        rfl

theorem cell23_5062974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 2, 1, 1, 3, 2].length) (baseStart_5062974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5062974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5062974 prefixEnd_5062974 := by exact prefixLift 5062974
  have htrace : WordTrace (prefixWord ++ tailWord_5062974) baseStart_5062974 baseEnd_5062974 := by
    simpa [prefixWord, tailWord_5062974, baseEnd_5062974] using wordTrace_append hprefix tailTrace_5062974
  have hstable : (prefixWord ++ tailWord_5062974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5062974).length < 2 ^ (prefixWord ++ tailWord_5062974).sum := by decide
  have hdescent : baseEnd_5062974 < baseStart_5062974 := by decide
  rcases family_descends (prefixWord ++ tailWord_5062974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5062993 : List Nat := [1, 2, 2, 1, 4, 2, 2, 4, 5]
def baseStart_5062993 : Nat := 118140960795 + 5062993 * 2 ^ 59
def prefixEnd_5062993 : Nat := 4983230072969 + 3 ^ 40 * 5062993 * 2
def baseEnd_5062993 : Nat := 288860995483246083367025

theorem tailTrace_5062993 : CollatzResearch.WordTrace tailWord_5062993 prefixEnd_5062993 288860995483246083367025 := by
  unfold tailWord_5062993
  simp only [CollatzResearch.WordTrace]
  refine ⟨184662525346648526207993633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123108350231099017471995755 184662525346648526207993633)
  ·
    refine ⟨138496894009986394655995225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184662525346648526207993633 138496894009986394655995225)
    ·
      refine ⟨103872670507489795991996419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138496894009986394655995225 103872670507489795991996419)
      ·
        refine ⟨155809005761234693987994629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103872670507489795991996419 155809005761234693987994629)
        ·
          refine ⟨29214188580231505122748993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 155809005761234693987994629 29214188580231505122748993)
          ·
            refine ⟨21910641435173628842061745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29214188580231505122748993 21910641435173628842061745)
            ·
              refine ⟨16432981076380221631546309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21910641435173628842061745 16432981076380221631546309)
              ·
                refine ⟨3081183951821291555914933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16432981076380221631546309 3081183951821291555914933)
                ·
                  refine ⟨288860995483246083367025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3081183951821291555914933 288860995483246083367025)
                  ·
                    rfl

theorem cell23_5062993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 4, 5].length) (baseStart_5062993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5062993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5062993 prefixEnd_5062993 := by exact prefixLift 5062993
  have htrace : WordTrace (prefixWord ++ tailWord_5062993) baseStart_5062993 baseEnd_5062993 := by
    simpa [prefixWord, tailWord_5062993, baseEnd_5062993] using wordTrace_append hprefix tailTrace_5062993
  have hstable : (prefixWord ++ tailWord_5062993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5062993).length < 2 ^ (prefixWord ++ tailWord_5062993).sum := by decide
  have hdescent : baseEnd_5062993 < baseStart_5062993 := by decide
  rcases family_descends (prefixWord ++ tailWord_5062993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5063004 : List Nat := [2, 2, 4, 3, 1, 2, 1, 1, 1, 4, 2]
def baseStart_5063004 : Nat := 118140960795 + 5063004 * 2 ^ 59
def prefixEnd_5063004 : Nat := 4983230072969 + 3 ^ 40 * 5063004 * 2
def baseEnd_5063004 : Nat := 2599754607636414207265675

theorem tailTrace_5063004 : CollatzResearch.WordTrace tailWord_5063004 prefixEnd_5063004 2599754607636414207265675 := by
  unfold tailWord_5063004
  simp only [CollatzResearch.WordTrace]
  refine ⟨92331463274804337543322033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123108617699739116724429377 92331463274804337543322033)
  ·
    refine ⟨69248597456103253157491525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92331463274804337543322033 69248597456103253157491525)
    ·
      refine ⟨12984112023019359967029661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 69248597456103253157491525 12984112023019359967029661)
      ·
        refine ⟨4869042008632259987636123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12984112023019359967029661 4869042008632259987636123)
        ·
          refine ⟨7303563012948389981454185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4869042008632259987636123 7303563012948389981454185)
          ·
            refine ⟨5477672259711292486090639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7303563012948389981454185 5477672259711292486090639)
            ·
              refine ⟨8216508389566938729135959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5477672259711292486090639 8216508389566938729135959)
              ·
                refine ⟨12324762584350408093703939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8216508389566938729135959 12324762584350408093703939)
                ·
                  refine ⟨18487143876525612140555909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12324762584350408093703939 18487143876525612140555909)
                  ·
                    refine ⟨3466339476848552276354233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18487143876525612140555909 3466339476848552276354233)
                    ·
                      refine ⟨2599754607636414207265675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3466339476848552276354233 2599754607636414207265675)
                      ·
                        rfl

theorem cell23_5063004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 1, 1, 1, 4, 2].length) (baseStart_5063004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5063004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5063004 prefixEnd_5063004 := by exact prefixLift 5063004
  have htrace : WordTrace (prefixWord ++ tailWord_5063004) baseStart_5063004 baseEnd_5063004 := by
    simpa [prefixWord, tailWord_5063004, baseEnd_5063004] using wordTrace_append hprefix tailTrace_5063004
  have hstable : (prefixWord ++ tailWord_5063004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5063004).length < 2 ^ (prefixWord ++ tailWord_5063004).sum := by decide
  have hdescent : baseEnd_5063004 < baseStart_5063004 := by decide
  rcases family_descends (prefixWord ++ tailWord_5063004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5063050 : List Nat := [3, 1, 2, 5, 1, 1, 1, 1, 1, 2, 5]
def baseStart_5063050 : Nat := 118140960795 + 5063050 * 2 ^ 59
def prefixEnd_5063050 : Nat := 4983230072969 + 3 ^ 40 * 5063050 * 2
def baseEnd_5063050 : Nat := 2599778227746521027290463

theorem tailTrace_5063050 : CollatzResearch.WordTrace tailWord_5063050 prefixEnd_5063050 2599778227746521027290463 := by
  unfold tailWord_5063050
  simp only [CollatzResearch.WordTrace]
  refine ⟨46166151076860506235704651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123109736204961349961879069 46166151076860506235704651)
  ·
    refine ⟨69249226615290759353556977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46166151076860506235704651 69249226615290759353556977)
    ·
      refine ⟨51936919961468069515167733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69249226615290759353556977 51936919961468069515167733)
      ·
        refine ⟨4869086246387631517046975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 51936919961468069515167733 4869086246387631517046975)
        ·
          refine ⟨7303629369581447275570463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4869086246387631517046975 7303629369581447275570463)
          ·
            refine ⟨10955444054372170913355695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7303629369581447275570463 10955444054372170913355695)
            ·
              refine ⟨16433166081558256370033543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10955444054372170913355695 16433166081558256370033543)
              ·
                refine ⟨24649749122337384555050315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16433166081558256370033543 24649749122337384555050315)
                ·
                  refine ⟨36974623683506076832575473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24649749122337384555050315 36974623683506076832575473)
                  ·
                    refine ⟨27730967762629557624431605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36974623683506076832575473 27730967762629557624431605)
                    ·
                      refine ⟨2599778227746521027290463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27730967762629557624431605 2599778227746521027290463)
                      ·
                        rfl

theorem cell23_5063050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_5063050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5063050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5063050 prefixEnd_5063050 := by exact prefixLift 5063050
  have htrace : WordTrace (prefixWord ++ tailWord_5063050) baseStart_5063050 baseEnd_5063050 := by
    simpa [prefixWord, tailWord_5063050, baseEnd_5063050] using wordTrace_append hprefix tailTrace_5063050
  have hstable : (prefixWord ++ tailWord_5063050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5063050).length < 2 ^ (prefixWord ++ tailWord_5063050).sum := by decide
  have hdescent : baseEnd_5063050 < baseStart_5063050 := by decide
  rcases family_descends (prefixWord ++ tailWord_5063050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5063100 : List Nat := [2, 2, 2, 4, 1, 2, 2, 2, 6]
def baseStart_5063100 : Nat := 118140960795 + 5063100 * 2 ^ 59
def prefixEnd_5063100 : Nat := 4983230072969 + 3 ^ 40 * 5063100 * 2
def baseEnd_5063100 : Nat := 288867100197693981296137

theorem tailTrace_5063100 : CollatzResearch.WordTrace tailWord_5063100 prefixEnd_5063100 288867100197693981296137 := by
  unfold tailWord_5063100
  simp only [CollatzResearch.WordTrace]
  refine ⟨92333213978630441741069377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123110951971507255654759169 92333213978630441741069377)
  ·
    refine ⟨69249910483972831305802033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92333213978630441741069377 69249910483972831305802033)
    ·
      refine ⟨51937432862979623479351525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69249910483972831305802033 51937432862979623479351525)
      ·
        refine ⟨9738268661808679402378411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51937432862979623479351525 9738268661808679402378411)
        ·
          refine ⟨14607402992713019103567617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9738268661808679402378411 14607402992713019103567617)
          ·
            refine ⟨10955552244534764327675713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14607402992713019103567617 10955552244534764327675713)
            ·
              refine ⟨8216664183401073245756785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10955552244534764327675713 8216664183401073245756785)
              ·
                refine ⟨6162498137550804934317589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8216664183401073245756785 6162498137550804934317589)
                ·
                  refine ⟨288867100197693981296137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6162498137550804934317589 288867100197693981296137)
                  ·
                    rfl

theorem cell23_5063100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 2, 2, 6].length) (baseStart_5063100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5063100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5063100 prefixEnd_5063100 := by exact prefixLift 5063100
  have htrace : WordTrace (prefixWord ++ tailWord_5063100) baseStart_5063100 baseEnd_5063100 := by
    simpa [prefixWord, tailWord_5063100, baseEnd_5063100] using wordTrace_append hprefix tailTrace_5063100
  have hstable : (prefixWord ++ tailWord_5063100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5063100).length < 2 ^ (prefixWord ++ tailWord_5063100).sum := by decide
  have hdescent : baseEnd_5063100 < baseStart_5063100 := by decide
  rcases family_descends (prefixWord ++ tailWord_5063100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5063103 : List Nat := [1, 1, 2, 2, 2, 1, 1, 1, 5, 5, 2]
def baseStart_5063103 : Nat := 118140960795 + 5063103 * 2 ^ 59
def prefixEnd_5063103 : Nat := 4983230072969 + 3 ^ 40 * 5063103 * 2
def baseEnd_5063103 : Nat := 2599805442221209319927719

theorem tailTrace_5063103 : CollatzResearch.WordTrace tailWord_5063103 prefixEnd_5063103 2599805442221209319927719 := by
  unfold tailWord_5063103
  simp only [CollatzResearch.WordTrace]
  refine ⟨184666537376250014994497963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123111024917500009996331975 184666537376250014994497963)
  ·
    refine ⟨276999806064375022491746945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184666537376250014994497963 276999806064375022491746945)
    ·
      refine ⟨207749854548281266868810209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 276999806064375022491746945 207749854548281266868810209)
      ·
        refine ⟨155812390911210950151607657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 207749854548281266868810209 155812390911210950151607657)
        ·
          refine ⟨116859293183408212613705743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 155812390911210950151607657 116859293183408212613705743)
          ·
            refine ⟨175288939775112318920558615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116859293183408212613705743 175288939775112318920558615)
            ·
              refine ⟨262933409662668478380837923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 175288939775112318920558615 262933409662668478380837923)
              ·
                refine ⟨394400114494002717571256885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 262933409662668478380837923 394400114494002717571256885)
                ·
                  refine ⟨36975010733812754772305333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 394400114494002717571256885 36975010733812754772305333)
                  ·
                    refine ⟨3466407256294945759903625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 36975010733812754772305333 3466407256294945759903625)
                    ·
                      refine ⟨2599805442221209319927719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3466407256294945759903625 2599805442221209319927719)
                      ·
                        rfl

theorem cell23_5063103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 5, 5, 2].length) (baseStart_5063103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5063103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5063103 prefixEnd_5063103 := by exact prefixLift 5063103
  have htrace : WordTrace (prefixWord ++ tailWord_5063103) baseStart_5063103 baseEnd_5063103 := by
    simpa [prefixWord, tailWord_5063103, baseEnd_5063103] using wordTrace_append hprefix tailTrace_5063103
  have hstable : (prefixWord ++ tailWord_5063103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5063103).length < 2 ^ (prefixWord ++ tailWord_5063103).sum := by decide
  have hdescent : baseEnd_5063103 < baseStart_5063103 := by decide
  rcases family_descends (prefixWord ++ tailWord_5063103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5063143 : List Nat := [1, 1, 5, 2, 1, 1, 1, 4, 1, 6]
def baseStart_5063143 : Nat := 118140960795 + 5063143 * 2 ^ 59
def prefixEnd_5063143 : Nat := 4983230072969 + 3 ^ 40 * 5063143 * 2
def baseEnd_5063143 : Nat := 866608660482463054475845

theorem tailTrace_5063143 : CollatzResearch.WordTrace tailWord_5063143 prefixEnd_5063143 866608660482463054475845 := by
  unfold tailWord_5063143
  simp only [CollatzResearch.WordTrace]
  refine ⟨184667996296105101825954083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123111997530736734550636055 184667996296105101825954083)
  ·
    refine ⟨277001994444157652738931125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184667996296105101825954083 277001994444157652738931125)
    ·
      refine ⟨25968936979139779944274793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 277001994444157652738931125 25968936979139779944274793)
      ·
        refine ⟨19476702734354834958206095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25968936979139779944274793 19476702734354834958206095)
        ·
          refine ⟨29215054101532252437309143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19476702734354834958206095 29215054101532252437309143)
          ·
            refine ⟨43822581152298378655963715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29215054101532252437309143 43822581152298378655963715)
            ·
              refine ⟨65733871728447567983945573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43822581152298378655963715 65733871728447567983945573)
              ·
                refine ⟨12325100949083918996989795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 65733871728447567983945573 12325100949083918996989795)
                ·
                  refine ⟨18487651423625878495484693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12325100949083918996989795 18487651423625878495484693)
                  ·
                    refine ⟨866608660482463054475845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18487651423625878495484693 866608660482463054475845)
                    ·
                      rfl

theorem cell23_5063143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 4, 1, 6].length) (baseStart_5063143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5063143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5063143 prefixEnd_5063143 := by exact prefixLift 5063143
  have htrace : WordTrace (prefixWord ++ tailWord_5063143) baseStart_5063143 baseEnd_5063143 := by
    simpa [prefixWord, tailWord_5063143, baseEnd_5063143] using wordTrace_append hprefix tailTrace_5063143
  have hstable : (prefixWord ++ tailWord_5063143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5063143).length < 2 ^ (prefixWord ++ tailWord_5063143).sum := by decide
  have hdescent : baseEnd_5063143 < baseStart_5063143 := by decide
  rcases family_descends (prefixWord ++ tailWord_5063143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5063144 : List Nat := [2, 1, 4, 1, 1, 4, 2, 3, 1, 1, 3]
def baseStart_5063144 : Nat := 118140960795 + 5063144 * 2 ^ 59
def prefixEnd_5063144 : Nat := 4983230072969 + 3 ^ 40 * 5063144 * 2
def baseEnd_5063144 : Nat := 2599826494928043659515031

theorem tailTrace_5063144 : CollatzResearch.WordTrace tailWord_5063144 prefixEnd_5063144 2599826494928043659515031 := by
  unfold tailWord_5063144
  simp only [CollatzResearch.WordTrace]
  refine ⟨92334016384550739498370243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123112021846067652664493657 92334016384550739498370243)
  ·
    refine ⟨138501024576826109247555365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92334016384550739498370243 138501024576826109247555365)
    ·
      refine ⟨25968942108154895483916631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 138501024576826109247555365 25968942108154895483916631)
      ·
        refine ⟨38953413162232343225874947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25968942108154895483916631 38953413162232343225874947)
        ·
          refine ⟨58430119743348514838812421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38953413162232343225874947 58430119743348514838812421)
          ·
            refine ⟨10955647451877846532277329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58430119743348514838812421 10955647451877846532277329)
            ·
              refine ⟨8216735588908384899207997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10955647451877846532277329 8216735588908384899207997)
              ·
                refine ⟨3081275845840644337202999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8216735588908384899207997 3081275845840644337202999)
                ·
                  refine ⟨4621913768760966505804499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3081275845840644337202999 4621913768760966505804499)
                  ·
                    refine ⟨6932870653141449758706749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4621913768760966505804499 6932870653141449758706749)
                    ·
                      refine ⟨2599826494928043659515031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6932870653141449758706749 2599826494928043659515031)
                      ·
                        rfl

theorem cell23_5063144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 2, 3, 1, 1, 3].length) (baseStart_5063144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5063144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5063144 prefixEnd_5063144 := by exact prefixLift 5063144
  have htrace : WordTrace (prefixWord ++ tailWord_5063144) baseStart_5063144 baseEnd_5063144 := by
    simpa [prefixWord, tailWord_5063144, baseEnd_5063144] using wordTrace_append hprefix tailTrace_5063144
  have hstable : (prefixWord ++ tailWord_5063144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5063144).length < 2 ^ (prefixWord ++ tailWord_5063144).sum := by decide
  have hdescent : baseEnd_5063144 < baseStart_5063144 := by decide
  rcases family_descends (prefixWord ++ tailWord_5063144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5063153 : List Nat := [1, 2, 2, 2, 3, 1, 2, 3, 1, 1, 5]
def baseStart_5063153 : Nat := 118140960795 + 5063153 * 2 ^ 59
def prefixEnd_5063153 : Nat := 4983230072969 + 3 ^ 40 * 5063153 * 2
def baseEnd_5063153 : Nat := 2599831116253934124302489

theorem tailTrace_5063153 : CollatzResearch.WordTrace tailWord_5063153 prefixEnd_5063153 2599831116253934124302489 := by
  unfold tailWord_5063153
  simp only [CollatzResearch.WordTrace]
  refine ⟨184668361026068873533818113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123112240684045915689212075 184668361026068873533818113)
  ·
    refine ⟨138501270769551655150363585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184668361026068873533818113 138501270769551655150363585)
    ·
      refine ⟨103875953077163741362772689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138501270769551655150363585 103875953077163741362772689)
      ·
        refine ⟨77906964807872806022079517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103875953077163741362772689 77906964807872806022079517)
        ·
          refine ⟨29215111802952302258279819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77906964807872806022079517 29215111802952302258279819)
          ·
            refine ⟨43822667704428453387419729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29215111802952302258279819 43822667704428453387419729)
            ·
              refine ⟨32867000778321340040564797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43822667704428453387419729 32867000778321340040564797)
              ·
                refine ⟨12325125291870502515211799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32867000778321340040564797 12325125291870502515211799)
                ·
                  refine ⟨18487687937805753772817699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12325125291870502515211799 18487687937805753772817699)
                  ·
                    refine ⟨27731531906708630659226549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18487687937805753772817699 27731531906708630659226549)
                    ·
                      refine ⟨2599831116253934124302489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27731531906708630659226549 2599831116253934124302489)
                      ·
                        rfl

theorem cell23_5063153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 3, 1, 1, 5].length) (baseStart_5063153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5063153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5063153 prefixEnd_5063153 := by exact prefixLift 5063153
  have htrace : WordTrace (prefixWord ++ tailWord_5063153) baseStart_5063153 baseEnd_5063153 := by
    simpa [prefixWord, tailWord_5063153, baseEnd_5063153] using wordTrace_append hprefix tailTrace_5063153
  have hstable : (prefixWord ++ tailWord_5063153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5063153).length < 2 ^ (prefixWord ++ tailWord_5063153).sum := by decide
  have hdescent : baseEnd_5063153 < baseStart_5063153 := by decide
  rcases family_descends (prefixWord ++ tailWord_5063153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5063167 : List Nat := [1, 1, 2, 2, 1, 2, 6, 1, 3, 2, 2]
def baseStart_5063167 : Nat := 118140960795 + 5063167 * 2 ^ 59
def prefixEnd_5063167 : Nat := 4983230072969 + 3 ^ 40 * 5063167 * 2
def baseEnd_5063167 : Nat := 2599838304983097069527425

theorem tailTrace_5063167 : CollatzResearch.WordTrace tailWord_5063167 prefixEnd_5063167 2599838304983097069527425 := by
  unfold tailWord_5063167
  simp only [CollatzResearch.WordTrace]
  refine ⟨184668871648018153924827755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123112581098678769283218503 184668871648018153924827755)
  ·
    refine ⟨277003307472027230887241633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184668871648018153924827755 277003307472027230887241633)
    ·
      refine ⟨207752480604020423165431225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 277003307472027230887241633 207752480604020423165431225)
      ·
        refine ⟨155814360453015317374073419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 207752480604020423165431225 155814360453015317374073419)
        ·
          refine ⟨233721540679522976061110129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155814360453015317374073419 233721540679522976061110129)
          ·
            refine ⟨175291155509642232045832597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 233721540679522976061110129 175291155509642232045832597)
            ·
              refine ⟨8216772914514479627148403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 175291155509642232045832597 8216772914514479627148403)
              ·
                refine ⟨12325159371771719440722605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8216772914514479627148403 12325159371771719440722605)
                ·
                  refine ⟨4621934764414394790270977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12325159371771719440722605 4621934764414394790270977)
                  ·
                    refine ⟨3466451073310796092703233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4621934764414394790270977 3466451073310796092703233)
                    ·
                      refine ⟨2599838304983097069527425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3466451073310796092703233 2599838304983097069527425)
                      ·
                        rfl

theorem cell23_5063167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 6, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 6, 1, 3, 2, 2].length) (baseStart_5063167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5063167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5063167 prefixEnd_5063167 := by exact prefixLift 5063167
  have htrace : WordTrace (prefixWord ++ tailWord_5063167) baseStart_5063167 baseEnd_5063167 := by
    simpa [prefixWord, tailWord_5063167, baseEnd_5063167] using wordTrace_append hprefix tailTrace_5063167
  have hstable : (prefixWord ++ tailWord_5063167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5063167).length < 2 ^ (prefixWord ++ tailWord_5063167).sum := by decide
  have hdescent : baseEnd_5063167 < baseStart_5063167 := by decide
  rcases family_descends (prefixWord ++ tailWord_5063167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5063180 : List Nat := [2, 2, 1, 2, 4, 1, 3, 1, 1, 2, 4]
def baseStart_5063180 : Nat := 118140960795 + 5063180 * 2 ^ 59
def prefixEnd_5063180 : Nat := 4983230072969 + 3 ^ 40 * 5063180 * 2
def baseEnd_5063180 : Nat := 2599844980231605518664865

theorem tailTrace_5063180 : CollatzResearch.WordTrace tailWord_5063180 prefixEnd_5063180 2599844980231605518664865 := by
  unfold tailWord_5063180
  simp only [CollatzResearch.WordTrace]
  refine ⟨92334672898485528572525497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123112897197980704763367329 92334672898485528572525497)
  ·
    refine ⟨69251004673864146429394123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92334672898485528572525497 69251004673864146429394123)
    ·
      refine ⟨103876507010796219644091185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69251004673864146429394123 103876507010796219644091185)
      ·
        refine ⟨77907380258097164733068389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103876507010796219644091185 77907380258097164733068389)
        ·
          refine ⟨14607633798393218387450323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 77907380258097164733068389 14607633798393218387450323)
          ·
            refine ⟨21911450697589827581175485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14607633798393218387450323 21911450697589827581175485)
            ·
              refine ⟨8216794011596185342940807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21911450697589827581175485 8216794011596185342940807)
              ·
                refine ⟨12325191017394278014411211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8216794011596185342940807 12325191017394278014411211)
                ·
                  refine ⟨18487786526091417021616817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12325191017394278014411211 18487786526091417021616817)
                  ·
                    refine ⟨13865839894568562766212613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18487786526091417021616817 13865839894568562766212613)
                    ·
                      refine ⟨2599844980231605518664865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13865839894568562766212613 2599844980231605518664865)
                      ·
                        rfl

theorem cell23_5063180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 3, 1, 1, 2, 4].length) (baseStart_5063180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5063180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5063180 prefixEnd_5063180 := by exact prefixLift 5063180
  have htrace : WordTrace (prefixWord ++ tailWord_5063180) baseStart_5063180 baseEnd_5063180 := by
    simpa [prefixWord, tailWord_5063180, baseEnd_5063180] using wordTrace_append hprefix tailTrace_5063180
  have hstable : (prefixWord ++ tailWord_5063180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5063180).length < 2 ^ (prefixWord ++ tailWord_5063180).sum := by decide
  have hdescent : baseEnd_5063180 < baseStart_5063180 := by decide
  rcases family_descends (prefixWord ++ tailWord_5063180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5063207 : List Nat := [1, 1, 7, 2, 1, 2, 9]
def baseStart_5063207 : Nat := 118140960795 + 5063207 * 2 ^ 59
def prefixEnd_5063207 : Nat := 4983230072969 + 3 ^ 40 * 5063207 * 2
def baseEnd_5063207 : Nat := 32097022768015764358361

theorem tailTrace_5063207 : CollatzResearch.WordTrace tailWord_5063207 prefixEnd_5063207 32097022768015764358361 := by
  unfold tailWord_5063207
  simp only [CollatzResearch.WordTrace]
  refine ⟨184670330567873240756283875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123113553711915493837522583 184670330567873240756283875)
  ·
    refine ⟨277005495851809861134425813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184670330567873240756283875 277005495851809861134425813)
    ·
      refine ⟨6492316309026793620338105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 277005495851809861134425813 6492316309026793620338105)
      ·
        refine ⟨4869237231770095215253579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6492316309026793620338105 4869237231770095215253579)
        ·
          refine ⟨7303855847655142822880369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4869237231770095215253579 7303855847655142822880369)
          ·
            refine ⟨5477891885741357117160277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7303855847655142822880369 5477891885741357117160277)
            ·
              refine ⟨32097022768015764358361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5477891885741357117160277 32097022768015764358361)
              ·
                rfl

theorem cell23_5063207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 9].length) (baseStart_5063207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5063207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5063207 prefixEnd_5063207 := by exact prefixLift 5063207
  have htrace : WordTrace (prefixWord ++ tailWord_5063207) baseStart_5063207 baseEnd_5063207 := by
    simpa [prefixWord, tailWord_5063207, baseEnd_5063207] using wordTrace_append hprefix tailTrace_5063207
  have hstable : (prefixWord ++ tailWord_5063207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5063207).length < 2 ^ (prefixWord ++ tailWord_5063207).sum := by decide
  have hdescent : baseEnd_5063207 < baseStart_5063207 := by decide
  rcases family_descends (prefixWord ++ tailWord_5063207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5063223 : List Nat := [1, 1, 3, 1, 2, 3, 2, 1, 2, 3, 4]
def baseStart_5063223 : Nat := 118140960795 + 5063223 * 2 ^ 59
def prefixEnd_5063223 : Nat := 4983230072969 + 3 ^ 40 * 5063223 * 2
def baseEnd_5063223 : Nat := 2599867059899748850427167

theorem tailTrace_5063223 : CollatzResearch.WordTrace tailWord_5063223 prefixEnd_5063223 2599867059899748850427167 := by
  unfold tailWord_5063223
  simp only [CollatzResearch.WordTrace]
  refine ⟨184670914135815275488866323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123113942757210183659244215 184670914135815275488866323)
  ·
    refine ⟨277006371203722913233299485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184670914135815275488866323 277006371203722913233299485)
    ·
      refine ⟨103877389201396092462487307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 277006371203722913233299485 103877389201396092462487307)
      ·
        refine ⟨155816083802094138693730961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103877389201396092462487307 155816083802094138693730961)
        ·
          refine ⟨116862062851570604020298221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 155816083802094138693730961 116862062851570604020298221)
          ·
            refine ⟨43823273569338976507611833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 116862062851570604020298221 43823273569338976507611833)
            ·
              refine ⟨32867455177004232380708875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43823273569338976507611833 32867455177004232380708875)
              ·
                refine ⟨49301182765506348571063313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32867455177004232380708875 49301182765506348571063313)
                ·
                  refine ⟨36975887074129761428297485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49301182765506348571063313 36975887074129761428297485)
                  ·
                    refine ⟨13865957652798660535611557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36975887074129761428297485 13865957652798660535611557)
                    ·
                      refine ⟨2599867059899748850427167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13865957652798660535611557 2599867059899748850427167)
                      ·
                        rfl

theorem cell23_5063223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 1, 2, 3, 4].length) (baseStart_5063223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5063223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5063223 prefixEnd_5063223 := by exact prefixLift 5063223
  have htrace : WordTrace (prefixWord ++ tailWord_5063223) baseStart_5063223 baseEnd_5063223 := by
    simpa [prefixWord, tailWord_5063223, baseEnd_5063223] using wordTrace_append hprefix tailTrace_5063223
  have hstable : (prefixWord ++ tailWord_5063223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5063223).length < 2 ^ (prefixWord ++ tailWord_5063223).sum := by decide
  have hdescent : baseEnd_5063223 < baseStart_5063223 := by decide
  rcases family_descends (prefixWord ++ tailWord_5063223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5063240 : List Nat := [2, 1, 3, 1, 1, 1, 1, 2, 5, 4, 2]
def baseStart_5063240 : Nat := 118140960795 + 5063240 * 2 ^ 59
def prefixEnd_5063240 : Nat := 4983230072969 + 3 ^ 40 * 5063240 * 2
def baseEnd_5063240 : Nat := 2599875789070875283914589

theorem tailTrace_5063240 : CollatzResearch.WordTrace tailWord_5063240 prefixEnd_5063240 2599875789070875283914589 := by
  unfold tailWord_5063240
  simp only [CollatzResearch.WordTrace]
  refine ⟨92335767088376843696117587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123114356117835791594823449 92335767088376843696117587)
  ·
    refine ⟨138503650632565265544176381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92335767088376843696117587 138503650632565265544176381)
    ·
      refine ⟨51938868987211974579066143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 138503650632565265544176381 51938868987211974579066143)
      ·
        refine ⟨77908303480817961868599215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51938868987211974579066143 77908303480817961868599215)
        ·
          refine ⟨116862455221226942802898823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77908303480817961868599215 116862455221226942802898823)
          ·
            refine ⟨175293682831840414204348235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116862455221226942802898823 175293682831840414204348235)
            ·
              refine ⟨262940524247760621306522353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 175293682831840414204348235 262940524247760621306522353)
              ·
                refine ⟨197205393185820465979891765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 262940524247760621306522353 197205393185820465979891765)
                ·
                  refine ⟨18488005611170668685614853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 197205393185820465979891765 18488005611170668685614853)
                  ·
                    refine ⟨3466501052094500378552785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18488005611170668685614853 3466501052094500378552785)
                    ·
                      refine ⟨2599875789070875283914589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3466501052094500378552785 2599875789070875283914589)
                      ·
                        rfl

theorem cell23_5063240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 2, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 2, 5, 4, 2].length) (baseStart_5063240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5063240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5063240 prefixEnd_5063240 := by exact prefixLift 5063240
  have htrace : WordTrace (prefixWord ++ tailWord_5063240) baseStart_5063240 baseEnd_5063240 := by
    simpa [prefixWord, tailWord_5063240, baseEnd_5063240] using wordTrace_append hprefix tailTrace_5063240
  have hstable : (prefixWord ++ tailWord_5063240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5063240).length < 2 ^ (prefixWord ++ tailWord_5063240).sum := by decide
  have hdescent : baseEnd_5063240 < baseStart_5063240 := by decide
  rcases family_descends (prefixWord ++ tailWord_5063240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5063243 : List Nat := [1, 1, 1, 1, 3, 1, 5, 2, 2, 1, 5]
def baseStart_5063243 : Nat := 118140960795 + 5063243 * 2 ^ 59
def prefixEnd_5063243 : Nat := 4983230072969 + 3 ^ 40 * 5063243 * 2
def baseEnd_5063243 : Nat := 2599877329512838772177075

theorem tailTrace_5063243 : CollatzResearch.WordTrace tailWord_5063243 prefixEnd_5063243 2599877329512838772177075 := by
  unfold tailWord_5063243
  simp only [CollatzResearch.WordTrace]
  refine ⟨184671643595742818904594383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123114429063828545936396255 184671643595742818904594383)
  ·
    refine ⟨277007465393614228356891575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184671643595742818904594383 277007465393614228356891575)
    ·
      refine ⟨415511198090421342535337363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 277007465393614228356891575 415511198090421342535337363)
      ·
        refine ⟨623266797135632013803006045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 415511198090421342535337363 623266797135632013803006045)
        ·
          refine ⟨233725048925862005176127267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 623266797135632013803006045 233725048925862005176127267)
          ·
            refine ⟨350587573388793007764190901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 233725048925862005176127267 350587573388793007764190901)
            ·
              refine ⟨32867585005199344477892897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 350587573388793007764190901 32867585005199344477892897)
              ·
                refine ⟨24650688753899508358419673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32867585005199344477892897 24650688753899508358419673)
                ·
                  refine ⟨18488016565424631268814755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24650688753899508358419673 18488016565424631268814755)
                  ·
                    refine ⟨27732024848136946903222133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18488016565424631268814755 27732024848136946903222133)
                    ·
                      refine ⟨2599877329512838772177075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27732024848136946903222133 2599877329512838772177075)
                      ·
                        rfl

theorem cell23_5063243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 2, 2, 1, 5].length) (baseStart_5063243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5063243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5063243 prefixEnd_5063243 := by exact prefixLift 5063243
  have htrace : WordTrace (prefixWord ++ tailWord_5063243) baseStart_5063243 baseEnd_5063243 := by
    simpa [prefixWord, tailWord_5063243, baseEnd_5063243] using wordTrace_append hprefix tailTrace_5063243
  have hstable : (prefixWord ++ tailWord_5063243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5063243).length < 2 ^ (prefixWord ++ tailWord_5063243).sum := by decide
  have hdescent : baseEnd_5063243 < baseStart_5063243 := by decide
  rcases family_descends (prefixWord ++ tailWord_5063243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5063310 : List Nat := [4, 1, 1, 3, 1, 1, 3, 1, 1, 7]
def baseStart_5063310 : Nat := 118140960795 + 5063310 * 2 ^ 59
def prefixEnd_5063310 : Nat := 4983230072969 + 3 ^ 40 * 5063310 * 2
def baseEnd_5063310 : Nat := 866637244238896670013089

theorem tailTrace_5063310 : CollatzResearch.WordTrace tailWord_5063310 prefixEnd_5063310 866637244238896670013089 := by
  unfold tailWord_5063310
  simp only [CollatzResearch.WordTrace]
  refine ⟨23084260910812511168410423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 123116058191000059564855589 23084260910812511168410423)
  ·
    refine ⟨34626391366218766752615635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23084260910812511168410423 34626391366218766752615635)
    ·
      refine ⟨51939587049328150128923453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34626391366218766752615635 51939587049328150128923453)
      ·
        refine ⟨19477345143498056298346295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51939587049328150128923453 19477345143498056298346295)
        ·
          refine ⟨29216017715247084447519443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19477345143498056298346295 29216017715247084447519443)
          ·
            refine ⟨43824026572870626671279165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29216017715247084447519443 43824026572870626671279165)
            ·
              refine ⟨16434009964826485001729687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43824026572870626671279165 16434009964826485001729687)
              ·
                refine ⟨24651014947239727502594531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16434009964826485001729687 24651014947239727502594531)
                ·
                  refine ⟨36976522420859591253891797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24651014947239727502594531 36976522420859591253891797)
                  ·
                    refine ⟨866637244238896670013089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36976522420859591253891797 866637244238896670013089)
                    ·
                      rfl

theorem cell23_5063310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 1, 1, 7].length) (baseStart_5063310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5063310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5063310 prefixEnd_5063310 := by exact prefixLift 5063310
  have htrace : WordTrace (prefixWord ++ tailWord_5063310) baseStart_5063310 baseEnd_5063310 := by
    simpa [prefixWord, tailWord_5063310, baseEnd_5063310] using wordTrace_append hprefix tailTrace_5063310
  have hstable : (prefixWord ++ tailWord_5063310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5063310).length < 2 ^ (prefixWord ++ tailWord_5063310).sum := by decide
  have hdescent : baseEnd_5063310 < baseStart_5063310 := by decide
  rcases family_descends (prefixWord ++ tailWord_5063310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5063314 : List Nat := [3, 2, 3, 1, 2, 2, 2, 3, 5]
def baseStart_5063314 : Nat := 118140960795 + 5063314 * 2 ^ 59
def prefixEnd_5063314 : Nat := 4983230072969 + 3 ^ 40 * 5063314 * 2
def baseEnd_5063314 : Nat := 288879309626589777154361

theorem tailTrace_5063314 : CollatzResearch.WordTrace tailWord_5063314 prefixEnd_5063314 288879309626589777154361 := by
  unfold tailWord_5063314
  simp only [CollatzResearch.WordTrace]
  refine ⟨46168558294621399507607249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123116155452323732020285997 46168558294621399507607249)
  ·
    refine ⟨34626418720966049630705437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46168558294621399507607249 34626418720966049630705437)
    ·
      refine ⟨12984907020362268611514539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34626418720966049630705437 12984907020362268611514539)
      ·
        refine ⟨19477360530543402917271809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12984907020362268611514539 19477360530543402917271809)
        ·
          refine ⟨14608020397907552187953857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19477360530543402917271809 14608020397907552187953857)
          ·
            refine ⟨10956015298430664140965393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14608020397907552187953857 10956015298430664140965393)
            ·
              refine ⟨8217011473822998105724045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10956015298430664140965393 8217011473822998105724045)
              ·
                refine ⟨3081379302683624289646517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8217011473822998105724045 3081379302683624289646517)
                ·
                  refine ⟨288879309626589777154361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3081379302683624289646517 288879309626589777154361)
                  ·
                    rfl

theorem cell23_5063314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 2, 3, 5].length) (baseStart_5063314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5063314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5063314 prefixEnd_5063314 := by exact prefixLift 5063314
  have htrace : WordTrace (prefixWord ++ tailWord_5063314) baseStart_5063314 baseEnd_5063314 := by
    simpa [prefixWord, tailWord_5063314, baseEnd_5063314] using wordTrace_append hprefix tailTrace_5063314
  have hstable : (prefixWord ++ tailWord_5063314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5063314).length < 2 ^ (prefixWord ++ tailWord_5063314).sum := by decide
  have hdescent : baseEnd_5063314 < baseStart_5063314 := by decide
  rcases family_descends (prefixWord ++ tailWord_5063314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5063347 : List Nat := [1, 1, 1, 2, 3, 4, 2, 1, 2, 4, 2]
def baseStart_5063347 : Nat := 118140960795 + 5063347 * 2 ^ 59
def prefixEnd_5063347 : Nat := 4983230072969 + 3 ^ 40 * 5063347 * 2
def baseEnd_5063347 : Nat := 2599930731500906365276597

theorem tailTrace_5063347 : CollatzResearch.WordTrace tailWord_5063347 prefixEnd_5063347 2599930731500906365276597 := by
  unfold tailWord_5063347
  simp only [CollatzResearch.WordTrace]
  refine ⟨184675436787366044666380295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123116957858244029777586863 184675436787366044666380295)
  ·
    refine ⟨277013155181049066999570443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184675436787366044666380295 277013155181049066999570443)
    ·
      refine ⟨415519732771573600499355665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 277013155181049066999570443 415519732771573600499355665)
      ·
        refine ⟨311639799578680200374516749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 415519732771573600499355665 311639799578680200374516749)
        ·
          refine ⟨116864924842005075140443781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 311639799578680200374516749 116864924842005075140443781)
          ·
            refine ⟨21912173407875951588833209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 116864924842005075140443781 21912173407875951588833209)
            ·
              refine ⟨16434130055906963691624907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21912173407875951588833209 16434130055906963691624907)
              ·
                refine ⟨24651195083860445537437361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16434130055906963691624907 24651195083860445537437361)
                ·
                  refine ⟨18488396312895334153078021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24651195083860445537437361 18488396312895334153078021)
                  ·
                    refine ⟨3466574308667875153702129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18488396312895334153078021 3466574308667875153702129)
                    ·
                      refine ⟨2599930731500906365276597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3466574308667875153702129 2599930731500906365276597)
                      ·
                        rfl

theorem cell23_5063347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 1, 2, 4, 2].length) (baseStart_5063347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5063347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5063347 prefixEnd_5063347 := by exact prefixLift 5063347
  have htrace : WordTrace (prefixWord ++ tailWord_5063347) baseStart_5063347 baseEnd_5063347 := by
    simpa [prefixWord, tailWord_5063347, baseEnd_5063347] using wordTrace_append hprefix tailTrace_5063347
  have hstable : (prefixWord ++ tailWord_5063347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5063347).length < 2 ^ (prefixWord ++ tailWord_5063347).sum := by decide
  have hdescent : baseEnd_5063347 < baseStart_5063347 := by decide
  rcases family_descends (prefixWord ++ tailWord_5063347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5063357 : List Nat := [1, 4, 1, 2, 1, 3, 2, 2, 3, 4]
def baseStart_5063357 : Nat := 118140960795 + 5063357 * 2 ^ 59
def prefixEnd_5063357 : Nat := 4983230072969 + 3 ^ 40 * 5063357 * 2
def baseEnd_5063357 : Nat := 866645288769150442050517

theorem tailTrace_5063357 : CollatzResearch.WordTrace tailWord_5063357 prefixEnd_5063357 866645288769150442050517 := by
  unfold tailWord_5063357
  simp only [CollatzResearch.WordTrace]
  refine ⟨184675801517329816374244325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123117201011553210916162883 184675801517329816374244325)
  ·
    refine ⟨34626712784499340570170811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 184675801517329816374244325 34626712784499340570170811)
    ·
      refine ⟨51940069176749010855256217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34626712784499340570170811 51940069176749010855256217)
      ·
        refine ⟨38955051882561758141442163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51940069176749010855256217 38955051882561758141442163)
        ·
          refine ⟨58432577823842637212163245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38955051882561758141442163 58432577823842637212163245)
          ·
            refine ⟨21912216683940988954561217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58432577823842637212163245 21912216683940988954561217)
            ·
              refine ⟨16434162512955741715920913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21912216683940988954561217 16434162512955741715920913)
              ·
                refine ⟨12325621884716806286940685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16434162512955741715920913 12325621884716806286940685)
                ·
                  refine ⟨4622108206768802357602757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12325621884716806286940685 4622108206768802357602757)
                  ·
                    refine ⟨866645288769150442050517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4622108206768802357602757 866645288769150442050517)
                    ·
                      rfl

theorem cell23_5063357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 2, 3, 4].length) (baseStart_5063357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5063357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5063357 prefixEnd_5063357 := by exact prefixLift 5063357
  have htrace : WordTrace (prefixWord ++ tailWord_5063357) baseStart_5063357 baseEnd_5063357 := by
    simpa [prefixWord, tailWord_5063357, baseEnd_5063357] using wordTrace_append hprefix tailTrace_5063357
  have hstable : (prefixWord ++ tailWord_5063357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5063357).length < 2 ^ (prefixWord ++ tailWord_5063357).sum := by decide
  have hdescent : baseEnd_5063357 < baseStart_5063357 := by decide
  rcases family_descends (prefixWord ++ tailWord_5063357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5063363 : List Nat := [1, 1, 1, 3, 1, 1, 1, 1, 1, 3, 9]
def baseStart_5063363 : Nat := 118140960795 + 5063363 * 2 ^ 59
def prefixEnd_5063363 : Nat := 4983230072969 + 3 ^ 40 * 5063363 * 2
def baseEnd_5063363 : Nat := 2599938947191378302676523

theorem tailTrace_5063363 : CollatzResearch.WordTrace tailWord_5063363 prefixEnd_5063363 2599938947191378302676523 := by
  unfold tailWord_5063363
  simp only [CollatzResearch.WordTrace]
  refine ⟨184676020355308079398962743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123117346903538719599308495 184676020355308079398962743)
  ·
    refine ⟨277014030532962119098444115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184676020355308079398962743 277014030532962119098444115)
    ·
      refine ⟨415521045799443178647666173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 277014030532962119098444115 415521045799443178647666173)
      ·
        refine ⟨155820392174791191992874815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 415521045799443178647666173 155820392174791191992874815)
        ·
          refine ⟨233730588262186787989312223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155820392174791191992874815 233730588262186787989312223)
          ·
            refine ⟨350595882393280181983968335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 233730588262186787989312223 350595882393280181983968335)
            ·
              refine ⟨525893823589920272975952503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 350595882393280181983968335 525893823589920272975952503)
              ·
                refine ⟨788840735384880409463928755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 525893823589920272975952503 788840735384880409463928755)
                ·
                  refine ⟨1183261103077320614195893133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 788840735384880409463928755 1183261103077320614195893133)
                  ·
                    refine ⟨443722913653995230323459925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1183261103077320614195893133 443722913653995230323459925)
                    ·
                      refine ⟨2599938947191378302676523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 443722913653995230323459925 2599938947191378302676523)
                      ·
                        rfl

theorem cell23_5063363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 3, 9].length) (baseStart_5063363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5063363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5063363 prefixEnd_5063363 := by exact prefixLift 5063363
  have htrace : WordTrace (prefixWord ++ tailWord_5063363) baseStart_5063363 baseEnd_5063363 := by
    simpa [prefixWord, tailWord_5063363, baseEnd_5063363] using wordTrace_append hprefix tailTrace_5063363
  have hstable : (prefixWord ++ tailWord_5063363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5063363).length < 2 ^ (prefixWord ++ tailWord_5063363).sum := by decide
  have hdescent : baseEnd_5063363 < baseStart_5063363 := by decide
  rcases family_descends (prefixWord ++ tailWord_5063363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5063370 : List Nat := [3, 1, 2, 1, 4, 1, 1, 2, 8]
def baseStart_5063370 : Nat := 118140960795 + 5063370 * 2 ^ 59
def prefixEnd_5063370 : Nat := 4983230072969 + 3 ^ 40 * 5063370 * 2
def baseEnd_5063370 : Nat := 288882504617328863920999

theorem tailTrace_5063370 : CollatzResearch.WordTrace tailWord_5063370 prefixEnd_5063370 288882504617328863920999 := by
  unfold tailWord_5063370
  simp only [CollatzResearch.WordTrace]
  refine ⟨46169068916570679898616891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123117517110855146396311709 46169068916570679898616891)
  ·
    refine ⟨69253603374856019847925337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46169068916570679898616891 69253603374856019847925337)
    ·
      refine ⟨51940202531142014885944003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69253603374856019847925337 51940202531142014885944003)
      ·
        refine ⟨77910303796713022328916005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51940202531142014885944003 77910303796713022328916005)
        ·
          refine ⟨14608181961883691686671751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 77910303796713022328916005 14608181961883691686671751)
          ·
            refine ⟨21912272942825537530007627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14608181961883691686671751 21912272942825537530007627)
            ·
              refine ⟨32868409414238306295011441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21912272942825537530007627 32868409414238306295011441)
              ·
                refine ⟨24651307060678729721258581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32868409414238306295011441 24651307060678729721258581)
                ·
                  refine ⟨288882504617328863920999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24651307060678729721258581 288882504617328863920999)
                  ·
                    rfl

theorem cell23_5063370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 2, 8].length) (baseStart_5063370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5063370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5063370 prefixEnd_5063370 := by exact prefixLift 5063370
  have htrace : WordTrace (prefixWord ++ tailWord_5063370) baseStart_5063370 baseEnd_5063370 := by
    simpa [prefixWord, tailWord_5063370, baseEnd_5063370] using wordTrace_append hprefix tailTrace_5063370
  have hstable : (prefixWord ++ tailWord_5063370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5063370).length < 2 ^ (prefixWord ++ tailWord_5063370).sum := by decide
  have hdescent : baseEnd_5063370 < baseStart_5063370 := by decide
  rcases family_descends (prefixWord ++ tailWord_5063370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5063391 : List Nat := [1, 1, 2, 3, 2, 4, 3, 2, 1, 4]
def baseStart_5063391 : Nat := 118140960795 + 5063391 * 2 ^ 59
def prefixEnd_5063391 : Nat := 4983230072969 + 3 ^ 40 * 5063391 * 2
def baseEnd_5063391 : Nat := 866651108216568064375465

theorem tailTrace_5063391 : CollatzResearch.WordTrace tailWord_5063391 prefixEnd_5063391 866651108216568064375465 := by
  unfold tailWord_5063391
  simp only [CollatzResearch.WordTrace]
  refine ⟨184677041599206640180982027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123118027732804426787321351 184677041599206640180982027)
  ·
    refine ⟨277015562398809960271473041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184677041599206640180982027 277015562398809960271473041)
    ·
      refine ⟨207761671799107470203604781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 277015562398809960271473041 207761671799107470203604781)
      ·
        refine ⟨77910626924665301326351793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 207761671799107470203604781 77910626924665301326351793)
        ·
          refine ⟨58432970193498975994763845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77910626924665301326351793 58432970193498975994763845)
          ·
            refine ⟨10956181911281057999018221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58432970193498975994763845 10956181911281057999018221)
            ·
              refine ⟨4108568216730396749631833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10956181911281057999018221 4108568216730396749631833)
              ·
                refine ⟨3081426162547797562223875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4108568216730396749631833 3081426162547797562223875)
                ·
                  refine ⟨4622139243821696343335813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3081426162547797562223875 4622139243821696343335813)
                  ·
                    refine ⟨866651108216568064375465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4622139243821696343335813 866651108216568064375465)
                    ·
                      rfl

theorem cell23_5063391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 3, 2, 1, 4].length) (baseStart_5063391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5063391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5063391 prefixEnd_5063391 := by exact prefixLift 5063391
  have htrace : WordTrace (prefixWord ++ tailWord_5063391) baseStart_5063391 baseEnd_5063391 := by
    simpa [prefixWord, tailWord_5063391, baseEnd_5063391] using wordTrace_append hprefix tailTrace_5063391
  have hstable : (prefixWord ++ tailWord_5063391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5063391).length < 2 ^ (prefixWord ++ tailWord_5063391).sum := by decide
  have hdescent : baseEnd_5063391 < baseStart_5063391 := by decide
  rcases family_descends (prefixWord ++ tailWord_5063391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5063414 : List Nat := [5, 1, 1, 1, 1, 2, 2, 1, 5, 1, 3]
def baseStart_5063414 : Nat := 118140960795 + 5063414 * 2 ^ 59
def prefixEnd_5063414 : Nat := 4983230072969 + 3 ^ 40 * 5063414 * 2
def baseEnd_5063414 : Nat := 2599965134704757603138789

theorem tailTrace_5063414 : CollatzResearch.WordTrace tailWord_5063414 prefixEnd_5063414 2599965134704757603138789 := by
  unfold tailWord_5063414
  simp only [CollatzResearch.WordTrace]
  refine ⟨11542367529882707194316831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 123118586985415543406046197 11542367529882707194316831)
  ·
    refine ⟨17313551294824060791475247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11542367529882707194316831 17313551294824060791475247)
    ·
      refine ⟨25970326942236091187212871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17313551294824060791475247 25970326942236091187212871)
      ·
        refine ⟨38955490413354136780819307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25970326942236091187212871 38955490413354136780819307)
        ·
          refine ⟨58433235620031205171228961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38955490413354136780819307 58433235620031205171228961)
          ·
            refine ⟨43824926715023403878421721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58433235620031205171228961 43824926715023403878421721)
            ·
              refine ⟨32868695036267552908816291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43824926715023403878421721 32868695036267552908816291)
              ·
                refine ⟨49303042554401329363224437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32868695036267552908816291 49303042554401329363224437)
                ·
                  refine ⟨4622160239475124627802291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 49303042554401329363224437 4622160239475124627802291)
                  ·
                    refine ⟨6933240359212686941703437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4622160239475124627802291 6933240359212686941703437)
                    ·
                      refine ⟨2599965134704757603138789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6933240359212686941703437 2599965134704757603138789)
                      ·
                        rfl

theorem cell23_5063414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 1, 5, 1, 3].length) (baseStart_5063414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5063414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5063414 prefixEnd_5063414 := by exact prefixLift 5063414
  have htrace : WordTrace (prefixWord ++ tailWord_5063414) baseStart_5063414 baseEnd_5063414 := by
    simpa [prefixWord, tailWord_5063414, baseEnd_5063414] using wordTrace_append hprefix tailTrace_5063414
  have hstable : (prefixWord ++ tailWord_5063414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5063414).length < 2 ^ (prefixWord ++ tailWord_5063414).sum := by decide
  have hdescent : baseEnd_5063414 < baseStart_5063414 := by decide
  rcases family_descends (prefixWord ++ tailWord_5063414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5063434 : List Nat := [3, 1, 2, 2, 1, 2, 5, 1, 1, 5]
def baseStart_5063434 : Nat := 118140960795 + 5063434 * 2 ^ 59
def prefixEnd_5063434 : Nat := 4983230072969 + 3 ^ 40 * 5063434 * 2
def baseEnd_5063434 : Nat := 866658468105949174962899

theorem tailTrace_5063434 : CollatzResearch.WordTrace tailWord_5063434 prefixEnd_5063434 866658468105949174962899 := by
  unfold tailWord_5063434
  simp only [CollatzResearch.WordTrace]
  refine ⟨46169652484512714631199339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123119073292033905683198237 46169652484512714631199339)
  ·
    refine ⟨69254478726769071946799009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46169652484512714631199339 69254478726769071946799009)
    ·
      refine ⟨51940859045076803960099257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69254478726769071946799009 51940859045076803960099257)
      ·
        refine ⟨38955644283807602970074443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51940859045076803960099257 38955644283807602970074443)
        ·
          refine ⟨58433466425711404455111665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38955644283807602970074443 58433466425711404455111665)
          ·
            refine ⟨43825099819283553341333749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58433466425711404455111665 43825099819283553341333749)
            ·
              refine ⟨4108603108057833125750039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 43825099819283553341333749 4108603108057833125750039)
              ·
                refine ⟨6162904662086749688625059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4108603108057833125750039 6162904662086749688625059)
                ·
                  refine ⟨9244356993130124532937589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6162904662086749688625059 9244356993130124532937589)
                  ·
                    refine ⟨866658468105949174962899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9244356993130124532937589 866658468105949174962899)
                    ·
                      rfl

theorem cell23_5063434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 5, 1, 1, 5].length) (baseStart_5063434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5063434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5063434 prefixEnd_5063434 := by exact prefixLift 5063434
  have htrace : WordTrace (prefixWord ++ tailWord_5063434) baseStart_5063434 baseEnd_5063434 := by
    simpa [prefixWord, tailWord_5063434, baseEnd_5063434] using wordTrace_append hprefix tailTrace_5063434
  have hstable : (prefixWord ++ tailWord_5063434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5063434).length < 2 ^ (prefixWord ++ tailWord_5063434).sum := by decide
  have hdescent : baseEnd_5063434 < baseStart_5063434 := by decide
  rcases family_descends (prefixWord ++ tailWord_5063434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5063442 : List Nat := [3, 2, 4, 1, 3, 1, 2, 2, 1, 4]
def baseStart_5063442 : Nat := 118140960795 + 5063442 * 2 ^ 59
def prefixEnd_5063442 : Nat := 4983230072969 + 3 ^ 40 * 5063442 * 2
def baseEnd_5063442 : Nat := 866659837387694497862887

theorem tailTrace_5063442 : CollatzResearch.WordTrace tailWord_5063442 prefixEnd_5063442 866659837387694497862887 := by
  unfold tailWord_5063442
  simp only [CollatzResearch.WordTrace]
  refine ⟨46169725430505468972772145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123119267814681250594059053 46169725430505468972772145)
  ·
    refine ⟨34627294072879101729579109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46169725430505468972772145 34627294072879101729579109)
    ·
      refine ⟨6492617638664831574296083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34627294072879101729579109 6492617638664831574296083)
      ·
        refine ⟨9738926457997247361444125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6492617638664831574296083 9738926457997247361444125)
        ·
          refine ⟨3652097421748967760541547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9738926457997247361444125 3652097421748967760541547)
          ·
            refine ⟨5478146132623451640812321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3652097421748967760541547 5478146132623451640812321)
            ·
              refine ⟨4108609599467588730609241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5478146132623451640812321 4108609599467588730609241)
              ·
                refine ⟨3081457199600691547956931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4108609599467588730609241 3081457199600691547956931)
                ·
                  refine ⟨4622185799401037321935397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3081457199600691547956931 4622185799401037321935397)
                  ·
                    refine ⟨866659837387694497862887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4622185799401037321935397 866659837387694497862887)
                    ·
                      rfl

theorem cell23_5063442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 2, 2, 1, 4].length) (baseStart_5063442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5063442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5063442 prefixEnd_5063442 := by exact prefixLift 5063442
  have htrace : WordTrace (prefixWord ++ tailWord_5063442) baseStart_5063442 baseEnd_5063442 := by
    simpa [prefixWord, tailWord_5063442, baseEnd_5063442] using wordTrace_append hprefix tailTrace_5063442
  have hstable : (prefixWord ++ tailWord_5063442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5063442).length < 2 ^ (prefixWord ++ tailWord_5063442).sum := by decide
  have hdescent : baseEnd_5063442 < baseStart_5063442 := by decide
  rcases family_descends (prefixWord ++ tailWord_5063442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5063457 : List Nat := [1, 2, 3, 2, 1, 2, 1, 1, 5, 2, 3]
def baseStart_5063457 : Nat := 118140960795 + 5063457 * 2 ^ 59
def prefixEnd_5063457 : Nat := 4983230072969 + 3 ^ 40 * 5063457 * 2
def baseEnd_5063457 : Nat := 2599987214372900934901091

theorem tailTrace_5063457 : CollatzResearch.WordTrace tailWord_5063457 prefixEnd_5063457 2599987214372900934901091 := by
  unfold tailWord_5063457
  simp only [CollatzResearch.WordTrace]
  refine ⟨184679448816967533452884625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123119632544645022301923083 184679448816967533452884625)
  ·
    refine ⟨138509586612725650089663469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184679448816967533452884625 138509586612725650089663469)
    ·
      refine ⟨51941094979772118783623801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 138509586612725650089663469 51941094979772118783623801)
      ·
        refine ⟨38955821234829089087717851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51941094979772118783623801 38955821234829089087717851)
        ·
          refine ⟨58433731852243633631576777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38955821234829089087717851 58433731852243633631576777)
          ·
            refine ⟨43825298889182725223682583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58433731852243633631576777 43825298889182725223682583)
            ·
              refine ⟨65737948333774087835523875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43825298889182725223682583 65737948333774087835523875)
              ·
                refine ⟨98606922500661131753285813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65737948333774087835523875 98606922500661131753285813)
                ·
                  refine ⟨9244398984436981101870545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 98606922500661131753285813 9244398984436981101870545)
                  ·
                    refine ⟨6933299238327735826402909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9244398984436981101870545 6933299238327735826402909)
                    ·
                      refine ⟨2599987214372900934901091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6933299238327735826402909 2599987214372900934901091)
                      ·
                        rfl

theorem cell23_5063457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 1, 5, 2, 3].length) (baseStart_5063457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5063457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5063457 prefixEnd_5063457 := by exact prefixLift 5063457
  have htrace : WordTrace (prefixWord ++ tailWord_5063457) baseStart_5063457 baseEnd_5063457 := by
    simpa [prefixWord, tailWord_5063457, baseEnd_5063457] using wordTrace_append hprefix tailTrace_5063457
  have hstable : (prefixWord ++ tailWord_5063457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5063457).length < 2 ^ (prefixWord ++ tailWord_5063457).sum := by decide
  have hdescent : baseEnd_5063457 < baseStart_5063457 := by decide
  rcases family_descends (prefixWord ++ tailWord_5063457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5063464 : List Nat := [2, 1, 5, 1, 1, 1, 1, 5, 2, 4]
def baseStart_5063464 : Nat := 118140960795 + 5063464 * 2 ^ 59
def prefixEnd_5063464 : Nat := 4983230072969 + 3 ^ 40 * 5063464 * 2
def baseEnd_5063464 : Nat := 866663602912494135837853

theorem tailTrace_5063464 : CollatzResearch.WordTrace tailWord_5063464 prefixEnd_5063464 866663602912494135837853 := by
  unfold tailWord_5063464
  simp only [CollatzResearch.WordTrace]
  refine ⟨92339852063971086824194723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123119802751961449098926297 92339852063971086824194723)
  ·
    refine ⟨138509778095956630236292085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92339852063971086824194723 138509778095956630236292085)
    ·
      refine ⟨12985291696495934084652383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 138509778095956630236292085 12985291696495934084652383)
      ·
        refine ⟨19477937544743901126978575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12985291696495934084652383 19477937544743901126978575)
        ·
          refine ⟨29216906317115851690467863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19477937544743901126978575 29216906317115851690467863)
          ·
            refine ⟨43825359475673777535701795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29216906317115851690467863 43825359475673777535701795)
            ·
              refine ⟨65738039213510666303552693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43825359475673777535701795 65738039213510666303552693)
              ·
                refine ⟨6162941176266624965958065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 65738039213510666303552693 6162941176266624965958065)
                ·
                  refine ⟨4622205882199968724468549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6162941176266624965958065 4622205882199968724468549)
                  ·
                    refine ⟨866663602912494135837853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4622205882199968724468549 866663602912494135837853)
                    ·
                      rfl

theorem cell23_5063464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 5, 2, 4].length) (baseStart_5063464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5063464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5063464 prefixEnd_5063464 := by exact prefixLift 5063464
  have htrace : WordTrace (prefixWord ++ tailWord_5063464) baseStart_5063464 baseEnd_5063464 := by
    simpa [prefixWord, tailWord_5063464, baseEnd_5063464] using wordTrace_append hprefix tailTrace_5063464
  have hstable : (prefixWord ++ tailWord_5063464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5063464).length < 2 ^ (prefixWord ++ tailWord_5063464).sum := by decide
  have hdescent : baseEnd_5063464 < baseStart_5063464 := by decide
  rcases family_descends (prefixWord ++ tailWord_5063464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5063474 : List Nat := [3, 2, 1, 1, 3, 1, 2, 4, 1, 2, 3]
def baseStart_5063474 : Nat := 118140960795 + 5063474 * 2 ^ 59
def prefixEnd_5063474 : Nat := 4983230072969 + 3 ^ 40 * 5063474 * 2
def baseEnd_5063474 : Nat := 2599995943544027368388513

theorem tailTrace_5063474 : CollatzResearch.WordTrace tailWord_5063474 prefixEnd_5063474 2599995943544027368388513 := by
  unfold tailWord_5063474
  simp only [CollatzResearch.WordTrace]
  refine ⟨46170017214476486339063369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123120045905270630237502317 46170017214476486339063369)
  ·
    refine ⟨34627512910857364754297527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46170017214476486339063369 34627512910857364754297527)
    ·
      refine ⟨51941269366286047131446291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34627512910857364754297527 51941269366286047131446291)
      ·
        refine ⟨77911904049429070697169437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51941269366286047131446291 77911904049429070697169437)
        ·
          refine ⟨29216964018535901511438539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77911904049429070697169437 29216964018535901511438539)
          ·
            refine ⟨43825446027803852267157809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29216964018535901511438539 43825446027803852267157809)
            ·
              refine ⟨32869084520852889200368357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43825446027803852267157809 32869084520852889200368357)
              ·
                refine ⟨6162953347659916725069067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32869084520852889200368357 6162953347659916725069067)
                ·
                  refine ⟨9244430021489875087603601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6162953347659916725069067 9244430021489875087603601)
                  ·
                    refine ⟨6933322516117406315702701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9244430021489875087603601 6933322516117406315702701)
                    ·
                      refine ⟨2599995943544027368388513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6933322516117406315702701 2599995943544027368388513)
                      ·
                        rfl

theorem cell23_5063474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 4, 1, 2, 3].length) (baseStart_5063474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5063474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5063474 prefixEnd_5063474 := by exact prefixLift 5063474
  have htrace : WordTrace (prefixWord ++ tailWord_5063474) baseStart_5063474 baseEnd_5063474 := by
    simpa [prefixWord, tailWord_5063474, baseEnd_5063474] using wordTrace_append hprefix tailTrace_5063474
  have hstable : (prefixWord ++ tailWord_5063474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5063474).length < 2 ^ (prefixWord ++ tailWord_5063474).sum := by decide
  have hdescent : baseEnd_5063474 < baseStart_5063474 := by decide
  rcases family_descends (prefixWord ++ tailWord_5063474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5063561 : List Nat := [1, 2, 1, 1, 5, 2, 2, 1, 4, 2, 2]
def baseStart_5063561 : Nat := 118140960795 + 5063561 * 2 ^ 59
def prefixEnd_5063561 : Nat := 4983230072969 + 3 ^ 40 * 5063561 * 2
def baseEnd_5063561 : Nat := 2600040616360968528000613

theorem tailTrace_5063561 : CollatzResearch.WordTrace tailWord_5063561 prefixEnd_5063561 2600040616360968528000613 := by
  unfold tailWord_5063561
  simp only [CollatzResearch.WordTrace]
  refine ⟨184683242008590759214670537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123122161339060506143113691 184683242008590759214670537)
  ·
    refine ⟨138512431506443069411002903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184683242008590759214670537 138512431506443069411002903)
    ·
      refine ⟨207768647259664604116504355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138512431506443069411002903 207768647259664604116504355)
      ·
        refine ⟨311652970889496906174756533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 207768647259664604116504355 311652970889496906174756533)
        ·
          refine ⟨29217466020890334953883425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 311652970889496906174756533 29217466020890334953883425)
          ·
            refine ⟨21913099515667751215412569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29217466020890334953883425 21913099515667751215412569)
            ·
              refine ⟨16434824636750813411559427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21913099515667751215412569 16434824636750813411559427)
              ·
                refine ⟨24652236955126220117339141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16434824636750813411559427 24652236955126220117339141)
                ·
                  refine ⟨4622294429086166272001089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24652236955126220117339141 4622294429086166272001089)
                  ·
                    refine ⟨3466720821814624704000817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4622294429086166272001089 3466720821814624704000817)
                    ·
                      refine ⟨2600040616360968528000613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3466720821814624704000817 2600040616360968528000613)
                      ·
                        rfl

theorem cell23_5063561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 1, 4, 2, 2].length) (baseStart_5063561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5063561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5063561 prefixEnd_5063561 := by exact prefixLift 5063561
  have htrace : WordTrace (prefixWord ++ tailWord_5063561) baseStart_5063561 baseEnd_5063561 := by
    simpa [prefixWord, tailWord_5063561, baseEnd_5063561] using wordTrace_append hprefix tailTrace_5063561
  have hstable : (prefixWord ++ tailWord_5063561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5063561).length < 2 ^ (prefixWord ++ tailWord_5063561).sum := by decide
  have hdescent : baseEnd_5063561 < baseStart_5063561 := by decide
  rcases family_descends (prefixWord ++ tailWord_5063561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5063577 : List Nat := [1, 2, 1, 2, 1, 3, 1, 3, 1, 5, 3]
def baseStart_5063577 : Nat := 118140960795 + 5063577 * 2 ^ 59
def prefixEnd_5063577 : Nat := 4983230072969 + 3 ^ 40 * 5063577 * 2
def baseEnd_5063577 : Nat := 2600048832051440465400539

theorem tailTrace_5063577 : CollatzResearch.WordTrace tailWord_5063577 prefixEnd_5063577 2600048832051440465400539 := by
  unfold tailWord_5063577
  simp only [CollatzResearch.WordTrace]
  refine ⟨184683825576532793947252985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123122550384355195964835323 184683825576532793947252985)
  ·
    refine ⟨138512869182399595460439739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184683825576532793947252985 138512869182399595460439739)
    ·
      refine ⟨207769303773599393190659609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138512869182399595460439739 207769303773599393190659609)
      ·
        refine ⟨155826977830199544892994707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 207769303773599393190659609 155826977830199544892994707)
        ·
          refine ⟨233740466745299317339492061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155826977830199544892994707 233740466745299317339492061)
          ·
            refine ⟨87652675029487244002309523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 233740466745299317339492061 87652675029487244002309523)
            ·
              refine ⟨131479012544230866003464285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87652675029487244002309523 131479012544230866003464285)
              ·
                refine ⟨49304629704086574751299107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 131479012544230866003464285 49304629704086574751299107)
                ·
                  refine ⟨73956944556129862126948661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49304629704086574751299107 73956944556129862126948661)
                  ·
                    refine ⟨6933463552137174574401437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 73956944556129862126948661 6933463552137174574401437)
                    ·
                      refine ⟨2600048832051440465400539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6933463552137174574401437 2600048832051440465400539)
                      ·
                        rfl

theorem cell23_5063577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 3, 1, 5, 3].length) (baseStart_5063577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5063577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5063577 prefixEnd_5063577 := by exact prefixLift 5063577
  have htrace : WordTrace (prefixWord ++ tailWord_5063577) baseStart_5063577 baseEnd_5063577 := by
    simpa [prefixWord, tailWord_5063577, baseEnd_5063577] using wordTrace_append hprefix tailTrace_5063577
  have hstable : (prefixWord ++ tailWord_5063577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5063577).length < 2 ^ (prefixWord ++ tailWord_5063577).sum := by decide
  have hdescent : baseEnd_5063577 < baseStart_5063577 := by decide
  rcases family_descends (prefixWord ++ tailWord_5063577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5063607 : List Nat := [1, 1, 3, 1, 3, 1, 3, 2, 1, 2, 5]
def baseStart_5063607 : Nat := 118140960795 + 5063607 * 2 ^ 59
def prefixEnd_5063607 : Nat := 4983230072969 + 3 ^ 40 * 5063607 * 2
def baseEnd_5063607 : Nat := 2600064236471075348025401

theorem tailTrace_5063607 : CollatzResearch.WordTrace tailWord_5063607 prefixEnd_5063607 2600064236471075348025401 := by
  unfold tailWord_5063607
  simp only [CollatzResearch.WordTrace]
  refine ⟨184684919766424109070845075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123123279844282739380563383 184684919766424109070845075)
  ·
    refine ⟨277027379649636163606267613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184684919766424109070845075 277027379649636163606267613)
    ·
      refine ⟨103885267368613561352350355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 277027379649636163606267613 103885267368613561352350355)
      ·
        refine ⟨155827901052920342028525533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103885267368613561352350355 155827901052920342028525533)
        ·
          refine ⟨58435462894845128260697075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 155827901052920342028525533 58435462894845128260697075)
          ·
            refine ⟨87653194342267692391045613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58435462894845128260697075 87653194342267692391045613)
            ·
              refine ⟨32869947878350384646642105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 87653194342267692391045613 32869947878350384646642105)
              ·
                refine ⟨24652460908762788484981579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32869947878350384646642105 24652460908762788484981579)
                ·
                  refine ⟨36978691363144182727472369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24652460908762788484981579 36978691363144182727472369)
                  ·
                    refine ⟨27734018522358137045604277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36978691363144182727472369 27734018522358137045604277)
                    ·
                      refine ⟨2600064236471075348025401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27734018522358137045604277 2600064236471075348025401)
                      ·
                        rfl

theorem cell23_5063607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 2, 1, 2, 5].length) (baseStart_5063607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5063607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5063607 prefixEnd_5063607 := by exact prefixLift 5063607
  have htrace : WordTrace (prefixWord ++ tailWord_5063607) baseStart_5063607 baseEnd_5063607 := by
    simpa [prefixWord, tailWord_5063607, baseEnd_5063607] using wordTrace_append hprefix tailTrace_5063607
  have hstable : (prefixWord ++ tailWord_5063607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5063607).length < 2 ^ (prefixWord ++ tailWord_5063607).sum := by decide
  have hdescent : baseEnd_5063607 < baseStart_5063607 := by decide
  rcases family_descends (prefixWord ++ tailWord_5063607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5063614 : List Nat := [4, 2, 1, 1, 1, 2, 1, 4, 2, 5]
def baseStart_5063614 : Nat := 118140960795 + 5063614 * 2 ^ 59
def prefixEnd_5063614 : Nat := 4983230072969 + 3 ^ 40 * 5063614 * 2
def baseEnd_5063614 : Nat := 866689276945218940212623

theorem tailTrace_5063614 : CollatzResearch.WordTrace tailWord_5063614 prefixEnd_5063614 866689276945218940212623 := by
  unfold tailWord_5063614
  simp only [CollatzResearch.WordTrace]
  refine ⟨23085646884674843658293737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 123123450051599166177566597 23085646884674843658293737)
  ·
    refine ⟨17314235163506132743720303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23085646884674843658293737 17314235163506132743720303)
    ·
      refine ⟨25971352745259199115580455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17314235163506132743720303 25971352745259199115580455)
      ·
        refine ⟨38957029117888798673370683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25971352745259199115580455 38957029117888798673370683)
        ·
          refine ⟨58435543676833198010056025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38957029117888798673370683 58435543676833198010056025)
          ·
            refine ⟨43826657757624898507542019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58435543676833198010056025 43826657757624898507542019)
            ·
              refine ⟨65739986636437347761313029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43826657757624898507542019 65739986636437347761313029)
              ·
                refine ⟨12326247494332002705246193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 65739986636437347761313029 12326247494332002705246193)
                ·
                  refine ⟨9244685620749002028934645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12326247494332002705246193 9244685620749002028934645)
                  ·
                    refine ⟨866689276945218940212623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9244685620749002028934645 866689276945218940212623)
                    ·
                      rfl

theorem cell23_5063614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 4, 2, 5].length) (baseStart_5063614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5063614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5063614 prefixEnd_5063614 := by exact prefixLift 5063614
  have htrace : WordTrace (prefixWord ++ tailWord_5063614) baseStart_5063614 baseEnd_5063614 := by
    simpa [prefixWord, tailWord_5063614, baseEnd_5063614] using wordTrace_append hprefix tailTrace_5063614
  have hstable : (prefixWord ++ tailWord_5063614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5063614).length < 2 ^ (prefixWord ++ tailWord_5063614).sum := by decide
  have hdescent : baseEnd_5063614 < baseStart_5063614 := by decide
  rcases family_descends (prefixWord ++ tailWord_5063614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5063691 : List Nat := [1, 1, 1, 1, 6, 3, 3, 1, 6]
def baseStart_5063691 : Nat := 118140960795 + 5063691 * 2 ^ 59
def prefixEnd_5063691 : Nat := 4983230072969 + 3 ^ 40 * 5063691 * 2
def baseEnd_5063691 : Nat := 288900818760672557708335

theorem tailTrace_5063691 : CollatzResearch.WordTrace tailWord_5063691 prefixEnd_5063691 288900818760672557708335 := by
  unfold tailWord_5063691
  simp only [CollatzResearch.WordTrace]
  refine ⟨184687983498119791416902927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123125322332079860944601951 184687983498119791416902927)
  ·
    refine ⟨277031975247179687125354391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184687983498119791416902927 277031975247179687125354391)
    ·
      refine ⟨415547962870769530688031587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 277031975247179687125354391 415547962870769530688031587)
      ·
        refine ⟨623321944306154296032047381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 415547962870769530688031587 623321944306154296032047381)
        ·
          refine ⟨29218216139350982626502221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 623321944306154296032047381 29218216139350982626502221)
          ·
            refine ⟨10956831052256618484938333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29218216139350982626502221 10956831052256618484938333)
            ·
              refine ⟨4108811644596231931851875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10956831052256618484938333 4108811644596231931851875)
              ·
                refine ⟨6163217466894347897777813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4108811644596231931851875 6163217466894347897777813)
                ·
                  refine ⟨288900818760672557708335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6163217466894347897777813 288900818760672557708335)
                  ·
                    rfl

theorem cell23_5063691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 3, 1, 6].length) (baseStart_5063691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5063691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5063691 prefixEnd_5063691 := by exact prefixLift 5063691
  have htrace : WordTrace (prefixWord ++ tailWord_5063691) baseStart_5063691 baseEnd_5063691 := by
    simpa [prefixWord, tailWord_5063691, baseEnd_5063691] using wordTrace_append hprefix tailTrace_5063691
  have hstable : (prefixWord ++ tailWord_5063691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5063691).length < 2 ^ (prefixWord ++ tailWord_5063691).sum := by decide
  have hdescent : baseEnd_5063691 < baseStart_5063691 := by decide
  rcases family_descends (prefixWord ++ tailWord_5063691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5063697 : List Nat := [1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 7]
def baseStart_5063697 : Nat := 118140960795 + 5063697 * 2 ^ 59
def prefixEnd_5063697 : Nat := 4983230072969 + 3 ^ 40 * 5063697 * 2
def baseEnd_5063697 : Nat := 2600110449729979995899987

theorem tailTrace_5063697 : CollatzResearch.WordTrace tailWord_5063697 prefixEnd_5063697 2600110449729979995899987 := by
  unfold tailWord_5063697
  simp only [CollatzResearch.WordTrace]
  refine ⟨184688202336098054441621345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123125468224065369627747563 184688202336098054441621345)
  ·
    refine ⟨138516151752073540831216009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184688202336098054441621345 138516151752073540831216009)
    ·
      refine ⟨103887113814055155623412007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138516151752073540831216009 103887113814055155623412007)
      ·
        refine ⟨155830670721082733435118011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103887113814055155623412007 155830670721082733435118011)
        ·
          refine ⟨233746006081624100152677017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155830670721082733435118011 233746006081624100152677017)
          ·
            refine ⟨175309504561218075114507763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 233746006081624100152677017 175309504561218075114507763)
            ·
              refine ⟨262964256841827112671761645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 175309504561218075114507763 262964256841827112671761645)
              ·
                refine ⟨98611596315685167251910617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 262964256841827112671761645 98611596315685167251910617)
                ·
                  refine ⟨73958697236763875438932963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 98611596315685167251910617 73958697236763875438932963)
                  ·
                    refine ⟨110938045855145813158399445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 73958697236763875438932963 110938045855145813158399445)
                    ·
                      refine ⟨2600110449729979995899987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 110938045855145813158399445 2600110449729979995899987)
                      ·
                        rfl

theorem cell23_5063697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 7].length) (baseStart_5063697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5063697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5063697 prefixEnd_5063697 := by exact prefixLift 5063697
  have htrace : WordTrace (prefixWord ++ tailWord_5063697) baseStart_5063697 baseEnd_5063697 := by
    simpa [prefixWord, tailWord_5063697, baseEnd_5063697] using wordTrace_append hprefix tailTrace_5063697
  have hstable : (prefixWord ++ tailWord_5063697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5063697).length < 2 ^ (prefixWord ++ tailWord_5063697).sum := by decide
  have hdescent : baseEnd_5063697 < baseStart_5063697 := by decide
  rcases family_descends (prefixWord ++ tailWord_5063697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5063711 : List Nat := [1, 1, 2, 4, 1, 3, 2, 1, 1, 5, 2]
def baseStart_5063711 : Nat := 118140960795 + 5063711 * 2 ^ 59
def prefixEnd_5063711 : Nat := 4983230072969 + 3 ^ 40 * 5063711 * 2
def baseEnd_5063711 : Nat := 2600117638459142941124923

theorem tailTrace_5063711 : CollatzResearch.WordTrace tailWord_5063711 prefixEnd_5063711 2600117638459142941124923 := by
  unfold tailWord_5063711
  simp only [CollatzResearch.WordTrace]
  refine ⟨184688712958047334832630987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123125808638698223221753991 184688712958047334832630987)
  ·
    refine ⟨277033069437071002248946481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184688712958047334832630987 277033069437071002248946481)
    ·
      refine ⟨207774802077803251686709861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 277033069437071002248946481 207774802077803251686709861)
      ·
        refine ⟨38957775389588109691258099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 207774802077803251686709861 38957775389588109691258099)
        ·
          refine ⟨58436663084382164536887149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38957775389588109691258099 58436663084382164536887149)
          ·
            refine ⟨21913748656643311701332681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58436663084382164536887149 21913748656643311701332681)
            ·
              refine ⟨16435311492482483775999511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21913748656643311701332681 16435311492482483775999511)
              ·
                refine ⟨24652967238723725663999267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16435311492482483775999511 24652967238723725663999267)
                ·
                  refine ⟨36979450858085588495998901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24652967238723725663999267 36979450858085588495998901)
                  ·
                    refine ⟨3466823517945523921499897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 36979450858085588495998901 3466823517945523921499897)
                    ·
                      refine ⟨2600117638459142941124923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3466823517945523921499897 2600117638459142941124923)
                      ·
                        rfl

theorem cell23_5063711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 1, 1, 5, 2].length) (baseStart_5063711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5063711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5063711 prefixEnd_5063711 := by exact prefixLift 5063711
  have htrace : WordTrace (prefixWord ++ tailWord_5063711) baseStart_5063711 baseEnd_5063711 := by
    simpa [prefixWord, tailWord_5063711, baseEnd_5063711] using wordTrace_append hprefix tailTrace_5063711
  have hstable : (prefixWord ++ tailWord_5063711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5063711).length < 2 ^ (prefixWord ++ tailWord_5063711).sum := by decide
  have hdescent : baseEnd_5063711 < baseStart_5063711 := by decide
  rcases family_descends (prefixWord ++ tailWord_5063711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5063712 : List Nat := [2, 1, 1, 7, 1, 2, 1, 3, 1, 4]
def baseStart_5063712 : Nat := 118140960795 + 5063712 * 2 ^ 59
def prefixEnd_5063712 : Nat := 4983230072969 + 3 ^ 40 * 5063712 * 2
def baseEnd_5063712 : Nat := 866706050646599145737473

theorem tailTrace_5063712 : CollatzResearch.WordTrace tailWord_5063712 prefixEnd_5063712 866706050646599145737473 := by
  unfold tailWord_5063712
  simp only [CollatzResearch.WordTrace]
  refine ⟨92344374715521856001708695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123125832954029141335611593 92344374715521856001708695)
  ·
    refine ⟨138516562073282784002563043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92344374715521856001708695 138516562073282784002563043)
    ·
      refine ⟨207774843109924176003844565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138516562073282784002563043 207774843109924176003844565)
      ·
        refine ⟨4869722885388847875090107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 207774843109924176003844565 4869722885388847875090107)
        ·
          refine ⟨7304584328083271812635161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4869722885388847875090107 7304584328083271812635161)
          ·
            refine ⟨5478438246062453859476371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7304584328083271812635161 5478438246062453859476371)
            ·
              refine ⟨8217657369093680789214557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5478438246062453859476371 8217657369093680789214557)
              ·
                refine ⟨3081621513410130295955459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8217657369093680789214557 3081621513410130295955459)
                ·
                  refine ⟨4622432270115195443933189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3081621513410130295955459 4622432270115195443933189)
                  ·
                    refine ⟨866706050646599145737473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4622432270115195443933189 866706050646599145737473)
                    ·
                      rfl

theorem cell23_5063712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 1, 3, 1, 4].length) (baseStart_5063712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5063712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5063712 prefixEnd_5063712 := by exact prefixLift 5063712
  have htrace : WordTrace (prefixWord ++ tailWord_5063712) baseStart_5063712 baseEnd_5063712 := by
    simpa [prefixWord, tailWord_5063712, baseEnd_5063712] using wordTrace_append hprefix tailTrace_5063712
  have hstable : (prefixWord ++ tailWord_5063712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5063712).length < 2 ^ (prefixWord ++ tailWord_5063712).sum := by decide
  have hdescent : baseEnd_5063712 < baseStart_5063712 := by decide
  rcases family_descends (prefixWord ++ tailWord_5063712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5063744 : List Nat := [2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 5]
def baseStart_5063744 : Nat := 118140960795 + 5063744 * 2 ^ 59
def prefixEnd_5063744 : Nat := 4983230072969 + 3 ^ 40 * 5063744 * 2
def baseEnd_5063744 : Nat := 2600134583320741312012271

theorem tailTrace_5063744 : CollatzResearch.WordTrace tailWord_5063744 prefixEnd_5063744 2600134583320741312012271 := by
  unfold tailWord_5063744
  simp only [CollatzResearch.WordTrace]
  refine ⟨92344958283463890734291143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123126611044618520979054857 92344958283463890734291143)
  ·
    refine ⟨138517437425195836101436715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92344958283463890734291143 138517437425195836101436715)
    ·
      refine ⟨207776156137793754152155073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138517437425195836101436715 207776156137793754152155073)
      ·
        refine ⟨155832117103345315614116305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 207776156137793754152155073 155832117103345315614116305)
        ·
          refine ⟨116874087827508986710587229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 155832117103345315614116305 116874087827508986710587229)
          ·
            refine ⟨43827782935315870016470211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 116874087827508986710587229 43827782935315870016470211)
            ·
              refine ⟨65741674402973805024705317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43827782935315870016470211 65741674402973805024705317)
              ·
                refine ⟨12326563950557588442132247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 65741674402973805024705317 12326563950557588442132247)
                ·
                  refine ⟨18489845925836382663198371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12326563950557588442132247 18489845925836382663198371)
                  ·
                    refine ⟨27734768888754573994797557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18489845925836382663198371 27734768888754573994797557)
                    ·
                      refine ⟨2600134583320741312012271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27734768888754573994797557 2600134583320741312012271)
                      ·
                        rfl

theorem cell23_5063744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 5].length) (baseStart_5063744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5063744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5063744 prefixEnd_5063744 := by exact prefixLift 5063744
  have htrace : WordTrace (prefixWord ++ tailWord_5063744) baseStart_5063744 baseEnd_5063744 := by
    simpa [prefixWord, tailWord_5063744, baseEnd_5063744] using wordTrace_append hprefix tailTrace_5063744
  have hstable : (prefixWord ++ tailWord_5063744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5063744).length < 2 ^ (prefixWord ++ tailWord_5063744).sum := by decide
  have hdescent : baseEnd_5063744 < baseStart_5063744 := by decide
  rcases family_descends (prefixWord ++ tailWord_5063744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5063754 : List Nat := [3, 1, 2, 1, 1, 2, 4, 1, 1, 1, 6]
def baseStart_5063754 : Nat := 118140960795 + 5063754 * 2 ^ 59
def prefixEnd_5063754 : Nat := 4983230072969 + 3 ^ 40 * 5063754 * 2
def baseEnd_5063754 : Nat := 2600139718127286272887225

theorem tailTrace_5063754 : CollatzResearch.WordTrace tailWord_5063754 prefixEnd_5063754 2600139718127286272887225 := by
  unfold tailWord_5063754
  simp only [CollatzResearch.WordTrace]
  refine ⟨46172570324222888294111579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123126854197927702117630877 46172570324222888294111579)
  ·
    refine ⟨69258855486334332441167369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46172570324222888294111579 69258855486334332441167369)
    ·
      refine ⟨51944141614750749330875527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69258855486334332441167369 51944141614750749330875527)
      ·
        refine ⟨77916212422126123996313291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51944141614750749330875527 77916212422126123996313291)
        ·
          refine ⟨116874318633189185994469937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77916212422126123996313291 116874318633189185994469937)
          ·
            refine ⟨87655738974891889495852453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 116874318633189185994469937 87655738974891889495852453)
            ·
              refine ⟨16435451057792229280472335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 87655738974891889495852453 16435451057792229280472335)
              ·
                refine ⟨24653176586688343920708503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16435451057792229280472335 24653176586688343920708503)
                ·
                  refine ⟨36979764880032515881062755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24653176586688343920708503 36979764880032515881062755)
                  ·
                    refine ⟨55469647320048773821594133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36979764880032515881062755 55469647320048773821594133)
                    ·
                      refine ⟨2600139718127286272887225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 55469647320048773821594133 2600139718127286272887225)
                      ·
                        rfl

theorem cell23_5063754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 1, 1, 1, 6].length) (baseStart_5063754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5063754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5063754 prefixEnd_5063754 := by exact prefixLift 5063754
  have htrace : WordTrace (prefixWord ++ tailWord_5063754) baseStart_5063754 baseEnd_5063754 := by
    simpa [prefixWord, tailWord_5063754, baseEnd_5063754] using wordTrace_append hprefix tailTrace_5063754
  have hstable : (prefixWord ++ tailWord_5063754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5063754).length < 2 ^ (prefixWord ++ tailWord_5063754).sum := by decide
  have hdescent : baseEnd_5063754 < baseStart_5063754 := by decide
  rcases family_descends (prefixWord ++ tailWord_5063754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5063758 : List Nat := [4, 1, 1, 1, 1, 3, 2, 1, 5, 2, 2]
def baseStart_5063758 : Nat := 118140960795 + 5063758 * 2 ^ 59
def prefixEnd_5063758 : Nat := 4983230072969 + 3 ^ 40 * 5063758 * 2
def baseEnd_5063758 : Nat := 2600141772049904257237207

theorem tailTrace_5063758 : CollatzResearch.WordTrace tailWord_5063758 prefixEnd_5063758 2600141772049904257237207 := by
  unfold tailWord_5063758
  simp only [CollatzResearch.WordTrace]
  refine ⟨23086303398609632732448991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 123126951459251374573061285 23086303398609632732448991)
  ·
    refine ⟨34629455097914449098673487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23086303398609632732448991 34629455097914449098673487)
    ·
      refine ⟨51944182646871673648010231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34629455097914449098673487 51944182646871673648010231)
      ·
        refine ⟨77916273970307510472015347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51944182646871673648010231 77916273970307510472015347)
        ·
          refine ⟨116874410955461265708023021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77916273970307510472015347 116874410955461265708023021)
          ·
            refine ⟨43827904108297974640508633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 116874410955461265708023021 43827904108297974640508633)
            ·
              refine ⟨32870928081223480980381475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43827904108297974640508633 32870928081223480980381475)
              ·
                refine ⟨49306392121835221470572213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32870928081223480980381475 49306392121835221470572213)
                ·
                  refine ⟨4622474261422052012866145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 49306392121835221470572213 4622474261422052012866145)
                  ·
                    refine ⟨3466855696066539009649609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4622474261422052012866145 3466855696066539009649609)
                    ·
                      refine ⟨2600141772049904257237207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3466855696066539009649609 2600141772049904257237207)
                      ·
                        rfl

theorem cell23_5063758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 1, 5, 2, 2].length) (baseStart_5063758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5063758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5063758 prefixEnd_5063758 := by exact prefixLift 5063758
  have htrace : WordTrace (prefixWord ++ tailWord_5063758) baseStart_5063758 baseEnd_5063758 := by
    simpa [prefixWord, tailWord_5063758, baseEnd_5063758] using wordTrace_append hprefix tailTrace_5063758
  have hstable : (prefixWord ++ tailWord_5063758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5063758).length < 2 ^ (prefixWord ++ tailWord_5063758).sum := by decide
  have hdescent : baseEnd_5063758 < baseStart_5063758 := by decide
  rcases family_descends (prefixWord ++ tailWord_5063758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5063764 : List Nat := [2, 4, 1, 1, 1, 1, 4, 9]
def baseStart_5063764 : Nat := 118140960795 + 5063764 * 2 ^ 59
def prefixEnd_5063764 : Nat := 4983230072969 + 3 ^ 40 * 5063764 * 2
def baseEnd_5063764 : Nat := 96301661219771527176377

theorem tailTrace_5063764 : CollatzResearch.WordTrace tailWord_5063764 prefixEnd_5063764 96301661219771527176377 := by
  unfold tailWord_5063764
  simp only [CollatzResearch.WordTrace]
  refine ⟨92345323013427662442155173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123127097351236883256206897 92345323013427662442155173)
  ·
    refine ⟨17314748065017686707904095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 92345323013427662442155173 17314748065017686707904095)
    ·
      refine ⟨25972122097526530061856143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17314748065017686707904095 25972122097526530061856143)
      ·
        refine ⟨38958183146289795092784215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25972122097526530061856143 38958183146289795092784215)
        ·
          refine ⟨58437274719434692639176323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38958183146289795092784215 58437274719434692639176323)
          ·
            refine ⟨87655912079152038958764485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58437274719434692639176323 87655912079152038958764485)
            ·
              refine ⟨16435483514841007304768341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 87655912079152038958764485 16435483514841007304768341)
              ·
                refine ⟨96301661219771527176377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 16435483514841007304768341 96301661219771527176377)
                ·
                  rfl

theorem cell23_5063764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 9].length) (baseStart_5063764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5063764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5063764 prefixEnd_5063764 := by exact prefixLift 5063764
  have htrace : WordTrace (prefixWord ++ tailWord_5063764) baseStart_5063764 baseEnd_5063764 := by
    simpa [prefixWord, tailWord_5063764, baseEnd_5063764] using wordTrace_append hprefix tailTrace_5063764
  have hstable : (prefixWord ++ tailWord_5063764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5063764).length < 2 ^ (prefixWord ++ tailWord_5063764).sum := by decide
  have hdescent : baseEnd_5063764 < baseStart_5063764 := by decide
  rcases family_descends (prefixWord ++ tailWord_5063764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5063775 : List Nat := [1, 1, 2, 3, 1, 1, 4, 5, 1, 2, 2]
def baseStart_5063775 : Nat := 118140960795 + 5063775 * 2 ^ 59
def prefixEnd_5063775 : Nat := 4983230072969 + 3 ^ 40 * 5063775 * 2
def baseEnd_5063775 : Nat := 2600150501221030690724629

theorem tailTrace_5063775 : CollatzResearch.WordTrace tailWord_5063775 prefixEnd_5063775 2600150501221030690724629 := by
  unfold tailWord_5063775
  simp only [CollatzResearch.WordTrace]
  refine ⟨184691047229815473762960779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123127364819876982508640519 184691047229815473762960779)
  ·
    refine ⟨277036570844723210644441169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184691047229815473762960779 277036570844723210644441169)
    ·
      refine ⟨207777428133542407983330877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 277036570844723210644441169 207777428133542407983330877)
      ·
        refine ⟨77916535550078402993749079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 207777428133542407983330877 77916535550078402993749079)
        ·
          refine ⟨116874803325117604490623619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77916535550078402993749079 116874803325117604490623619)
          ·
            refine ⟨175312204987676406735935429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116874803325117604490623619 175312204987676406735935429)
            ·
              refine ⟨32871038435189326262987893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 175312204987676406735935429 32871038435189326262987893)
              ·
                refine ⟨3081659853298999337155115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32871038435189326262987893 3081659853298999337155115)
                ·
                  refine ⟨4622489779948499005732673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3081659853298999337155115 4622489779948499005732673)
                  ·
                    refine ⟨3466867334961374254299505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4622489779948499005732673 3466867334961374254299505)
                    ·
                      refine ⟨2600150501221030690724629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3466867334961374254299505 2600150501221030690724629)
                      ·
                        rfl

theorem cell23_5063775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 5, 1, 2, 2].length) (baseStart_5063775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5063775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5063775 prefixEnd_5063775 := by exact prefixLift 5063775
  have htrace : WordTrace (prefixWord ++ tailWord_5063775) baseStart_5063775 baseEnd_5063775 := by
    simpa [prefixWord, tailWord_5063775, baseEnd_5063775] using wordTrace_append hprefix tailTrace_5063775
  have hstable : (prefixWord ++ tailWord_5063775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5063775).length < 2 ^ (prefixWord ++ tailWord_5063775).sum := by decide
  have hdescent : baseEnd_5063775 < baseStart_5063775 := by decide
  rcases family_descends (prefixWord ++ tailWord_5063775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5063778 : List Nat := [3, 3, 2, 2, 1, 1, 3, 1, 1, 1, 5]
def baseStart_5063778 : Nat := 118140960795 + 5063778 * 2 ^ 59
def prefixEnd_5063778 : Nat := 4983230072969 + 3 ^ 40 * 5063778 * 2
def baseEnd_5063778 : Nat := 2600152041662994178987115

theorem tailTrace_5063778 : CollatzResearch.WordTrace tailWord_5063778 prefixEnd_5063778 2600152041662994178987115 := by
  unfold tailWord_5063778
  simp only [CollatzResearch.WordTrace]
  refine ⟨46172789162201151318829997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123127437765869736850213325 46172789162201151318829997)
  ·
    refine ⟨17314795935825431744561249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46172789162201151318829997 17314795935825431744561249)
    ·
      refine ⟨12986096951869073808420937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17314795935825431744561249 12986096951869073808420937)
      ·
        refine ⟨9739572713901805356315703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12986096951869073808420937 9739572713901805356315703)
        ·
          refine ⟨14609359070852708034473555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9739572713901805356315703 14609359070852708034473555)
          ·
            refine ⟨21914038606279062051710333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14609359070852708034473555 21914038606279062051710333)
            ·
              refine ⟨8217764477354648269391375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21914038606279062051710333 8217764477354648269391375)
              ·
                refine ⟨12326646716031972404087063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8217764477354648269391375 12326646716031972404087063)
                ·
                  refine ⟨18489970074047958606130595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12326646716031972404087063 18489970074047958606130595)
                  ·
                    refine ⟨27734955111071937909195893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18489970074047958606130595 27734955111071937909195893)
                    ·
                      refine ⟨2600152041662994178987115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27734955111071937909195893 2600152041662994178987115)
                      ·
                        rfl

theorem cell23_5063778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 3, 1, 1, 1, 5].length) (baseStart_5063778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5063778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5063778 prefixEnd_5063778 := by exact prefixLift 5063778
  have htrace : WordTrace (prefixWord ++ tailWord_5063778) baseStart_5063778 baseEnd_5063778 := by
    simpa [prefixWord, tailWord_5063778, baseEnd_5063778] using wordTrace_append hprefix tailTrace_5063778
  have hstable : (prefixWord ++ tailWord_5063778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5063778).length < 2 ^ (prefixWord ++ tailWord_5063778).sum := by decide
  have hdescent : baseEnd_5063778 < baseStart_5063778 := by decide
  rcases family_descends (prefixWord ++ tailWord_5063778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5063794 : List Nat := [3, 2, 1, 2, 2, 1, 1, 1, 1, 9]
def baseStart_5063794 : Nat := 118140960795 + 5063794 * 2 ^ 59
def prefixEnd_5063794 : Nat := 4983230072969 + 3 ^ 40 * 5063794 * 2
def baseEnd_5063794 : Nat := 866720085784488705462347

theorem tailTrace_5063794 : CollatzResearch.WordTrace tailWord_5063794 prefixEnd_5063794 866720085784488705462347 := by
  unfold tailWord_5063794
  simp only [CollatzResearch.WordTrace]
  refine ⟨46172935054186660001975609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123127826811164426671934957 46172935054186660001975609)
  ·
    refine ⟨34629701290639995001481707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46172935054186660001975609 34629701290639995001481707)
    ·
      refine ⟨51944551935959992502222561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34629701290639995001481707 51944551935959992502222561)
      ·
        refine ⟨38958413951969994376666921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51944551935959992502222561 38958413951969994376666921)
        ·
          refine ⟨29218810463977495782500191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38958413951969994376666921 29218810463977495782500191)
          ·
            refine ⟨43828215695966243673750287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29218810463977495782500191 43828215695966243673750287)
            ·
              refine ⟨65742323543949365510625431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43828215695966243673750287 65742323543949365510625431)
              ·
                refine ⟨98613485315924048265938147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65742323543949365510625431 98613485315924048265938147)
                ·
                  refine ⟨147920227973886072398907221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 98613485315924048265938147 147920227973886072398907221)
                  ·
                    refine ⟨866720085784488705462347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 147920227973886072398907221 866720085784488705462347)
                    ·
                      rfl

theorem cell23_5063794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 1, 1, 9].length) (baseStart_5063794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5063794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5063794 prefixEnd_5063794 := by exact prefixLift 5063794
  have htrace : WordTrace (prefixWord ++ tailWord_5063794) baseStart_5063794 baseEnd_5063794 := by
    simpa [prefixWord, tailWord_5063794, baseEnd_5063794] using wordTrace_append hprefix tailTrace_5063794
  have hstable : (prefixWord ++ tailWord_5063794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5063794).length < 2 ^ (prefixWord ++ tailWord_5063794).sum := by decide
  have hdescent : baseEnd_5063794 < baseStart_5063794 := by decide
  rcases family_descends (prefixWord ++ tailWord_5063794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5063808 : List Nat := [2, 1, 1, 2, 1, 3, 4, 3, 2, 1, 3]
def baseStart_5063808 : Nat := 118140960795 + 5063808 * 2 ^ 59
def prefixEnd_5063808 : Nat := 4983230072969 + 3 ^ 40 * 5063808 * 2
def baseEnd_5063808 : Nat := 2600167446082629061611977

theorem tailTrace_5063808 : CollatzResearch.WordTrace tailWord_5063808 prefixEnd_5063808 2600167446082629061611977 := by
  unfold tailWord_5063808
  simp only [CollatzResearch.WordTrace]
  refine ⟨92346125419347960199456039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123128167225797280265941385 92346125419347960199456039)
  ·
    refine ⟨138519188129021940299184059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92346125419347960199456039 138519188129021940299184059)
    ·
      refine ⟨207778782193532910448776089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138519188129021940299184059 207778782193532910448776089)
      ·
        refine ⟨155834086645149682836582067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 207778782193532910448776089 155834086645149682836582067)
        ·
          refine ⟨233751129967724524254873101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155834086645149682836582067 233751129967724524254873101)
          ·
            refine ⟨87656673737896696595577413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 233751129967724524254873101 87656673737896696595577413)
            ·
              refine ⟨16435626325855630611670765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 87656673737896696595577413 16435626325855630611670765)
              ·
                refine ⟨6163359872195861479376537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16435626325855630611670765 6163359872195861479376537)
                ·
                  refine ⟨4622519904146896109532403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6163359872195861479376537 4622519904146896109532403)
                  ·
                    refine ⟨6933779856220344164298605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4622519904146896109532403 6933779856220344164298605)
                    ·
                      refine ⟨2600167446082629061611977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6933779856220344164298605 2600167446082629061611977)
                      ·
                        rfl

theorem cell23_5063808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 3, 2, 1, 3].length) (baseStart_5063808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5063808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5063808 prefixEnd_5063808 := by exact prefixLift 5063808
  have htrace : WordTrace (prefixWord ++ tailWord_5063808) baseStart_5063808 baseEnd_5063808 := by
    simpa [prefixWord, tailWord_5063808, baseEnd_5063808] using wordTrace_append hprefix tailTrace_5063808
  have hstable : (prefixWord ++ tailWord_5063808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5063808).length < 2 ^ (prefixWord ++ tailWord_5063808).sum := by decide
  have hdescent : baseEnd_5063808 < baseStart_5063808 := by decide
  rcases family_descends (prefixWord ++ tailWord_5063808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5063818 : List Nat := [3, 1, 2, 3, 1, 1, 1, 3, 3, 3, 2]
def baseStart_5063818 : Nat := 118140960795 + 5063818 * 2 ^ 59
def prefixEnd_5063818 : Nat := 4983230072969 + 3 ^ 40 * 5063818 * 2
def baseEnd_5063818 : Nat := 2600172580889174022486931

theorem tailTrace_5063818 : CollatzResearch.WordTrace tailWord_5063818 prefixEnd_5063818 2600172580889174022486931 := by
  unfold tailWord_5063818
  simp only [CollatzResearch.WordTrace]
  refine ⟨46173153892164923026694027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123128410379106461404517405 46173153892164923026694027)
  ·
    refine ⟨69259730838247384540041041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46173153892164923026694027 69259730838247384540041041)
    ·
      refine ⟨51944798128685538405030781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69259730838247384540041041 51944798128685538405030781)
      ·
        refine ⟨19479299298257076901886543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51944798128685538405030781 19479299298257076901886543)
        ·
          refine ⟨29218948947385615352829815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19479299298257076901886543 29218948947385615352829815)
          ·
            refine ⟨43828423421078423029244723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29218948947385615352829815 43828423421078423029244723)
            ·
              refine ⟨65742635131617634543867085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43828423421078423029244723 65742635131617634543867085)
              ·
                refine ⟨24653488174356612953950157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 65742635131617634543867085 24653488174356612953950157)
                ·
                  refine ⟨9245058065383729857731309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24653488174356612953950157 9245058065383729857731309)
                  ·
                    refine ⟨3466896774518898696649241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9245058065383729857731309 3466896774518898696649241)
                    ·
                      refine ⟨2600172580889174022486931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3466896774518898696649241 2600172580889174022486931)
                      ·
                        rfl

theorem cell23_5063818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 3, 3, 3, 2].length) (baseStart_5063818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5063818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5063818 prefixEnd_5063818 := by exact prefixLift 5063818
  have htrace : WordTrace (prefixWord ++ tailWord_5063818) baseStart_5063818 baseEnd_5063818 := by
    simpa [prefixWord, tailWord_5063818, baseEnd_5063818] using wordTrace_append hprefix tailTrace_5063818
  have hstable : (prefixWord ++ tailWord_5063818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5063818).length < 2 ^ (prefixWord ++ tailWord_5063818).sum := by decide
  have hdescent : baseEnd_5063818 < baseStart_5063818 := by decide
  rcases family_descends (prefixWord ++ tailWord_5063818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5063865 : List Nat := [1, 2, 1, 4, 1, 5, 1, 1, 1, 4, 2]
def baseStart_5063865 : Nat := 118140960795 + 5063865 * 2 ^ 59
def prefixEnd_5063865 : Nat := 4983230072969 + 3 ^ 40 * 5063865 * 2
def baseEnd_5063865 : Nat := 2600196714479935338599215

theorem tailTrace_5063865 : CollatzResearch.WordTrace tailWord_5063865 prefixEnd_5063865 2600196714479935338599215 := by
  unfold tailWord_5063865
  simp only [CollatzResearch.WordTrace]
  refine ⟨184694329799489419133737049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123129553199659612755824699 184694329799489419133737049)
  ·
    refine ⟨138520747349617064350302787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184694329799489419133737049 138520747349617064350302787)
    ·
      refine ⟨207781121024425596525454181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138520747349617064350302787 207781121024425596525454181)
      ·
        refine ⟨38958960192079799348522659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 207781121024425596525454181 38958960192079799348522659)
        ·
          refine ⟨58438440288119699022783989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38958960192079799348522659 58438440288119699022783989)
          ·
            refine ⟨5478603777011221783385999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 58438440288119699022783989 5478603777011221783385999)
            ·
              refine ⟨8217905665516832675078999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5478603777011221783385999 8217905665516832675078999)
              ·
                refine ⟨12326858498275249012618499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8217905665516832675078999 12326858498275249012618499)
                ·
                  refine ⟨18490287747412873518927749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12326858498275249012618499 18490287747412873518927749)
                  ·
                    refine ⟨3466928952639913784798953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18490287747412873518927749 3466928952639913784798953)
                    ·
                      refine ⟨2600196714479935338599215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3466928952639913784798953 2600196714479935338599215)
                      ·
                        rfl

theorem cell23_5063865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 1, 1, 1, 4, 2].length) (baseStart_5063865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5063865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5063865 prefixEnd_5063865 := by exact prefixLift 5063865
  have htrace : WordTrace (prefixWord ++ tailWord_5063865) baseStart_5063865 baseEnd_5063865 := by
    simpa [prefixWord, tailWord_5063865, baseEnd_5063865] using wordTrace_append hprefix tailTrace_5063865
  have hstable : (prefixWord ++ tailWord_5063865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5063865).length < 2 ^ (prefixWord ++ tailWord_5063865).sum := by decide
  have hdescent : baseEnd_5063865 < baseStart_5063865 := by decide
  rcases family_descends (prefixWord ++ tailWord_5063865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5063905 : List Nat := [1, 2, 3, 1, 3, 3, 3, 2, 5]
def baseStart_5063905 : Nat := 118140960795 + 5063905 * 2 ^ 59
def prefixEnd_5063905 : Nat := 4983230072969 + 3 ^ 40 * 5063905 * 2
def baseEnd_5063905 : Nat := 288913028189568353566559

theorem tailTrace_5063905 : CollatzResearch.WordTrace tailWord_5063905 prefixEnd_5063905 288913028189568353566559 := by
  unfold tailWord_5063905
  simp only [CollatzResearch.WordTrace]
  refine ⟨184695788719344505965193169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123130525812896337310128779 184695788719344505965193169)
  ·
    refine ⟨138521841539508379473894877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184695788719344505965193169 138521841539508379473894877)
    ·
      refine ⟨51945690577315642302710579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 138521841539508379473894877 51945690577315642302710579)
      ·
        refine ⟨77918535865973463454065869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51945690577315642302710579 77918535865973463454065869)
        ·
          refine ⟨29219450949740048795274701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77918535865973463454065869 29219450949740048795274701)
          ·
            refine ⟨10957294106152518298228013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29219450949740048795274701 10957294106152518298228013)
            ·
              refine ⟨4108985289807194361835505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10957294106152518298228013 4108985289807194361835505)
              ·
                refine ⟨3081738967355395771376629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4108985289807194361835505 3081738967355395771376629)
                ·
                  refine ⟨288913028189568353566559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3081738967355395771376629 288913028189568353566559)
                  ·
                    rfl

theorem cell23_5063905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 3, 2, 5].length) (baseStart_5063905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5063905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5063905 prefixEnd_5063905 := by exact prefixLift 5063905
  have htrace : WordTrace (prefixWord ++ tailWord_5063905) baseStart_5063905 baseEnd_5063905 := by
    simpa [prefixWord, tailWord_5063905, baseEnd_5063905] using wordTrace_append hprefix tailTrace_5063905
  have hstable : (prefixWord ++ tailWord_5063905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5063905).length < 2 ^ (prefixWord ++ tailWord_5063905).sum := by decide
  have hdescent : baseEnd_5063905 < baseStart_5063905 := by decide
  rcases family_descends (prefixWord ++ tailWord_5063905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5063921 : List Nat := [1, 2, 2, 2, 2, 1, 1, 1, 6, 1, 4]
def baseStart_5063921 : Nat := 118140960795 + 5063921 * 2 ^ 59
def prefixEnd_5063921 : Nat := 4983230072969 + 3 ^ 40 * 5063921 * 2
def baseEnd_5063921 : Nat := 2600225469396587119498957

theorem tailTrace_5063921 : CollatzResearch.WordTrace tailWord_5063921 prefixEnd_5063921 2600225469396587119498957 := by
  unfold tailWord_5063921
  simp only [CollatzResearch.WordTrace]
  refine ⟨184696372287286540697775617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123130914858191027131850411 184696372287286540697775617)
  ·
    refine ⟨138522279215464905523331713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184696372287286540697775617 138522279215464905523331713)
    ·
      refine ⟨103891709411598679142498785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138522279215464905523331713 103891709411598679142498785)
      ·
        refine ⟨77918782058699009356874089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103891709411598679142498785 77918782058699009356874089)
        ·
          refine ⟨58439086544024257017655567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77918782058699009356874089 58439086544024257017655567)
          ·
            refine ⟨87658629816036385526483351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58439086544024257017655567 87658629816036385526483351)
            ·
              refine ⟨131487944724054578289725027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87658629816036385526483351 131487944724054578289725027)
              ·
                refine ⟨197231917086081867434587541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 131487944724054578289725027 197231917086081867434587541)
                ·
                  refine ⟨9245246113410087535996291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 197231917086081867434587541 9245246113410087535996291)
                  ·
                    refine ⟨13867869170115131303994437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9245246113410087535996291 13867869170115131303994437)
                    ·
                      refine ⟨2600225469396587119498957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13867869170115131303994437 2600225469396587119498957)
                      ·
                        rfl

theorem cell23_5063921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 6, 1, 4].length) (baseStart_5063921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5063921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5063921 prefixEnd_5063921 := by exact prefixLift 5063921
  have htrace : WordTrace (prefixWord ++ tailWord_5063921) baseStart_5063921 baseEnd_5063921 := by
    simpa [prefixWord, tailWord_5063921, baseEnd_5063921] using wordTrace_append hprefix tailTrace_5063921
  have hstable : (prefixWord ++ tailWord_5063921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5063921).length < 2 ^ (prefixWord ++ tailWord_5063921).sum := by decide
  have hdescent : baseEnd_5063921 < baseStart_5063921 := by decide
  rcases family_descends (prefixWord ++ tailWord_5063921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5064042 : List Nat := [3, 1, 3, 3, 2, 1, 2, 2, 1, 5]
def baseStart_5064042 : Nat := 118140960795 + 5064042 * 2 ^ 59
def prefixEnd_5064042 : Nat := 4983230072969 + 3 ^ 40 * 5064042 * 2
def baseEnd_5064042 : Nat := 866762533518593715361967

theorem tailTrace_5064042 : CollatzResearch.WordTrace tailWord_5064042 prefixEnd_5064042 866762533518593715361967 := by
  unfold tailWord_5064042
  simp only [CollatzResearch.WordTrace]
  refine ⟨46175196379962044590732595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123133857013232118908620253 46175196379962044590732595)
  ·
    refine ⟨69262794569943066886098893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46175196379962044590732595 69262794569943066886098893)
    ·
      refine ⟨25973547963728650082287085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69262794569943066886098893 25973547963728650082287085)
      ·
        refine ⟨9740080486398243780857657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25973547963728650082287085 9740080486398243780857657)
        ·
          refine ⟨7305060364798682835643243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9740080486398243780857657 7305060364798682835643243)
          ·
            refine ⟨10957590547198024253464865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7305060364798682835643243 10957590547198024253464865)
            ·
              refine ⟨8218192910398518190098649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10957590547198024253464865 8218192910398518190098649)
              ·
                refine ⟨6163644682798888642573987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8218192910398518190098649 6163644682798888642573987)
                ·
                  refine ⟨9245467024198332963860981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6163644682798888642573987 9245467024198332963860981)
                  ·
                    refine ⟨866762533518593715361967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9245467024198332963860981 866762533518593715361967)
                    ·
                      rfl

theorem cell23_5064042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 2, 2, 1, 5].length) (baseStart_5064042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5064042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5064042 prefixEnd_5064042 := by exact prefixLift 5064042
  have htrace : WordTrace (prefixWord ++ tailWord_5064042) baseStart_5064042 baseEnd_5064042 := by
    simpa [prefixWord, tailWord_5064042, baseEnd_5064042] using wordTrace_append hprefix tailTrace_5064042
  have hstable : (prefixWord ++ tailWord_5064042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5064042).length < 2 ^ (prefixWord ++ tailWord_5064042).sum := by decide
  have hdescent : baseEnd_5064042 < baseStart_5064042 := by decide
  rcases family_descends (prefixWord ++ tailWord_5064042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5064045 : List Nat := [1, 5, 1, 1, 1, 3, 1, 4, 1, 1, 4]
def baseStart_5064045 : Nat := 118140960795 + 5064045 * 2 ^ 59
def prefixEnd_5064045 : Nat := 4983230072969 + 3 ^ 40 * 5064045 * 2
def baseEnd_5064045 : Nat := 2600289140997744634348387

theorem tailTrace_5064045 : CollatzResearch.WordTrace tailWord_5064045 prefixEnd_5064045 2600289140997744634348387 := by
  unfold tailWord_5064045
  simp only [CollatzResearch.WordTrace]
  refine ⟨184700894938837309875289589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123133929959224873250193059 184700894938837309875289589)
  ·
    refine ⟨17315708900515997800808399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 184700894938837309875289589 17315708900515997800808399)
    ·
      refine ⟨25973563350773996701212599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17315708900515997800808399 25973563350773996701212599)
      ·
        refine ⟨38960345026160995051818899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25973563350773996701212599 38960345026160995051818899)
        ·
          refine ⟨58440517539241492577728349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38960345026160995051818899 58440517539241492577728349)
          ·
            refine ⟨21915194077215559716648131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58440517539241492577728349 21915194077215559716648131)
            ·
              refine ⟨32872791115823339574972197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21915194077215559716648131 32872791115823339574972197)
              ·
                refine ⟨6163648334216876170307287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32872791115823339574972197 6163648334216876170307287)
                ·
                  refine ⟨9245472501325314255460931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6163648334216876170307287 9245472501325314255460931)
                  ·
                    refine ⟨13868208751987971383191397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9245472501325314255460931 13868208751987971383191397)
                    ·
                      refine ⟨2600289140997744634348387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13868208751987971383191397 2600289140997744634348387)
                      ·
                        rfl

theorem cell23_5064045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 4, 1, 1, 4].length) (baseStart_5064045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5064045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5064045 prefixEnd_5064045 := by exact prefixLift 5064045
  have htrace : WordTrace (prefixWord ++ tailWord_5064045) baseStart_5064045 baseEnd_5064045 := by
    simpa [prefixWord, tailWord_5064045, baseEnd_5064045] using wordTrace_append hprefix tailTrace_5064045
  have hstable : (prefixWord ++ tailWord_5064045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5064045).length < 2 ^ (prefixWord ++ tailWord_5064045).sum := by decide
  have hdescent : baseEnd_5064045 < baseStart_5064045 := by decide
  rcases family_descends (prefixWord ++ tailWord_5064045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5064068 : List Nat := [2, 3, 2, 1, 1, 5, 9]
def baseStart_5064068 : Nat := 118140960795 + 5064068 * 2 ^ 59
def prefixEnd_5064068 : Nat := 4983230072969 + 3 ^ 40 * 5064068 * 2
def baseEnd_5064068 : Nat := 32102480877195037584701

theorem tailTrace_5064068 : CollatzResearch.WordTrace tailWord_5064068 prefixEnd_5064068 32102480877195037584701 := by
  unfold tailWord_5064068
  simp only [CollatzResearch.WordTrace]
  refine ⟨92350866908876992401688429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123134489211835989868917905 92350866908876992401688429)
  ·
    refine ⟨34631575090828872150633161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92350866908876992401688429 34631575090828872150633161)
    ·
      refine ⟨25973681318121654112974871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34631575090828872150633161 25973681318121654112974871)
      ·
        refine ⟨38960521977182481169462307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25973681318121654112974871 38960521977182481169462307)
        ·
          refine ⟨58440782965773721754193461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38960521977182481169462307 58440782965773721754193461)
          ·
            refine ⟨5478823403041286414455637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 58440782965773721754193461 5478823403041286414455637)
            ·
              refine ⟨32102480877195037584701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5478823403041286414455637 32102480877195037584701)
              ·
                rfl

theorem cell23_5064068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 9].length) (baseStart_5064068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5064068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5064068 prefixEnd_5064068 := by exact prefixLift 5064068
  have htrace : WordTrace (prefixWord ++ tailWord_5064068) baseStart_5064068 baseEnd_5064068 := by
    simpa [prefixWord, tailWord_5064068, baseEnd_5064068] using wordTrace_append hprefix tailTrace_5064068
  have hstable : (prefixWord ++ tailWord_5064068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5064068).length < 2 ^ (prefixWord ++ tailWord_5064068).sum := by decide
  have hdescent : baseEnd_5064068 < baseStart_5064068 := by decide
  rcases family_descends (prefixWord ++ tailWord_5064068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5064081 : List Nat := [1, 2, 2, 1, 1, 1, 2, 3, 1, 9]
def baseStart_5064081 : Nat := 118140960795 + 5064081 * 2 ^ 59
def prefixEnd_5064081 : Nat := 4983230072969 + 3 ^ 40 * 5064081 * 2
def baseEnd_5064081 : Nat := 866769208767102164499407

theorem tailTrace_5064081 : CollatzResearch.WordTrace tailWord_5064081 prefixEnd_5064081 866769208767102164499407 := by
  unfold tailWord_5064081
  simp only [CollatzResearch.WordTrace]
  refine ⟨184702207966706888023600097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123134805311137925349066731 184702207966706888023600097)
  ·
    refine ⟨138526655975030166017700073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184702207966706888023600097 138526655975030166017700073)
    ·
      refine ⟨103894991981272624513275055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138526655975030166017700073 103894991981272624513275055)
      ·
        refine ⟨155842487971908936769912583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103894991981272624513275055 155842487971908936769912583)
        ·
          refine ⟨233763731957863405154868875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155842487971908936769912583 233763731957863405154868875)
          ·
            refine ⟨350645597936795107732303313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 233763731957863405154868875 350645597936795107732303313)
            ·
              refine ⟨262984198452596330799227485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 350645597936795107732303313 262984198452596330799227485)
              ·
                refine ⟨98619074419723624049710307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 262984198452596330799227485 98619074419723624049710307)
                ·
                  refine ⟨147928611629585436074565461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 98619074419723624049710307 147928611629585436074565461)
                  ·
                    refine ⟨866769208767102164499407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 147928611629585436074565461 866769208767102164499407)
                    ·
                      rfl

theorem cell23_5064081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 9].length) (baseStart_5064081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5064081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5064081 prefixEnd_5064081 := by exact prefixLift 5064081
  have htrace : WordTrace (prefixWord ++ tailWord_5064081) baseStart_5064081 baseEnd_5064081 := by
    simpa [prefixWord, tailWord_5064081, baseEnd_5064081] using wordTrace_append hprefix tailTrace_5064081
  have hstable : (prefixWord ++ tailWord_5064081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5064081).length < 2 ^ (prefixWord ++ tailWord_5064081).sum := by decide
  have hdescent : baseEnd_5064081 < baseStart_5064081 := by decide
  rcases family_descends (prefixWord ++ tailWord_5064081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5064135 : List Nat := [1, 1, 4, 1, 1, 3, 1, 2, 3, 4, 2]
def baseStart_5064135 : Nat := 118140960795 + 5064135 * 2 ^ 59
def prefixEnd_5064135 : Nat := 4983230072969 + 3 ^ 40 * 5064135 * 2
def baseEnd_5064135 : Nat := 2600335354256649282222973

theorem tailTrace_5064135 : CollatzResearch.WordTrace tailWord_5064135 prefixEnd_5064135 2600335354256649282222973 := by
  unfold tailWord_5064135
  simp only [CollatzResearch.WordTrace]
  refine ⟨184704177508511255246065859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123136118339007503497377239 184704177508511255246065859)
  ·
    refine ⟨277056266262766882869098789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184704177508511255246065859 277056266262766882869098789)
    ·
      refine ⟨51948049924268790537956023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 277056266262766882869098789 51948049924268790537956023)
      ·
        refine ⟨77922074886403185806934035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51948049924268790537956023 77922074886403185806934035)
        ·
          refine ⟨116883112329604778710401053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77922074886403185806934035 116883112329604778710401053)
          ·
            refine ⟨43831167123601792016400395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 116883112329604778710401053 43831167123601792016400395)
            ·
              refine ⟨65746750685402688024600593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43831167123601792016400395 65746750685402688024600593)
              ·
                refine ⟨49310063014052016018450445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65746750685402688024600593 49310063014052016018450445)
                ·
                  refine ⟨18491273630269506006918917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49310063014052016018450445 18491273630269506006918917)
                  ·
                    refine ⟨3467113805675532376297297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18491273630269506006918917 3467113805675532376297297)
                    ·
                      refine ⟨2600335354256649282222973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3467113805675532376297297 2600335354256649282222973)
                      ·
                        rfl

theorem cell23_5064135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 2, 3, 4, 2].length) (baseStart_5064135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5064135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5064135 prefixEnd_5064135 := by exact prefixLift 5064135
  have htrace : WordTrace (prefixWord ++ tailWord_5064135) baseStart_5064135 baseEnd_5064135 := by
    simpa [prefixWord, tailWord_5064135, baseEnd_5064135] using wordTrace_append hprefix tailTrace_5064135
  have hstable : (prefixWord ++ tailWord_5064135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5064135).length < 2 ^ (prefixWord ++ tailWord_5064135).sum := by decide
  have hdescent : baseEnd_5064135 < baseStart_5064135 := by decide
  rcases family_descends (prefixWord ++ tailWord_5064135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5064173 : List Nat := [1, 5, 1, 3, 2, 2, 2, 1, 1, 3, 2]
def baseStart_5064173 : Nat := 118140960795 + 5064173 * 2 ^ 59
def prefixEnd_5064173 : Nat := 4983230072969 + 3 ^ 40 * 5064173 * 2
def baseEnd_5064173 : Nat := 2600354866521520133547799

theorem tailTrace_5064173 : CollatzResearch.WordTrace tailWord_5064173 prefixEnd_5064173 2600354866521520133547799 := by
  unfold tailWord_5064173
  simp only [CollatzResearch.WordTrace]
  refine ⟨184705563482373587735949173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123137042321582391823966115 184705563482373587735949173)
  ·
    refine ⟨17316146576472523850245235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 184705563482373587735949173 17316146576472523850245235)
    ·
      refine ⟨25974219864708785775367853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17316146576472523850245235 25974219864708785775367853)
      ·
        refine ⟨9740332449265794665762945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25974219864708785775367853 9740332449265794665762945)
        ·
          refine ⟨7305249336949345999322209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9740332449265794665762945 7305249336949345999322209)
          ·
            refine ⟨5478937002712009499491657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7305249336949345999322209 5478937002712009499491657)
            ·
              refine ⟨4109202752034007124618743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5478937002712009499491657 4109202752034007124618743)
              ·
                refine ⟨6163804128051010686928115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4109202752034007124618743 6163804128051010686928115)
                ·
                  refine ⟨9245706192076516030392173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6163804128051010686928115 9245706192076516030392173)
                  ·
                    refine ⟨3467139822028693511397065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9245706192076516030392173 3467139822028693511397065)
                    ·
                      refine ⟨2600354866521520133547799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3467139822028693511397065 2600354866521520133547799)
                      ·
                        rfl

theorem cell23_5064173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 2, 1, 1, 3, 2].length) (baseStart_5064173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5064173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5064173 prefixEnd_5064173 := by exact prefixLift 5064173
  have htrace : WordTrace (prefixWord ++ tailWord_5064173) baseStart_5064173 baseEnd_5064173 := by
    simpa [prefixWord, tailWord_5064173, baseEnd_5064173] using wordTrace_append hprefix tailTrace_5064173
  have hstable : (prefixWord ++ tailWord_5064173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5064173).length < 2 ^ (prefixWord ++ tailWord_5064173).sum := by decide
  have hdescent : baseEnd_5064173 < baseStart_5064173 := by decide
  rcases family_descends (prefixWord ++ tailWord_5064173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5064175 : List Nat := [1, 1, 2, 1, 4, 1, 3, 5, 5]
def baseStart_5064175 : Nat := 118140960795 + 5064175 * 2 ^ 59
def prefixEnd_5064175 : Nat := 4983230072969 + 3 ^ 40 * 5064175 * 2
def baseEnd_5064175 : Nat := 288928432609203236191421

theorem tailTrace_5064175 : CollatzResearch.WordTrace tailWord_5064175 prefixEnd_5064175 288928432609203236191421 := by
  unfold tailWord_5064175
  simp only [CollatzResearch.WordTrace]
  refine ⟨184705636428366342077521979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123137090952244228051681319 184705636428366342077521979)
  ·
    refine ⟨277058454642549513116282969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184705636428366342077521979 277058454642549513116282969)
    ·
      refine ⟨207793840981912134837212227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 277058454642549513116282969 207793840981912134837212227)
      ·
        refine ⟨311690761472868202255818341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 207793840981912134837212227 311690761472868202255818341)
        ·
          refine ⟨58442017776162787922965939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 311690761472868202255818341 58442017776162787922965939)
          ·
            refine ⟨87663026664244181884448909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58442017776162787922965939 87663026664244181884448909)
            ·
              refine ⟨32873634999091568206668341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 87663026664244181884448909 32873634999091568206668341)
              ·
                refine ⟨3081903281164834519375157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32873634999091568206668341 3081903281164834519375157)
                ·
                  refine ⟨288928432609203236191421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3081903281164834519375157 288928432609203236191421)
                  ·
                    rfl

theorem cell23_5064175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 5, 5].length) (baseStart_5064175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5064175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5064175 prefixEnd_5064175 := by exact prefixLift 5064175
  have htrace : WordTrace (prefixWord ++ tailWord_5064175) baseStart_5064175 baseEnd_5064175 := by
    simpa [prefixWord, tailWord_5064175, baseEnd_5064175] using wordTrace_append hprefix tailTrace_5064175
  have hstable : (prefixWord ++ tailWord_5064175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5064175).length < 2 ^ (prefixWord ++ tailWord_5064175).sum := by decide
  have hdescent : baseEnd_5064175 < baseStart_5064175 := by decide
  rcases family_descends (prefixWord ++ tailWord_5064175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5064195 : List Nat := [1, 1, 1, 3, 2, 1, 2, 3, 2, 5, 2]
def baseStart_5064195 : Nat := 118140960795 + 5064195 * 2 ^ 59
def prefixEnd_5064195 : Nat := 4983230072969 + 3 ^ 40 * 5064195 * 2
def baseEnd_5064195 : Nat := 2600366163095919047472697

theorem tailTrace_5064195 : CollatzResearch.WordTrace tailWord_5064195 prefixEnd_5064195 2600366163095919047472697 := by
  unfold tailWord_5064195
  simp only [CollatzResearch.WordTrace]
  refine ⟨184706365888293885493250039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123137577258862590328833359 184706365888293885493250039)
  ·
    refine ⟨277059548832440828239875059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184706365888293885493250039 277059548832440828239875059)
    ·
      refine ⟨415589323248661242359812589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 277059548832440828239875059 415589323248661242359812589)
      ·
        refine ⟨155845996218247965884929721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 415589323248661242359812589 155845996218247965884929721)
        ·
          refine ⟨116884497163685974413697291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 155845996218247965884929721 116884497163685974413697291)
          ·
            refine ⟨175326745745528961620545937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116884497163685974413697291 175326745745528961620545937)
            ·
              refine ⟨131495059309146721215409453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 175326745745528961620545937 131495059309146721215409453)
              ·
                refine ⟨49310647240930020455778545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 131495059309146721215409453 49310647240930020455778545)
                ·
                  refine ⟨36982985430697515341833909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49310647240930020455778545 36982985430697515341833909)
                  ·
                    refine ⟨3467154884127892063296929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 36982985430697515341833909 3467154884127892063296929)
                    ·
                      refine ⟨2600366163095919047472697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3467154884127892063296929 2600366163095919047472697)
                      ·
                        rfl

theorem cell23_5064195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 3, 2, 5, 2].length) (baseStart_5064195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5064195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5064195 prefixEnd_5064195 := by exact prefixLift 5064195
  have htrace : WordTrace (prefixWord ++ tailWord_5064195) baseStart_5064195 baseEnd_5064195 := by
    simpa [prefixWord, tailWord_5064195, baseEnd_5064195] using wordTrace_append hprefix tailTrace_5064195
  have hstable : (prefixWord ++ tailWord_5064195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5064195).length < 2 ^ (prefixWord ++ tailWord_5064195).sum := by decide
  have hdescent : baseEnd_5064195 < baseStart_5064195 := by decide
  rcases family_descends (prefixWord ++ tailWord_5064195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5064218 : List Nat := [3, 1, 1, 3, 1, 1, 1, 1, 1, 10]
def baseStart_5064218 : Nat := 118140960795 + 5064218 * 2 ^ 59
def prefixEnd_5064218 : Nat := 4983230072969 + 3 ^ 40 * 5064218 * 2
def baseEnd_5064218 : Nat := 866792657716990819161697

theorem tailTrace_5064218 : CollatzResearch.WordTrace tailWord_5064218 prefixEnd_5064218 866792657716990819161697 := by
  unfold tailWord_5064218
  simp only [CollatzResearch.WordTrace]
  refine ⟨46176801191802640105334327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123138136511473706947558205 46176801191802640105334327)
  ·
    refine ⟨69265201787703960158001491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46176801191802640105334327 69265201787703960158001491)
    ·
      refine ⟨103897802681555940237002237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69265201787703960158001491 103897802681555940237002237)
      ·
        refine ⟨38961676005583477588875839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 103897802681555940237002237 38961676005583477588875839)
        ·
          refine ⟨58442514008375216383313759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38961676005583477588875839 58442514008375216383313759)
          ·
            refine ⟨87663771012562824574970639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58442514008375216383313759 87663771012562824574970639)
            ·
              refine ⟨131495656518844236862455959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87663771012562824574970639 131495656518844236862455959)
              ·
                refine ⟨197243484778266355293683939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 131495656518844236862455959 197243484778266355293683939)
                ·
                  refine ⟨295865227167399532940525909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 197243484778266355293683939 295865227167399532940525909)
                  ·
                    refine ⟨866792657716990819161697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 295865227167399532940525909 866792657716990819161697)
                    ·
                      rfl

theorem cell23_5064218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 1, 1, 10].length) (baseStart_5064218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5064218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5064218 prefixEnd_5064218 := by exact prefixLift 5064218
  have htrace : WordTrace (prefixWord ++ tailWord_5064218) baseStart_5064218 baseEnd_5064218 := by
    simpa [prefixWord, tailWord_5064218, baseEnd_5064218] using wordTrace_append hprefix tailTrace_5064218
  have hstable : (prefixWord ++ tailWord_5064218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5064218).length < 2 ^ (prefixWord ++ tailWord_5064218).sum := by decide
  have hdescent : baseEnd_5064218 < baseStart_5064218 := by decide
  rcases family_descends (prefixWord ++ tailWord_5064218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5064225 : List Nat := [1, 2, 3, 2, 2, 2, 2, 1, 1, 3, 4]
def baseStart_5064225 : Nat := 118140960795 + 5064225 * 2 ^ 59
def prefixEnd_5064225 : Nat := 4983230072969 + 3 ^ 40 * 5064225 * 2
def baseEnd_5064225 : Nat := 2600381567515553930097559

theorem tailTrace_5064225 : CollatzResearch.WordTrace tailWord_5064225 prefixEnd_5064225 2600381567515553930097559 := by
  unfold tailWord_5064225
  simp only [CollatzResearch.WordTrace]
  refine ⟨184707460078185200616842129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123138306718790133744561419 184707460078185200616842129)
  ·
    refine ⟨138530595058638900462631597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184707460078185200616842129 138530595058638900462631597)
    ·
      refine ⟨51948973146989587673486849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 138530595058638900462631597 51948973146989587673486849)
      ·
        refine ⟨38961729860242190755115137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51948973146989587673486849 38961729860242190755115137)
        ·
          refine ⟨29221297395181643066336353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38961729860242190755115137 29221297395181643066336353)
          ·
            refine ⟨21915973046386232299752265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29221297395181643066336353 21915973046386232299752265)
            ·
              refine ⟨16436979784789674224814199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21915973046386232299752265 16436979784789674224814199)
              ·
                refine ⟨24655469677184511337221299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16436979784789674224814199 24655469677184511337221299)
                ·
                  refine ⟨36983204515776767005831949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24655469677184511337221299 36983204515776767005831949)
                  ·
                    refine ⟨13868701693416287627186981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36983204515776767005831949 13868701693416287627186981)
                    ·
                      refine ⟨2600381567515553930097559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13868701693416287627186981 2600381567515553930097559)
                      ·
                        rfl

theorem cell23_5064225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 1, 1, 3, 4].length) (baseStart_5064225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5064225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5064225 prefixEnd_5064225 := by exact prefixLift 5064225
  have htrace : WordTrace (prefixWord ++ tailWord_5064225) baseStart_5064225 baseEnd_5064225 := by
    simpa [prefixWord, tailWord_5064225, baseEnd_5064225] using wordTrace_append hprefix tailTrace_5064225
  have hstable : (prefixWord ++ tailWord_5064225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5064225).length < 2 ^ (prefixWord ++ tailWord_5064225).sum := by decide
  have hdescent : baseEnd_5064225 < baseStart_5064225 := by decide
  rcases family_descends (prefixWord ++ tailWord_5064225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5064315 : List Nat := [1, 1, 1, 1, 1, 4, 3, 1, 5, 1, 4]
def baseStart_5064315 : Nat := 118140960795 + 5064315 * 2 ^ 59
def prefixEnd_5064315 : Nat := 4983230072969 + 3 ^ 40 * 5064315 * 2
def baseEnd_5064315 : Nat := 2600427780774458577972145

theorem tailTrace_5064315 : CollatzResearch.WordTrace tailWord_5064315 prefixEnd_5064315 2600427780774458577972145 := by
  unfold tailWord_5064315
  simp only [CollatzResearch.WordTrace]
  refine ⟨184710742647859145987618399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123140495098572763991745599 184710742647859145987618399)
  ·
    refine ⟨277066113971788718981427599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184710742647859145987618399 277066113971788718981427599)
    ·
      refine ⟨415599170957683078472141399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 277066113971788718981427599 415599170957683078472141399)
      ·
        refine ⟨623398756436524617708212099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 415599170957683078472141399 623398756436524617708212099)
        ·
          refine ⟨935098134654786926562318149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 623398756436524617708212099 935098134654786926562318149)
          ·
            refine ⟨175330900247772548730434653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 935098134654786926562318149 175330900247772548730434653)
            ·
              refine ⟨65749087592914705773912995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 175330900247772548730434653 65749087592914705773912995)
              ·
                refine ⟨98623631389372058660869493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65749087592914705773912995 98623631389372058660869493)
                ·
                  refine ⟨9245965442753630499456515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 98623631389372058660869493 9245965442753630499456515)
                  ·
                    refine ⟨13868948164130445749184773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9245965442753630499456515 13868948164130445749184773)
                    ·
                      refine ⟨2600427780774458577972145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13868948164130445749184773 2600427780774458577972145)
                      ·
                        rfl

theorem cell23_5064315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 1, 5, 1, 4].length) (baseStart_5064315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5064315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5064315 prefixEnd_5064315 := by exact prefixLift 5064315
  have htrace : WordTrace (prefixWord ++ tailWord_5064315) baseStart_5064315 baseEnd_5064315 := by
    simpa [prefixWord, tailWord_5064315, baseEnd_5064315] using wordTrace_append hprefix tailTrace_5064315
  have hstable : (prefixWord ++ tailWord_5064315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5064315).length < 2 ^ (prefixWord ++ tailWord_5064315).sum := by decide
  have hdescent : baseEnd_5064315 < baseStart_5064315 := by decide
  rcases family_descends (prefixWord ++ tailWord_5064315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5064332 : List Nat := [2, 2, 1, 2, 1, 1, 4, 4, 1, 1, 4]
def baseStart_5064332 : Nat := 118140960795 + 5064332 * 2 ^ 59
def prefixEnd_5064332 : Nat := 4983230072969 + 3 ^ 40 * 5064332 * 2
def baseEnd_5064332 : Nat := 2600436509945585011459567

theorem tailTrace_5064332 : CollatzResearch.WordTrace tailWord_5064332 prefixEnd_5064332 2600436509945585011459567 := by
  unfold tailWord_5064332
  simp only [CollatzResearch.WordTrace]
  refine ⟨92355681344398778945493625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123140908459198371927324833 92355681344398778945493625)
  ·
    refine ⟨69266761008299084209120219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92355681344398778945493625 69266761008299084209120219)
    ·
      refine ⟨103900141512448626313680329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69266761008299084209120219 103900141512448626313680329)
      ·
        refine ⟨77925106134336469735260247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103900141512448626313680329 77925106134336469735260247)
        ·
          refine ⟨116887659201504704602890371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77925106134336469735260247 116887659201504704602890371)
          ·
            refine ⟨175331488802257056904335557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116887659201504704602890371 175331488802257056904335557)
            ·
              refine ⟨32874654150423198169562917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 175331488802257056904335557 32874654150423198169562917)
              ·
                refine ⟨6163997653204349656793047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32874654150423198169562917 6163997653204349656793047)
                ·
                  refine ⟨9245996479806524485189571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6163997653204349656793047 9245996479806524485189571)
                  ·
                    refine ⟨13868994719709786727784357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9245996479806524485189571 13868994719709786727784357)
                    ·
                      refine ⟨2600436509945585011459567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13868994719709786727784357 2600436509945585011459567)
                      ·
                        rfl

theorem cell23_5064332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 4, 1, 1, 4].length) (baseStart_5064332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5064332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5064332 prefixEnd_5064332 := by exact prefixLift 5064332
  have htrace : WordTrace (prefixWord ++ tailWord_5064332) baseStart_5064332 baseEnd_5064332 := by
    simpa [prefixWord, tailWord_5064332, baseEnd_5064332] using wordTrace_append hprefix tailTrace_5064332
  have hstable : (prefixWord ++ tailWord_5064332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5064332).length < 2 ^ (prefixWord ++ tailWord_5064332).sum := by decide
  have hdescent : baseEnd_5064332 < baseStart_5064332 := by decide
  rcases family_descends (prefixWord ++ tailWord_5064332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5064345 : List Nat := [1, 2, 1, 2, 1, 2, 2, 3, 3, 2, 4]
def baseStart_5064345 : Nat := 118140960795 + 5064345 * 2 ^ 59
def prefixEnd_5064345 : Nat := 4983230072969 + 3 ^ 40 * 5064345 * 2
def baseEnd_5064345 : Nat := 2600443185194093460597007

theorem tailTrace_5064345 : CollatzResearch.WordTrace tailWord_5064345 prefixEnd_5064345 2600443185194093460597007 := by
  unfold tailWord_5064345
  simp only [CollatzResearch.WordTrace]
  refine ⟨184711836837750461111210489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123141224558500307407473659 184711836837750461111210489)
  ·
    refine ⟨138533877628312845833407867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184711836837750461111210489 138533877628312845833407867)
    ·
      refine ⟨207800816442469268750111801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138533877628312845833407867 207800816442469268750111801)
      ·
        refine ⟨155850612331851951562583851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 207800816442469268750111801 155850612331851951562583851)
        ·
          refine ⟨233775918497777927343875777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155850612331851951562583851 233775918497777927343875777)
          ·
            refine ⟨175331938873333445507906833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 233775918497777927343875777 175331938873333445507906833)
            ·
              refine ⟨131498954155000084130930125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 175331938873333445507906833 131498954155000084130930125)
              ·
                refine ⟨49312107808125031549098797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 131498954155000084130930125 49312107808125031549098797)
                ·
                  refine ⟨18492040428046886830912049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49312107808125031549098797 18492040428046886830912049)
                  ·
                    refine ⟨13869030321035165123184037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18492040428046886830912049 13869030321035165123184037)
                    ·
                      refine ⟨2600443185194093460597007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13869030321035165123184037 2600443185194093460597007)
                      ·
                        rfl

theorem cell23_5064345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 3, 3, 2, 4].length) (baseStart_5064345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5064345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5064345 prefixEnd_5064345 := by exact prefixLift 5064345
  have htrace : WordTrace (prefixWord ++ tailWord_5064345) baseStart_5064345 baseEnd_5064345 := by
    simpa [prefixWord, tailWord_5064345, baseEnd_5064345] using wordTrace_append hprefix tailTrace_5064345
  have hstable : (prefixWord ++ tailWord_5064345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5064345).length < 2 ^ (prefixWord ++ tailWord_5064345).sum := by decide
  have hdescent : baseEnd_5064345 < baseStart_5064345 := by decide
  rcases family_descends (prefixWord ++ tailWord_5064345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5064349 : List Nat := [1, 4, 2, 1, 1, 1, 1, 1, 7, 2, 2]
def baseStart_5064349 : Nat := 118140960795 + 5064349 * 2 ^ 59
def prefixEnd_5064349 : Nat := 4983230072969 + 3 ^ 40 * 5064349 * 2
def baseEnd_5064349 : Nat := 2600445239116711444946989

theorem tailTrace_5064349 : CollatzResearch.WordTrace tailWord_5064349 prefixEnd_5064349 2600445239116711444946989 := by
  unfold tailWord_5064349
  simp only [CollatzResearch.WordTrace]
  refine ⟨184711982729735969794356101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123141321819823979862904067 184711982729735969794356101)
  ·
    refine ⟨34633496761825494336441769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 184711982729735969794356101 34633496761825494336441769)
    ·
      refine ⟨25975122571369120752331327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34633496761825494336441769 25975122571369120752331327)
      ·
        refine ⟨38962683857053681128496991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25975122571369120752331327 38962683857053681128496991)
        ·
          refine ⟨58444025785580521692745487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38962683857053681128496991 58444025785580521692745487)
          ·
            refine ⟨87666038678370782539118231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58444025785580521692745487 87666038678370782539118231)
            ·
              refine ⟨131499058017556173808677347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87666038678370782539118231 131499058017556173808677347)
              ·
                refine ⟨197248587026334260713016021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 131499058017556173808677347 197248587026334260713016021)
                ·
                  refine ⟨4623013758429709235461313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 197248587026334260713016021 4623013758429709235461313)
                  ·
                    refine ⟨3467260318822281926595985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4623013758429709235461313 3467260318822281926595985)
                    ·
                      refine ⟨2600445239116711444946989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3467260318822281926595985 2600445239116711444946989)
                      ·
                        rfl

theorem cell23_5064349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 1, 7, 2, 2].length) (baseStart_5064349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5064349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5064349 prefixEnd_5064349 := by exact prefixLift 5064349
  have htrace : WordTrace (prefixWord ++ tailWord_5064349) baseStart_5064349 baseEnd_5064349 := by
    simpa [prefixWord, tailWord_5064349, baseEnd_5064349] using wordTrace_append hprefix tailTrace_5064349
  have hstable : (prefixWord ++ tailWord_5064349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5064349).length < 2 ^ (prefixWord ++ tailWord_5064349).sum := by decide
  have hdescent : baseEnd_5064349 < baseStart_5064349 := by decide
  rcases family_descends (prefixWord ++ tailWord_5064349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5064360 : List Nat := [2, 1, 7, 1, 1, 1, 2, 1, 3, 1, 3]
def baseStart_5064360 : Nat := 118140960795 + 5064360 * 2 ^ 59
def prefixEnd_5064360 : Nat := 4983230072969 + 3 ^ 40 * 5064360 * 2
def baseEnd_5064360 : Nat := 2600450887403910901909439

theorem tailTrace_5064360 : CollatzResearch.WordTrace tailWord_5064360 prefixEnd_5064360 2600450887403910901909439 := by
  unfold tailWord_5064360
  simp only [CollatzResearch.WordTrace]
  refine ⟨92356191966348059336503267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123141589288464079115337689 92356191966348059336503267)
  ·
    refine ⟨138534287949522089004754901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92356191966348059336503267 138534287949522089004754901)
    ·
      refine ⟨3246897373816923961048943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 138534287949522089004754901 3246897373816923961048943)
      ·
        refine ⟨4870346060725385941573415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3246897373816923961048943 4870346060725385941573415)
        ·
          refine ⟨7305519091088078912360123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4870346060725385941573415 7305519091088078912360123)
          ·
            refine ⟨10958278636632118368540185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7305519091088078912360123 10958278636632118368540185)
            ·
              refine ⟨8218708977474088776405139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10958278636632118368540185 8218708977474088776405139)
              ·
                refine ⟨12328063466211133164607709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8218708977474088776405139 12328063466211133164607709)
                ·
                  refine ⟨4623023799829174936727891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12328063466211133164607709 4623023799829174936727891)
                  ·
                    refine ⟨6934535699743762405091837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4623023799829174936727891 6934535699743762405091837)
                    ·
                      refine ⟨2600450887403910901909439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6934535699743762405091837 2600450887403910901909439)
                      ·
                        rfl

theorem cell23_5064360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_5064360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5064360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5064360 prefixEnd_5064360 := by exact prefixLift 5064360
  have htrace : WordTrace (prefixWord ++ tailWord_5064360) baseStart_5064360 baseEnd_5064360 := by
    simpa [prefixWord, tailWord_5064360, baseEnd_5064360] using wordTrace_append hprefix tailTrace_5064360
  have hstable : (prefixWord ++ tailWord_5064360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5064360).length < 2 ^ (prefixWord ++ tailWord_5064360).sum := by decide
  have hdescent : baseEnd_5064360 < baseStart_5064360 := by decide
  rcases family_descends (prefixWord ++ tailWord_5064360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5064406 : List Nat := [5, 2, 1, 3, 1, 2, 9]
def baseStart_5064406 : Nat := 118140960795 + 5064406 * 2 ^ 59
def prefixEnd_5064406 : Nat := 4983230072969 + 3 ^ 40 * 5064406 * 2
def baseEnd_5064406 : Nat := 32104623549555774344867

theorem tailTrace_5064406 : CollatzResearch.WordTrace tailWord_5064406 prefixEnd_5064406 32104623549555774344867 := by
  unfold tailWord_5064406
  simp only [CollatzResearch.WordTrace]
  refine ⟨11544628855658091783073817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 123142707793686312352787381 11544628855658091783073817)
  ·
    refine ⟨8658471641743568837305363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11544628855658091783073817 8658471641743568837305363)
    ·
      refine ⟨12987707462615353255958045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8658471641743568837305363 12987707462615353255958045)
      ·
        refine ⟨4870390298480757470984267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12987707462615353255958045 4870390298480757470984267)
        ·
          refine ⟨7305585447721136206476401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4870390298480757470984267 7305585447721136206476401)
          ·
            refine ⟨5479189085790852154857301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7305585447721136206476401 5479189085790852154857301)
            ·
              refine ⟨32104623549555774344867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5479189085790852154857301 32104623549555774344867)
              ·
                rfl

theorem cell23_5064406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 9].length) (baseStart_5064406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5064406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5064406 prefixEnd_5064406 := by exact prefixLift 5064406
  have htrace : WordTrace (prefixWord ++ tailWord_5064406) baseStart_5064406 baseEnd_5064406 := by
    simpa [prefixWord, tailWord_5064406, baseEnd_5064406] using wordTrace_append hprefix tailTrace_5064406
  have hstable : (prefixWord ++ tailWord_5064406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5064406).length < 2 ^ (prefixWord ++ tailWord_5064406).sum := by decide
  have hdescent : baseEnd_5064406 < baseStart_5064406 := by decide
  rcases family_descends (prefixWord ++ tailWord_5064406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5064425 : List Nat := [1, 2, 1, 1, 1, 2, 3, 1, 3, 3, 5]
def baseStart_5064425 : Nat := 118140960795 + 5064425 * 2 ^ 59
def prefixEnd_5064425 : Nat := 4983230072969 + 3 ^ 40 * 5064425 * 2
def baseEnd_5064425 : Nat := 2600484263646453147596639

theorem tailTrace_5064425 : CollatzResearch.WordTrace tailWord_5064425 prefixEnd_5064425 2600484263646453147596639 := by
  unfold tailWord_5064425
  simp only [CollatzResearch.WordTrace]
  refine ⟨184714754677460634774122729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123143169784973756516081819 184714754677460634774122729)
  ·
    refine ⟨138536066008095476080592047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184714754677460634774122729 138536066008095476080592047)
    ·
      refine ⟨207804099012143214120888071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138536066008095476080592047 207804099012143214120888071)
      ·
        refine ⟨311706148518214821181332107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 207804099012143214120888071 311706148518214821181332107)
        ·
          refine ⟨467559222777322231771998161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 311706148518214821181332107 467559222777322231771998161)
          ·
            refine ⟨350669417082991673828998621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 467559222777322231771998161 350669417082991673828998621)
            ·
              refine ⟨131501031406121877685874483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 350669417082991673828998621 131501031406121877685874483)
              ·
                refine ⟨197251547109182816528811725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 131501031406121877685874483 197251547109182816528811725)
                ·
                  refine ⟨73969330165943556198304397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 197251547109182816528811725 73969330165943556198304397)
                  ·
                    refine ⟨27738498812228833574364149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 73969330165943556198304397 27738498812228833574364149)
                    ·
                      refine ⟨2600484263646453147596639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27738498812228833574364149 2600484263646453147596639)
                      ·
                        rfl

theorem cell23_5064425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 1, 3, 3, 5].length) (baseStart_5064425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5064425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5064425 prefixEnd_5064425 := by exact prefixLift 5064425
  have htrace : WordTrace (prefixWord ++ tailWord_5064425) baseStart_5064425 baseEnd_5064425 := by
    simpa [prefixWord, tailWord_5064425, baseEnd_5064425] using wordTrace_append hprefix tailTrace_5064425
  have hstable : (prefixWord ++ tailWord_5064425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5064425).length < 2 ^ (prefixWord ++ tailWord_5064425).sum := by decide
  have hdescent : baseEnd_5064425 < baseStart_5064425 := by decide
  rcases family_descends (prefixWord ++ tailWord_5064425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5064433 : List Nat := [1, 2, 2, 2, 2, 5, 2, 1, 2, 1, 3]
def baseStart_5064433 : Nat := 118140960795 + 5064433 * 2 ^ 59
def prefixEnd_5064433 : Nat := 4983230072969 + 3 ^ 40 * 5064433 * 2
def baseEnd_5064433 : Nat := 2600488371491689116296603

theorem tailTrace_5064433 : CollatzResearch.WordTrace tailWord_5064433 prefixEnd_5064433 2600488371491689116296603 := by
  unfold tailWord_5064433
  simp only [CollatzResearch.WordTrace]
  refine ⟨184715046461431652140413953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123143364307621101426942635 184715046461431652140413953)
  ·
    refine ⟨138536284846073739105310465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184715046461431652140413953 138536284846073739105310465)
    ·
      refine ⟨103902213634555304328982849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138536284846073739105310465 103902213634555304328982849)
      ·
        refine ⟨77926660225916478246737137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103902213634555304328982849 77926660225916478246737137)
        ·
          refine ⟨58444995169437358685052853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77926660225916478246737137 58444995169437358685052853)
          ·
            refine ⟨5479218297134752376723705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 58444995169437358685052853 5479218297134752376723705)
            ·
              refine ⟨4109413722851064282542779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5479218297134752376723705 4109413722851064282542779)
              ·
                refine ⟨6164120584276596423814169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4109413722851064282542779 6164120584276596423814169)
                ·
                  refine ⟨4623090438207447317860627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6164120584276596423814169 4623090438207447317860627)
                  ·
                    refine ⟨6934635657311170976790941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4623090438207447317860627 6934635657311170976790941)
                    ·
                      refine ⟨2600488371491689116296603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6934635657311170976790941 2600488371491689116296603)
                      ·
                        rfl

theorem cell23_5064433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 2, 1, 2, 1, 3].length) (baseStart_5064433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5064433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5064433 prefixEnd_5064433 := by exact prefixLift 5064433
  have htrace : WordTrace (prefixWord ++ tailWord_5064433) baseStart_5064433 baseEnd_5064433 := by
    simpa [prefixWord, tailWord_5064433, baseEnd_5064433] using wordTrace_append hprefix tailTrace_5064433
  have hstable : (prefixWord ++ tailWord_5064433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5064433).length < 2 ^ (prefixWord ++ tailWord_5064433).sum := by decide
  have hdescent : baseEnd_5064433 < baseStart_5064433 := by decide
  rcases family_descends (prefixWord ++ tailWord_5064433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5064454 : List Nat := [6, 2, 2, 1, 2, 1, 1, 1, 1, 1, 5]
def baseStart_5064454 : Nat := 118140960795 + 5064454 * 2 ^ 59
def prefixEnd_5064454 : Nat := 4983230072969 + 3 ^ 40 * 5064454 * 2
def baseEnd_5064454 : Nat := 2600499154585433534134007

theorem tailTrace_5064454 : CollatzResearch.WordTrace tailWord_5064454 prefixEnd_5064454 2600499154585433534134007 := by
  unfold tailWord_5064454
  simp only [CollatzResearch.WordTrace]
  refine ⟨5772369137323611647716513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 123143874929570381817952277 5772369137323611647716513)
  ·
    refine ⟨4329276852992708735787385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5772369137323611647716513 4329276852992708735787385)
    ·
      refine ⟨3246957639744531551840539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4329276852992708735787385 3246957639744531551840539)
      ·
        refine ⟨4870436459616797327760809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3246957639744531551840539 4870436459616797327760809)
        ·
          refine ⟨3652827344712597995820607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4870436459616797327760809 3652827344712597995820607)
          ·
            refine ⟨5479241017068896993730911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3652827344712597995820607 5479241017068896993730911)
            ·
              refine ⟨8218861525603345490596367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5479241017068896993730911 8218861525603345490596367)
              ·
                refine ⟨12328292288405018235894551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8218861525603345490596367 12328292288405018235894551)
                ·
                  refine ⟨18492438432607527353841827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12328292288405018235894551 18492438432607527353841827)
                  ·
                    refine ⟨27738657648911291030762741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18492438432607527353841827 27738657648911291030762741)
                    ·
                      refine ⟨2600499154585433534134007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27738657648911291030762741 2600499154585433534134007)
                      ·
                        rfl

theorem cell23_5064454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 1, 1, 1, 1, 5].length) (baseStart_5064454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5064454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5064454 prefixEnd_5064454 := by exact prefixLift 5064454
  have htrace : WordTrace (prefixWord ++ tailWord_5064454) baseStart_5064454 baseEnd_5064454 := by
    simpa [prefixWord, tailWord_5064454, baseEnd_5064454] using wordTrace_append hprefix tailTrace_5064454
  have hstable : (prefixWord ++ tailWord_5064454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5064454).length < 2 ^ (prefixWord ++ tailWord_5064454).sum := by decide
  have hdescent : baseEnd_5064454 < baseStart_5064454 := by decide
  rcases family_descends (prefixWord ++ tailWord_5064454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5064468 : List Nat := [2, 4, 4, 1, 2, 1, 2, 2, 1, 2, 2]
def baseStart_5064468 : Nat := 118140960795 + 5064468 * 2 ^ 59
def prefixEnd_5064468 : Nat := 4983230072969 + 3 ^ 40 * 5064468 * 2
def baseEnd_5064468 : Nat := 2600506343314596479358943

theorem tailTrace_5064468 : CollatzResearch.WordTrace tailWord_5064468 prefixEnd_5064468 2600506343314596479358943 := by
  unfold tailWord_5064468
  simp only [CollatzResearch.WordTrace]
  refine ⟨92358161508152426558969029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123144215344203235411958705 92358161508152426558969029)
  ·
    refine ⟨17317155282778579979806693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 92358161508152426558969029 17317155282778579979806693)
    ·
      refine ⟨3246966615520983746213755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17317155282778579979806693 3246966615520983746213755)
      ·
        refine ⟨4870449923281475619320633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3246966615520983746213755 4870449923281475619320633)
        ·
          refine ⟨3652837442461106714490475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4870449923281475619320633 3652837442461106714490475)
          ·
            refine ⟨5479256163691660071735713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3652837442461106714490475 5479256163691660071735713)
            ·
              refine ⟨4109442122768745053801785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5479256163691660071735713 4109442122768745053801785)
              ·
                refine ⟨3082081592076558790351339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4109442122768745053801785 3082081592076558790351339)
                ·
                  refine ⟨4623122388114838185527009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3082081592076558790351339 4623122388114838185527009)
                  ·
                    refine ⟨3467341791086128639145257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4623122388114838185527009 3467341791086128639145257)
                    ·
                      refine ⟨2600506343314596479358943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3467341791086128639145257 2600506343314596479358943)
                      ·
                        rfl

theorem cell23_5064468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 2, 2, 1, 2, 2].length) (baseStart_5064468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5064468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5064468 prefixEnd_5064468 := by exact prefixLift 5064468
  have htrace : WordTrace (prefixWord ++ tailWord_5064468) baseStart_5064468 baseEnd_5064468 := by
    simpa [prefixWord, tailWord_5064468, baseEnd_5064468] using wordTrace_append hprefix tailTrace_5064468
  have hstable : (prefixWord ++ tailWord_5064468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5064468).length < 2 ^ (prefixWord ++ tailWord_5064468).sum := by decide
  have hdescent : baseEnd_5064468 < baseStart_5064468 := by decide
  rcases family_descends (prefixWord ++ tailWord_5064468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5064479 : List Nat := [1, 1, 2, 4, 2, 1, 3, 4, 5]
def baseStart_5064479 : Nat := 118140960795 + 5064479 * 2 ^ 59
def prefixEnd_5064479 : Nat := 4983230072969 + 3 ^ 40 * 5064479 * 2
def baseEnd_5064479 : Nat := 288945776844643992924599

theorem tailTrace_5064479 : CollatzResearch.WordTrace tailWord_5064479 prefixEnd_5064479 288945776844643992924599 := by
  unfold tailWord_5064479
  simp only [CollatzResearch.WordTrace]
  refine ⟨184716724219265001996588491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123144482812843334664392327 184716724219265001996588491)
  ·
    refine ⟨277075086328897502994882737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184716724219265001996588491 277075086328897502994882737)
    ·
      refine ⟨207806314746673127246162053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 277075086328897502994882737 207806314746673127246162053)
      ·
        refine ⟨38963684015001211358655385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 207806314746673127246162053 38963684015001211358655385)
        ·
          refine ⟨29222763011250908518991539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38963684015001211358655385 29222763011250908518991539)
          ·
            refine ⟨43834144516876362778487309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29222763011250908518991539 43834144516876362778487309)
            ·
              refine ⟨16437804193828636041932741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43834144516876362778487309 16437804193828636041932741)
              ·
                refine ⟨3082088286342869257862389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16437804193828636041932741 3082088286342869257862389)
                ·
                  refine ⟨288945776844643992924599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3082088286342869257862389 288945776844643992924599)
                  ·
                    rfl

theorem cell23_5064479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 4, 5].length) (baseStart_5064479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5064479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5064479 prefixEnd_5064479 := by exact prefixLift 5064479
  have htrace : WordTrace (prefixWord ++ tailWord_5064479) baseStart_5064479 baseEnd_5064479 := by
    simpa [prefixWord, tailWord_5064479, baseEnd_5064479] using wordTrace_append hprefix tailTrace_5064479
  have hstable : (prefixWord ++ tailWord_5064479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5064479).length < 2 ^ (prefixWord ++ tailWord_5064479).sum := by decide
  have hdescent : baseEnd_5064479 < baseStart_5064479 := by decide
  rcases family_descends (prefixWord ++ tailWord_5064479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5064509 : List Nat := [1, 4, 1, 4, 1, 2, 1, 1, 1, 7]
def baseStart_5064509 : Nat := 118140960795 + 5064509 * 2 ^ 59
def prefixEnd_5064509 : Nat := 4983230072969 + 3 ^ 40 * 5064509 * 2
def baseEnd_5064509 : Nat := 866842465340476939648751

theorem tailTrace_5064509 : CollatzResearch.WordTrace tailWord_5064509 prefixEnd_5064509 866842465340476939648751 := by
  unfold tailWord_5064509
  simp only [CollatzResearch.WordTrace]
  refine ⟨184717818409156317120180581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123145212272770878080120387 184717818409156317120180581)
  ·
    refine ⟨34634590951716809460033859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 184717818409156317120180581 34634590951716809460033859)
    ·
      refine ⟨51951886427575214190050789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34634590951716809460033859 51951886427575214190050789)
      ·
        refine ⟨9740978705170352660634523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51951886427575214190050789 9740978705170352660634523)
        ·
          refine ⟨14611468057755528990951785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9740978705170352660634523 14611468057755528990951785)
          ·
            refine ⟨10958601043316646743213839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14611468057755528990951785 10958601043316646743213839)
            ·
              refine ⟨16437901564974970114820759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10958601043316646743213839 16437901564974970114820759)
              ·
                refine ⟨24656852347462455172231139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16437901564974970114820759 24656852347462455172231139)
                ·
                  refine ⟨36985278521193682758346709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24656852347462455172231139 36985278521193682758346709)
                  ·
                    refine ⟨866842465340476939648751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36985278521193682758346709 866842465340476939648751)
                    ·
                      rfl

theorem cell23_5064509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 1, 1, 7].length) (baseStart_5064509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5064509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5064509 prefixEnd_5064509 := by exact prefixLift 5064509
  have htrace : WordTrace (prefixWord ++ tailWord_5064509) baseStart_5064509 baseEnd_5064509 := by
    simpa [prefixWord, tailWord_5064509, baseEnd_5064509] using wordTrace_append hprefix tailTrace_5064509
  have hstable : (prefixWord ++ tailWord_5064509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5064509).length < 2 ^ (prefixWord ++ tailWord_5064509).sum := by decide
  have hdescent : baseEnd_5064509 < baseStart_5064509 := by decide
  rcases family_descends (prefixWord ++ tailWord_5064509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5064590 : List Nat := [4, 1, 1, 5, 1, 2, 1, 1, 3, 4]
def baseStart_5064590 : Nat := 118140960795 + 5064590 * 2 ^ 59
def prefixEnd_5064590 : Nat := 4983230072969 + 3 ^ 40 * 5064590 * 2
def baseEnd_5064590 : Nat := 866856329318148334011127

theorem tailTrace_5064590 : CollatzResearch.WordTrace tailWord_5064590 prefixEnd_5064590 866856329318148334011127 := by
  unfold tailWord_5064590
  simp only [CollatzResearch.WordTrace]
  refine ⟨23090096590232858494234903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 123147181814575245302586149 23090096590232858494234903)
  ·
    refine ⟨34635144885349287741352355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23090096590232858494234903 34635144885349287741352355)
    ·
      refine ⟨51952717328023931612028533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34635144885349287741352355 51952717328023931612028533)
      ·
        refine ⟨4870567249502243588627675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 51952717328023931612028533 4870567249502243588627675)
        ·
          refine ⟨7305850874253365382941513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4870567249502243588627675 7305850874253365382941513)
          ·
            refine ⟨5479388155690024037206135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7305850874253365382941513 5479388155690024037206135)
            ·
              refine ⟨8219082233535036055809203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5479388155690024037206135 8219082233535036055809203)
              ·
                refine ⟨12328623350302554083713805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8219082233535036055809203 12328623350302554083713805)
                ·
                  refine ⟨4623233756363457781392677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12328623350302554083713805 4623233756363457781392677)
                  ·
                    refine ⟨866856329318148334011127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4623233756363457781392677 866856329318148334011127)
                    ·
                      rfl

theorem cell23_5064590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 1, 1, 3, 4].length) (baseStart_5064590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5064590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5064590 prefixEnd_5064590 := by exact prefixLift 5064590
  have htrace : WordTrace (prefixWord ++ tailWord_5064590) baseStart_5064590 baseEnd_5064590 := by
    simpa [prefixWord, tailWord_5064590, baseEnd_5064590] using wordTrace_append hprefix tailTrace_5064590
  have hstable : (prefixWord ++ tailWord_5064590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5064590).length < 2 ^ (prefixWord ++ tailWord_5064590).sum := by decide
  have hdescent : baseEnd_5064590 < baseStart_5064590 := by decide
  rcases family_descends (prefixWord ++ tailWord_5064590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5064629 : List Nat := [1, 3, 3, 2, 1, 2, 1, 1, 3, 6]
def baseStart_5064629 : Nat := 118140960795 + 5064629 * 2 ^ 59
def prefixEnd_5064629 : Nat := 4983230072969 + 3 ^ 40 * 5064629 * 2
def baseEnd_5064629 : Nat := 866863004566656783148567

theorem tailTrace_5064629 : CollatzResearch.WordTrace tailWord_5064629 prefixEnd_5064629 866863004566656783148567 := by
  unfold tailWord_5064629
  simp only [CollatzResearch.WordTrace]
  refine ⟨184722195168721577614548941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123148130112481051743032627 184722195168721577614548941)
  ·
    refine ⟨69270823188270591605455853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 184722195168721577614548941 69270823188270591605455853)
    ·
      refine ⟨25976558695601471852045945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69270823188270591605455853 25976558695601471852045945)
      ·
        refine ⟨19482419021701103889034459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25976558695601471852045945 19482419021701103889034459)
        ·
          refine ⟨29223628532551655833551689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19482419021701103889034459 29223628532551655833551689)
          ·
            refine ⟨21917721399413741875163767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29223628532551655833551689 21917721399413741875163767)
            ·
              refine ⟨32876582099120612812745651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21917721399413741875163767 32876582099120612812745651)
              ·
                refine ⟨49314873148680919219118477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32876582099120612812745651 49314873148680919219118477)
                ·
                  refine ⟨18493077430755344707169429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49314873148680919219118477 18493077430755344707169429)
                  ·
                    refine ⟨866863004566656783148567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18493077430755344707169429 866863004566656783148567)
                    ·
                      rfl

theorem cell23_5064629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 1, 3, 6].length) (baseStart_5064629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5064629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5064629 prefixEnd_5064629 := by exact prefixLift 5064629
  have htrace : WordTrace (prefixWord ++ tailWord_5064629) baseStart_5064629 baseEnd_5064629 := by
    simpa [prefixWord, tailWord_5064629, baseEnd_5064629] using wordTrace_append hprefix tailTrace_5064629
  have hstable : (prefixWord ++ tailWord_5064629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5064629).length < 2 ^ (prefixWord ++ tailWord_5064629).sum := by decide
  have hdescent : baseEnd_5064629 < baseStart_5064629 := by decide
  rcases family_descends (prefixWord ++ tailWord_5064629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5064674 : List Nat := [3, 3, 3, 1, 3, 1, 1, 1, 2, 3, 2]
def baseStart_5064674 : Nat := 118140960795 + 5064674 * 2 ^ 59
def prefixEnd_5064674 : Nat := 4983230072969 + 3 ^ 40 * 5064674 * 2
def baseEnd_5064674 : Nat := 2600612120329422673382995

theorem tailTrace_5064674 : CollatzResearch.WordTrace tailWord_5064674 prefixEnd_5064674 2600612120329422673382995 := by
  unfold tailWord_5064674
  simp only [CollatzResearch.WordTrace]
  refine ⟨46180959113389637574984269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123149224302372366866624717 46180959113389637574984269)
  ·
    refine ⟨17317859667521114090619101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46180959113389637574984269 17317859667521114090619101)
    ·
      refine ⟨6494197375320417783982163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17317859667521114090619101 6494197375320417783982163)
      ·
        refine ⟨9741296062980626675973245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6494197375320417783982163 9741296062980626675973245)
        ·
          refine ⟨3652986023617735003489967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9741296062980626675973245 3652986023617735003489967)
          ·
            refine ⟨5479479035426602505234951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3652986023617735003489967 5479479035426602505234951)
            ·
              refine ⟨8219218553139903757852427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5479479035426602505234951 8219218553139903757852427)
              ·
                refine ⟨12328827829709855636778641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8219218553139903757852427 12328827829709855636778641)
                ·
                  refine ⟨9246620872282391727583981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12328827829709855636778641 9246620872282391727583981)
                  ·
                    refine ⟨3467482827105896897843993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9246620872282391727583981 3467482827105896897843993)
                    ·
                      refine ⟨2600612120329422673382995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3467482827105896897843993 2600612120329422673382995)
                      ·
                        rfl

theorem cell23_5064674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 1, 1, 2, 3, 2].length) (baseStart_5064674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5064674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5064674 prefixEnd_5064674 := by exact prefixLift 5064674
  have htrace : WordTrace (prefixWord ++ tailWord_5064674) baseStart_5064674 baseEnd_5064674 := by
    simpa [prefixWord, tailWord_5064674, baseEnd_5064674] using wordTrace_append hprefix tailTrace_5064674
  have hstable : (prefixWord ++ tailWord_5064674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5064674).length < 2 ^ (prefixWord ++ tailWord_5064674).sum := by decide
  have hdescent : baseEnd_5064674 < baseStart_5064674 := by decide
  rcases family_descends (prefixWord ++ tailWord_5064674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5064729 : List Nat := [1, 2, 1, 2, 1, 1, 3, 4, 2, 1, 5]
def baseStart_5064729 : Nat := 118140960795 + 5064729 * 2 ^ 59
def prefixEnd_5064729 : Nat := 4983230072969 + 3 ^ 40 * 5064729 * 2
def baseEnd_5064729 : Nat := 2600640361765419958195241

theorem tailTrace_5064729 : CollatzResearch.WordTrace tailWord_5064729 prefixEnd_5064729 2600640361765419958195241 := by
  unfold tailWord_5064729
  simp only [CollatzResearch.WordTrace]
  refine ⟨184725842468359294693189241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123150561645572863128792827 184725842468359294693189241)
  ·
    refine ⟨138544381851269471019891931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184725842468359294693189241 138544381851269471019891931)
    ·
      refine ⟨207816572776904206529837897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138544381851269471019891931 207816572776904206529837897)
      ·
        refine ⟨155862429582678154897378423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 207816572776904206529837897 155862429582678154897378423)
        ·
          refine ⟨233793644374017232346067635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155862429582678154897378423 233793644374017232346067635)
          ·
            refine ⟨350690466561025848519101453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 233793644374017232346067635 350690466561025848519101453)
            ·
              refine ⟨131508924960384693194663045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 350690466561025848519101453 131508924960384693194663045)
              ·
                refine ⟨24657923430072129973999321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 131508924960384693194663045 24657923430072129973999321)
                ·
                  refine ⟨18493442572554097480499491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24657923430072129973999321 18493442572554097480499491)
                  ·
                    refine ⟨27740163858831146220749237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18493442572554097480499491 27740163858831146220749237)
                    ·
                      refine ⟨2600640361765419958195241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27740163858831146220749237 2600640361765419958195241)
                      ·
                        rfl

theorem cell23_5064729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 4, 2, 1, 5].length) (baseStart_5064729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5064729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5064729 prefixEnd_5064729 := by exact prefixLift 5064729
  have htrace : WordTrace (prefixWord ++ tailWord_5064729) baseStart_5064729 baseEnd_5064729 := by
    simpa [prefixWord, tailWord_5064729, baseEnd_5064729] using wordTrace_append hprefix tailTrace_5064729
  have hstable : (prefixWord ++ tailWord_5064729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5064729).length < 2 ^ (prefixWord ++ tailWord_5064729).sum := by decide
  have hdescent : baseEnd_5064729 < baseStart_5064729 := by decide
  rcases family_descends (prefixWord ++ tailWord_5064729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5064730 : List Nat := [3, 1, 1, 3, 1, 4, 2, 2, 1, 3, 2]
def baseStart_5064730 : Nat := 118140960795 + 5064730 * 2 ^ 59
def prefixEnd_5064730 : Nat := 4983230072969 + 3 ^ 40 * 5064730 * 2
def baseEnd_5064730 : Nat := 2600640875246074454282737

theorem tailTrace_5064730 : CollatzResearch.WordTrace tailWord_5064730 prefixEnd_5064730 2600640875246074454282737 := by
  unfold tailWord_5064730
  simp only [CollatzResearch.WordTrace]
  refine ⟨46181469735338917965993911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123150585960903781242650429 46181469735338917965993911)
  ·
    refine ⟨69272204603008376948990867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46181469735338917965993911 69272204603008376948990867)
    ·
      refine ⟨103908306904512565423486301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69272204603008376948990867 103908306904512565423486301)
      ·
        refine ⟨38965615089192212033807363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 103908306904512565423486301 38965615089192212033807363)
        ·
          refine ⟨58448422633788318050711045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38965615089192212033807363 58448422633788318050711045)
          ·
            refine ⟨10959079243835309634508321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58448422633788318050711045 10959079243835309634508321)
            ·
              refine ⟨8219309432876482225881241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10959079243835309634508321 8219309432876482225881241)
              ·
                refine ⟨6164482074657361669410931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8219309432876482225881241 6164482074657361669410931)
                ·
                  refine ⟨9246723111986042504116397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6164482074657361669410931 9246723111986042504116397)
                  ·
                    refine ⟨3467521166994765939043649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9246723111986042504116397 3467521166994765939043649)
                    ·
                      refine ⟨2600640875246074454282737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3467521166994765939043649 2600640875246074454282737)
                      ·
                        rfl

theorem cell23_5064730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 2, 2, 1, 3, 2].length) (baseStart_5064730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5064730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5064730 prefixEnd_5064730 := by exact prefixLift 5064730
  have htrace : WordTrace (prefixWord ++ tailWord_5064730) baseStart_5064730 baseEnd_5064730 := by
    simpa [prefixWord, tailWord_5064730, baseEnd_5064730] using wordTrace_append hprefix tailTrace_5064730
  have hstable : (prefixWord ++ tailWord_5064730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5064730).length < 2 ^ (prefixWord ++ tailWord_5064730).sum := by decide
  have hdescent : baseEnd_5064730 < baseStart_5064730 := by decide
  rcases family_descends (prefixWord ++ tailWord_5064730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5064746 : List Nat := [3, 1, 4, 1, 2, 1, 1, 1, 1, 3, 5]
def baseStart_5064746 : Nat := 118140960795 + 5064746 * 2 ^ 59
def prefixEnd_5064746 : Nat := 4983230072969 + 3 ^ 40 * 5064746 * 2
def baseEnd_5064746 : Nat := 2600649090936546391682663

theorem tailTrace_5064746 : CollatzResearch.WordTrace tailWord_5064746 prefixEnd_5064746 2600649090936546391682663 := by
  unfold tailWord_5064746
  simp only [CollatzResearch.WordTrace]
  refine ⟨46181615627324426649139523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123150975006198471064372061 46181615627324426649139523)
  ·
    refine ⟨69272423440986639973709285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46181615627324426649139523 69272423440986639973709285)
    ·
      refine ⟨12988579395184994995070491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 69272423440986639973709285 12988579395184994995070491)
      ·
        refine ⟨19482869092777492492605737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12988579395184994995070491 19482869092777492492605737)
        ·
          refine ⟨14612151819583119369454303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19482869092777492492605737 14612151819583119369454303)
          ·
            refine ⟨21918227729374679054181455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14612151819583119369454303 21918227729374679054181455)
            ·
              refine ⟨32877341594062018581272183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21918227729374679054181455 32877341594062018581272183)
              ·
                refine ⟨49316012391093027871908275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32877341594062018581272183 49316012391093027871908275)
                ·
                  refine ⟨73974018586639541807862413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49316012391093027871908275 73974018586639541807862413)
                  ·
                    refine ⟨27740256969989828177948405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 73974018586639541807862413 27740256969989828177948405)
                    ·
                      refine ⟨2600649090936546391682663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27740256969989828177948405 2600649090936546391682663)
                      ·
                        rfl

theorem cell23_5064746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 1, 1, 3, 5].length) (baseStart_5064746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5064746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5064746 prefixEnd_5064746 := by exact prefixLift 5064746
  have htrace : WordTrace (prefixWord ++ tailWord_5064746) baseStart_5064746 baseEnd_5064746 := by
    simpa [prefixWord, tailWord_5064746, baseEnd_5064746] using wordTrace_append hprefix tailTrace_5064746
  have hstable : (prefixWord ++ tailWord_5064746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5064746).length < 2 ^ (prefixWord ++ tailWord_5064746).sum := by decide
  have hdescent : baseEnd_5064746 < baseStart_5064746 := by decide
  rcases family_descends (prefixWord ++ tailWord_5064746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5064826 : List Nat := [3, 1, 1, 1, 1, 1, 1, 1, 9, 4]
def baseStart_5064826 : Nat := 118140960795 + 5064826 * 2 ^ 59
def prefixEnd_5064826 : Nat := 4983230072969 + 3 ^ 40 * 5064826 * 2
def baseEnd_5064826 : Nat := 866896723129635359560765

theorem tailTrace_5064826 : CollatzResearch.WordTrace tailWord_5064826 prefixEnd_5064826 866896723129635359560765 := by
  unfold tailWord_5064826
  simp only [CollatzResearch.WordTrace]
  refine ⟨46182345087251970064867583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123152920232671920172980221 46182345087251970064867583)
  ·
    refine ⟨69273517630877955097301375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46182345087251970064867583 69273517630877955097301375)
    ·
      refine ⟨103910276446316932645952063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69273517630877955097301375 103910276446316932645952063)
      ·
        refine ⟨155865414669475398968928095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103910276446316932645952063 155865414669475398968928095)
        ·
          refine ⟨233798122004213098453392143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155865414669475398968928095 233798122004213098453392143)
          ·
            refine ⟨350697183006319647680088215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 233798122004213098453392143 350697183006319647680088215)
            ·
              refine ⟨526045774509479471520132323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 350697183006319647680088215 526045774509479471520132323)
              ·
                refine ⟨789068661764219207280198485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 526045774509479471520132323 789068661764219207280198485)
                ·
                  refine ⟨4623449190024721917657413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 789068661764219207280198485 4623449190024721917657413)
                  ·
                    refine ⟨866896723129635359560765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4623449190024721917657413 866896723129635359560765)
                    ·
                      rfl

theorem cell23_5064826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 9, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 9, 4].length) (baseStart_5064826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5064826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5064826 prefixEnd_5064826 := by exact prefixLift 5064826
  have htrace : WordTrace (prefixWord ++ tailWord_5064826) baseStart_5064826 baseEnd_5064826 := by
    simpa [prefixWord, tailWord_5064826, baseEnd_5064826] using wordTrace_append hprefix tailTrace_5064826
  have hstable : (prefixWord ++ tailWord_5064826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5064826).length < 2 ^ (prefixWord ++ tailWord_5064826).sum := by decide
  have hdescent : baseEnd_5064826 < baseStart_5064826 := by decide
  rcases family_descends (prefixWord ++ tailWord_5064826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5064877 : List Nat := [1, 5, 2, 1, 2, 1, 2, 4, 1, 4]
def baseStart_5064877 : Nat := 118140960795 + 5064877 * 2 ^ 59
def prefixEnd_5064877 : Nat := 4983230072969 + 3 ^ 40 * 5064877 * 2
def baseEnd_5064877 : Nat := 866905452300761793048187

theorem tailTrace_5064877 : CollatzResearch.WordTrace tailWord_5064877 prefixEnd_5064877 866905452300761793048187 := by
  unfold tailWord_5064877
  simp only [CollatzResearch.WordTrace]
  refine ⟨184731240471823115969576885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123154160314548743979717923 184731240471823115969576885)
  ·
    refine ⟨17318553794233417122147833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 184731240471823115969576885 17318553794233417122147833)
    ·
      refine ⟨12988915345675062841610875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17318553794233417122147833 12988915345675062841610875)
      ·
        refine ⟨19483373018512594262416313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12988915345675062841610875 19483373018512594262416313)
        ·
          refine ⟨14612529763884445696812235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19483373018512594262416313 14612529763884445696812235)
          ·
            refine ⟨21918794645826668545218353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14612529763884445696812235 21918794645826668545218353)
            ·
              refine ⟨16439095984370001408913765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21918794645826668545218353 16439095984370001408913765)
              ·
                refine ⟨3082330497069375264171331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16439095984370001408913765 3082330497069375264171331)
                ·
                  refine ⟨4623495745604062896256997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3082330497069375264171331 4623495745604062896256997)
                  ·
                    refine ⟨866905452300761793048187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4623495745604062896256997 866905452300761793048187)
                    ·
                      rfl

theorem cell23_5064877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 4, 1, 4].length) (baseStart_5064877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5064877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5064877 prefixEnd_5064877 := by exact prefixLift 5064877
  have htrace : WordTrace (prefixWord ++ tailWord_5064877) baseStart_5064877 baseEnd_5064877 := by
    simpa [prefixWord, tailWord_5064877, baseEnd_5064877] using wordTrace_append hprefix tailTrace_5064877
  have hstable : (prefixWord ++ tailWord_5064877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5064877).length < 2 ^ (prefixWord ++ tailWord_5064877).sum := by decide
  have hdescent : baseEnd_5064877 < baseStart_5064877 := by decide
  rcases family_descends (prefixWord ++ tailWord_5064877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5064910 : List Nat := [4, 1, 1, 1, 4, 1, 2, 1, 1, 5, 2]
def baseStart_5064910 : Nat := 118140960795 + 5064910 * 2 ^ 59
def prefixEnd_5064910 : Nat := 4983230072969 + 3 ^ 40 * 5064910 * 2
def baseEnd_5064910 : Nat := 2600733301763883750031909

theorem tailTrace_5064910 : CollatzResearch.WordTrace tailWord_5064910 prefixEnd_5064910 2600733301763883750031909 := by
  unfold tailWord_5064910
  simp only [CollatzResearch.WordTrace]
  refine ⟨23091555510087945325691023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 123154962720469041737018789 23091555510087945325691023)
  ·
    refine ⟨34637333265131917988536535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23091555510087945325691023 34637333265131917988536535)
    ·
      refine ⟨51955999897697876982804803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34637333265131917988536535 51955999897697876982804803)
      ·
        refine ⟨77933999846546815474207205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51955999897697876982804803 77933999846546815474207205)
        ·
          refine ⟨14612624971227527901413851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 77933999846546815474207205 14612624971227527901413851)
          ·
            refine ⟨21918937456841291852120777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14612624971227527901413851 21918937456841291852120777)
            ·
              refine ⟨16439203092630968889090583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21918937456841291852120777 16439203092630968889090583)
              ·
                refine ⟨24658804638946453333635875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16439203092630968889090583 24658804638946453333635875)
                ·
                  refine ⟨36988206958419680000453813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24658804638946453333635875 36988206958419680000453813)
                  ·
                    refine ⟨3467644402351845000042545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 36988206958419680000453813 3467644402351845000042545)
                    ·
                      refine ⟨2600733301763883750031909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3467644402351845000042545 2600733301763883750031909)
                      ·
                        rfl

theorem cell23_5064910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 1, 1, 5, 2].length) (baseStart_5064910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5064910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5064910 prefixEnd_5064910 := by exact prefixLift 5064910
  have htrace : WordTrace (prefixWord ++ tailWord_5064910) baseStart_5064910 baseEnd_5064910 := by
    simpa [prefixWord, tailWord_5064910, baseEnd_5064910] using wordTrace_append hprefix tailTrace_5064910
  have hstable : (prefixWord ++ tailWord_5064910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5064910).length < 2 ^ (prefixWord ++ tailWord_5064910).sum := by decide
  have hdescent : baseEnd_5064910 < baseStart_5064910 := by decide
  rcases family_descends (prefixWord ++ tailWord_5064910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5064943 : List Nat := [1, 1, 2, 1, 6, 1, 2, 2, 1, 1, 5]
def baseStart_5064943 : Nat := 118140960795 + 5064943 * 2 ^ 59
def prefixEnd_5064943 : Nat := 4983230072969 + 3 ^ 40 * 5064943 * 2
def baseEnd_5064943 : Nat := 2600750246625482120919257

theorem tailTrace_5064943 : CollatzResearch.WordTrace tailWord_5064943 prefixEnd_5064943 2600750246625482120919257 := by
  unfold tailWord_5064943
  simp only [CollatzResearch.WordTrace]
  refine ⟨184733647689584009241479483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123155765126389339494319655 184733647689584009241479483)
  ·
    refine ⟨277100471534376013862219225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184733647689584009241479483 277100471534376013862219225)
    ·
      refine ⟨207825353650782010396664419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 277100471534376013862219225 207825353650782010396664419)
      ·
        refine ⟨311738030476173015594996629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 207825353650782010396664419 311738030476173015594996629)
        ·
          refine ⟨14612720178570610106015467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 311738030476173015594996629 14612720178570610106015467)
          ·
            refine ⟨21919080267855915159023201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14612720178570610106015467 21919080267855915159023201)
            ·
              refine ⟨16439310200891936369267401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21919080267855915159023201 16439310200891936369267401)
              ·
                refine ⟨12329482650668952276950551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16439310200891936369267401 12329482650668952276950551)
                ·
                  refine ⟨18494223976003428415425827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12329482650668952276950551 18494223976003428415425827)
                  ·
                    refine ⟨27741335964005142623138741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18494223976003428415425827 27741335964005142623138741)
                    ·
                      refine ⟨2600750246625482120919257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27741335964005142623138741 2600750246625482120919257)
                      ·
                        rfl

theorem cell23_5064943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 2, 1, 1, 5].length) (baseStart_5064943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5064943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5064943 prefixEnd_5064943 := by exact prefixLift 5064943
  have htrace : WordTrace (prefixWord ++ tailWord_5064943) baseStart_5064943 baseEnd_5064943 := by
    simpa [prefixWord, tailWord_5064943, baseEnd_5064943] using wordTrace_append hprefix tailTrace_5064943
  have hstable : (prefixWord ++ tailWord_5064943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5064943).length < 2 ^ (prefixWord ++ tailWord_5064943).sum := by decide
  have hdescent : baseEnd_5064943 < baseStart_5064943 := by decide
  rcases family_descends (prefixWord ++ tailWord_5064943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5064960 : List Nat := [2, 1, 1, 2, 1, 1, 7, 2, 1, 2, 3]
def baseStart_5064960 : Nat := 118140960795 + 5064960 * 2 ^ 59
def prefixEnd_5064960 : Nat := 4983230072969 + 3 ^ 40 * 5064960 * 2
def baseEnd_5064960 : Nat := 2600758975796608554406679

theorem tailTrace_5064960 : CollatzResearch.WordTrace tailWord_5064960 prefixEnd_5064960 2600758975796608554406679 := by
  unfold tailWord_5064960
  simp only [CollatzResearch.WordTrace]
  refine ⟨92367133865261210572424167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123156178487014947429898889 92367133865261210572424167)
  ·
    refine ⟨138550700797891815858636251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92367133865261210572424167 138550700797891815858636251)
    ·
      refine ⟨207826051196837723787954377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138550700797891815858636251 207826051196837723787954377)
      ·
        refine ⟨155869538397628292840965783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 207826051196837723787954377 155869538397628292840965783)
        ·
          refine ⟨233804307596442439261448675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155869538397628292840965783 233804307596442439261448675)
          ·
            refine ⟨350706461394663658892173013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 233804307596442439261448675 350706461394663658892173013)
            ·
              refine ⟨8219682688937429505285305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 350706461394663658892173013 8219682688937429505285305)
              ·
                refine ⟨6164762016703072128963979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8219682688937429505285305 6164762016703072128963979)
                ·
                  refine ⟨9247143025054608193445969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6164762016703072128963979 9247143025054608193445969)
                  ·
                    refine ⟨6935357268790956145084477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9247143025054608193445969 6935357268790956145084477)
                    ·
                      refine ⟨2600758975796608554406679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6935357268790956145084477 2600758975796608554406679)
                      ·
                        rfl

theorem cell23_5064960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 7, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 7, 2, 1, 2, 3].length) (baseStart_5064960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5064960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5064960 prefixEnd_5064960 := by exact prefixLift 5064960
  have htrace : WordTrace (prefixWord ++ tailWord_5064960) baseStart_5064960 baseEnd_5064960 := by
    simpa [prefixWord, tailWord_5064960, baseEnd_5064960] using wordTrace_append hprefix tailTrace_5064960
  have hstable : (prefixWord ++ tailWord_5064960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5064960).length < 2 ^ (prefixWord ++ tailWord_5064960).sum := by decide
  have hdescent : baseEnd_5064960 < baseStart_5064960 := by decide
  rcases family_descends (prefixWord ++ tailWord_5064960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5064974 : List Nat := [4, 1, 1, 2, 1, 2, 2, 5, 1, 2, 2]
def baseStart_5064974 : Nat := 118140960795 + 5064974 * 2 ^ 59
def prefixEnd_5064974 : Nat := 4983230072969 + 3 ^ 40 * 5064974 * 2
def baseEnd_5064974 : Nat := 2600766164525771499631615

theorem tailTrace_5064974 : CollatzResearch.WordTrace tailWord_5064974 prefixEnd_5064974 2600766164525771499631615 := by
  unfold tailWord_5064974
  simp only [CollatzResearch.WordTrace]
  refine ⟨23091847294058962691982247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 123156518901647801023905317 23091847294058962691982247)
  ·
    refine ⟨34637770941088444037973371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23091847294058962691982247 34637770941088444037973371)
    ·
      refine ⟨51956656411632666056960057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34637770941088444037973371 51956656411632666056960057)
      ·
        refine ⟨38967492308724499542720043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51956656411632666056960057 38967492308724499542720043)
        ·
          refine ⟨58451238463086749314080065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38967492308724499542720043 58451238463086749314080065)
          ·
            refine ⟨43838428847315061985560049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58451238463086749314080065 43838428847315061985560049)
            ·
              refine ⟨32878821635486296489170037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43838428847315061985560049 32878821635486296489170037)
              ·
                refine ⟨3082389528326840295859691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32878821635486296489170037 3082389528326840295859691)
                ·
                  refine ⟨4623584292490260443789537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3082389528326840295859691 4623584292490260443789537)
                  ·
                    refine ⟨3467688219367695332842153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4623584292490260443789537 3467688219367695332842153)
                    ·
                      refine ⟨2600766164525771499631615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3467688219367695332842153 2600766164525771499631615)
                      ·
                        rfl

theorem cell23_5064974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 5, 1, 2, 2].length) (baseStart_5064974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5064974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5064974 prefixEnd_5064974 := by exact prefixLift 5064974
  have htrace : WordTrace (prefixWord ++ tailWord_5064974) baseStart_5064974 baseEnd_5064974 := by
    simpa [prefixWord, tailWord_5064974, baseEnd_5064974] using wordTrace_append hprefix tailTrace_5064974
  have hstable : (prefixWord ++ tailWord_5064974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5064974).length < 2 ^ (prefixWord ++ tailWord_5064974).sum := by decide
  have hdescent : baseEnd_5064974 < baseStart_5064974 := by decide
  rcases family_descends (prefixWord ++ tailWord_5064974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5064977 : List Nat := [1, 2, 2, 1, 1, 6, 3, 1, 1, 2, 3]
def baseStart_5064977 : Nat := 118140960795 + 5064977 * 2 ^ 59
def prefixEnd_5064977 : Nat := 4983230072969 + 3 ^ 40 * 5064977 * 2
def baseEnd_5064977 : Nat := 2600767704967734987894101

theorem tailTrace_5064977 : CollatzResearch.WordTrace tailWord_5064977 prefixEnd_5064977 2600767704967734987894101 := by
  unfold tailWord_5064977
  simp only [CollatzResearch.WordTrace]
  refine ⟨184734887771460833048217185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123156591847640555365478123 184734887771460833048217185)
  ·
    refine ⟨138551165828595624786162889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184734887771460833048217185 138551165828595624786162889)
    ·
      refine ⟨103913374371446718589622167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138551165828595624786162889 103913374371446718589622167)
      ·
        refine ⟨155870061557170077884433251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103913374371446718589622167 155870061557170077884433251)
        ·
          refine ⟨233805092335755116826649877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155870061557170077884433251 233805092335755116826649877)
          ·
            refine ⟨10959613703238521101249213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 233805092335755116826649877 10959613703238521101249213)
            ·
              refine ⟨4109855138714445412968455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10959613703238521101249213 4109855138714445412968455)
              ·
                refine ⟨6164782708071668119452683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4109855138714445412968455 6164782708071668119452683)
                ·
                  refine ⟨9247174062107502179179025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6164782708071668119452683 9247174062107502179179025)
                  ·
                    refine ⟨6935380546580626634384269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9247174062107502179179025 6935380546580626634384269)
                    ·
                      refine ⟨2600767704967734987894101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6935380546580626634384269 2600767704967734987894101)
                      ·
                        rfl

theorem cell23_5064977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 3, 1, 1, 2, 3].length) (baseStart_5064977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5064977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5064977 prefixEnd_5064977 := by exact prefixLift 5064977
  have htrace : WordTrace (prefixWord ++ tailWord_5064977) baseStart_5064977 baseEnd_5064977 := by
    simpa [prefixWord, tailWord_5064977, baseEnd_5064977] using wordTrace_append hprefix tailTrace_5064977
  have hstable : (prefixWord ++ tailWord_5064977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5064977).length < 2 ^ (prefixWord ++ tailWord_5064977).sum := by decide
  have hdescent : baseEnd_5064977 < baseStart_5064977 := by decide
  rcases family_descends (prefixWord ++ tailWord_5064977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5064991 : List Nat := [1, 1, 2, 4, 3, 1, 4, 2, 1, 2, 2]
def baseStart_5064991 : Nat := 118140960795 + 5064991 * 2 ^ 59
def prefixEnd_5064991 : Nat := 4983230072969 + 3 ^ 40 * 5064991 * 2
def baseEnd_5064991 : Nat := 2600774893696897933119037

theorem tailTrace_5064991 : CollatzResearch.WordTrace tailWord_5064991 prefixEnd_5064991 2600774893696897933119037 := by
  unfold tailWord_5064991
  simp only [CollatzResearch.WordTrace]
  refine ⟨184735398393410113439226827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123156932262273408959484551 184735398393410113439226827)
  ·
    refine ⟨277103097590115170158840241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184735398393410113439226827 277103097590115170158840241)
    ·
      refine ⟨207827323192586377619130181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 277103097590115170158840241 207827323192586377619130181)
      ·
        refine ⟨38967623098609945803586909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 207827323192586377619130181 38967623098609945803586909)
        ·
          refine ⟨14612858661978729676345091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38967623098609945803586909 14612858661978729676345091)
          ·
            refine ⟨21919287992968094514517637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14612858661978729676345091 21919287992968094514517637)
            ·
              refine ⟨4109866498681517721472057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21919287992968094514517637 4109866498681517721472057)
              ·
                refine ⟨3082399874011138291104043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4109866498681517721472057 3082399874011138291104043)
                ·
                  refine ⟨4623599811016707436656065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3082399874011138291104043 4623599811016707436656065)
                  ·
                    refine ⟨3467699858262530577492049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4623599811016707436656065 3467699858262530577492049)
                    ·
                      refine ⟨2600774893696897933119037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3467699858262530577492049 2600774893696897933119037)
                      ·
                        rfl

theorem cell23_5064991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 4, 2, 1, 2, 2].length) (baseStart_5064991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5064991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5064991 prefixEnd_5064991 := by exact prefixLift 5064991
  have htrace : WordTrace (prefixWord ++ tailWord_5064991) baseStart_5064991 baseEnd_5064991 := by
    simpa [prefixWord, tailWord_5064991, baseEnd_5064991] using wordTrace_append hprefix tailTrace_5064991
  have hstable : (prefixWord ++ tailWord_5064991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5064991).length < 2 ^ (prefixWord ++ tailWord_5064991).sum := by decide
  have hdescent : baseEnd_5064991 < baseStart_5064991 := by decide
  rcases family_descends (prefixWord ++ tailWord_5064991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5065013 : List Nat := [1, 3, 3, 1, 2, 1, 1, 2, 2, 3, 4]
def baseStart_5065013 : Nat := 118140960795 + 5065013 * 2 ^ 59
def prefixEnd_5065013 : Nat := 4983230072969 + 3 ^ 40 * 5065013 * 2
def baseEnd_5065013 : Nat := 2600786190271296847043935

theorem tailTrace_5065013 : CollatzResearch.WordTrace tailWord_5065013 prefixEnd_5065013 2600786190271296847043935 := by
  unfold tailWord_5065013
  simp only [CollatzResearch.WordTrace]
  refine ⟨184736200799330411196527693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123157467199553607464351795 184736200799330411196527693)
  ·
    refine ⟨69276075299748904198697885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 184736200799330411196527693 69276075299748904198697885)
    ·
      refine ⟨25978528237405839074511707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69276075299748904198697885 25978528237405839074511707)
      ·
        refine ⟨38967792356108758611767561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25978528237405839074511707 38967792356108758611767561)
        ·
          refine ⟨29225844267081568958825671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38967792356108758611767561 29225844267081568958825671)
          ·
            refine ⟨43838766400622353438238507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29225844267081568958825671 43838766400622353438238507)
            ·
              refine ⟨65758149600933530157357761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43838766400622353438238507 65758149600933530157357761)
              ·
                refine ⟨49318612200700147618018321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65758149600933530157357761 49318612200700147618018321)
                ·
                  refine ⟨36988959150525110713513741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49318612200700147618018321 36988959150525110713513741)
                  ·
                    refine ⟨13870859681446916517567653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36988959150525110713513741 13870859681446916517567653)
                    ·
                      refine ⟨2600786190271296847043935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13870859681446916517567653 2600786190271296847043935)
                      ·
                        rfl

theorem cell23_5065013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 2, 2, 3, 4].length) (baseStart_5065013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5065013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5065013 prefixEnd_5065013 := by exact prefixLift 5065013
  have htrace : WordTrace (prefixWord ++ tailWord_5065013) baseStart_5065013 baseEnd_5065013 := by
    simpa [prefixWord, tailWord_5065013, baseEnd_5065013] using wordTrace_append hprefix tailTrace_5065013
  have hstable : (prefixWord ++ tailWord_5065013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5065013).length < 2 ^ (prefixWord ++ tailWord_5065013).sum := by decide
  have hdescent : baseEnd_5065013 < baseStart_5065013 := by decide
  rcases family_descends (prefixWord ++ tailWord_5065013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5065017 : List Nat := [1, 2, 1, 6, 1, 1, 2, 1, 3, 3, 2]
def baseStart_5065017 : Nat := 118140960795 + 5065017 * 2 ^ 59
def prefixEnd_5065017 : Nat := 4983230072969 + 3 ^ 40 * 5065017 * 2
def baseEnd_5065017 : Nat := 2600788244193914831393917

theorem tailTrace_5065017 : CollatzResearch.WordTrace tailWord_5065017 prefixEnd_5065017 2600788244193914831393917 := by
  unfold tailWord_5065017
  simp only [CollatzResearch.WordTrace]
  refine ⟨184736346691315919879673305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123157564460877279919782203 184736346691315919879673305)
  ·
    refine ⟨138552260018486939909754979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184736346691315919879673305 138552260018486939909754979)
    ·
      refine ⟨207828390027730409864632469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138552260018486939909754979 207828390027730409864632469)
      ·
        refine ⟨9741955782549862962404647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 207828390027730409864632469 9741955782549862962404647)
        ·
          refine ⟨14612933673824794443606971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9741955782549862962404647 14612933673824794443606971)
          ·
            refine ⟨21919400510737191665410457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14612933673824794443606971 21919400510737191665410457)
            ·
              refine ⟨16439550383052893749057843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21919400510737191665410457 16439550383052893749057843)
              ·
                refine ⟨24659325574579340623586765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16439550383052893749057843 24659325574579340623586765)
                ·
                  refine ⟨9247247090467252733845037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24659325574579340623586765 9247247090467252733845037)
                  ·
                    refine ⟨3467717658925219775191889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9247247090467252733845037 3467717658925219775191889)
                    ·
                      refine ⟨2600788244193914831393917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3467717658925219775191889 2600788244193914831393917)
                      ·
                        rfl

theorem cell23_5065017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 1, 3, 3, 2].length) (baseStart_5065017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5065017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5065017 prefixEnd_5065017 := by exact prefixLift 5065017
  have htrace : WordTrace (prefixWord ++ tailWord_5065017) baseStart_5065017 baseEnd_5065017 := by
    simpa [prefixWord, tailWord_5065017, baseEnd_5065017] using wordTrace_append hprefix tailTrace_5065017
  have hstable : (prefixWord ++ tailWord_5065017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5065017).length < 2 ^ (prefixWord ++ tailWord_5065017).sum := by decide
  have hdescent : baseEnd_5065017 < baseStart_5065017 := by decide
  rcases family_descends (prefixWord ++ tailWord_5065017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5065028 : List Nat := [2, 3, 4, 1, 3, 1, 2, 1, 1, 2, 3]
def baseStart_5065028 : Nat := 118140960795 + 5065028 * 2 ^ 59
def prefixEnd_5065028 : Nat := 4983230072969 + 3 ^ 40 * 5065028 * 2
def baseEnd_5065028 : Nat := 2600793892481114288356367

theorem tailTrace_5065028 : CollatzResearch.WordTrace tailWord_5065028 prefixEnd_5065028 2600793892481114288356367 := by
  unfold tailWord_5065028
  simp only [CollatzResearch.WordTrace]
  refine ⟨92368373947138034379161869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123157831929517379172215825 92368373947138034379161869)
  ·
    refine ⟨34638140230176762892185701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92368373947138034379161869 34638140230176762892185701)
    ·
      refine ⟨6494651293158143042284819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34638140230176762892185701 6494651293158143042284819)
      ·
        refine ⟨9741976939737214563427229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6494651293158143042284819 9741976939737214563427229)
        ·
          refine ⟨3653241352401455461285211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9741976939737214563427229 3653241352401455461285211)
          ·
            refine ⟨5479862028602183191927817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3653241352401455461285211 5479862028602183191927817)
            ·
              refine ⟨4109896521451637393945863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5479862028602183191927817 4109896521451637393945863)
              ·
                refine ⟨6164844782177456090918795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4109896521451637393945863 6164844782177456090918795)
                ·
                  refine ⟨9247267173266184136378193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6164844782177456090918795 9247267173266184136378193)
                  ·
                    refine ⟨6935450379949638102283645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9247267173266184136378193 6935450379949638102283645)
                    ·
                      refine ⟨2600793892481114288356367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6935450379949638102283645 2600793892481114288356367)
                      ·
                        rfl

theorem cell23_5065028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 2, 1, 1, 2, 3].length) (baseStart_5065028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5065028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5065028 prefixEnd_5065028 := by exact prefixLift 5065028
  have htrace : WordTrace (prefixWord ++ tailWord_5065028) baseStart_5065028 baseEnd_5065028 := by
    simpa [prefixWord, tailWord_5065028, baseEnd_5065028] using wordTrace_append hprefix tailTrace_5065028
  have hstable : (prefixWord ++ tailWord_5065028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5065028).length < 2 ^ (prefixWord ++ tailWord_5065028).sum := by decide
  have hdescent : baseEnd_5065028 < baseStart_5065028 := by decide
  rcases family_descends (prefixWord ++ tailWord_5065028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5065047 : List Nat := [1, 1, 3, 2, 3, 1, 3, 1, 4, 2, 2]
def baseStart_5065047 : Nat := 118140960795 + 5065047 * 2 ^ 59
def prefixEnd_5065047 : Nat := 4983230072969 + 3 ^ 40 * 5065047 * 2
def baseEnd_5065047 : Nat := 2600803648613549714018779

theorem tailTrace_5065047 : CollatzResearch.WordTrace tailWord_5065047 prefixEnd_5065047 2600803648613549714018779 := by
  unfold tailWord_5065047
  simp only [CollatzResearch.WordTrace]
  refine ⟨184737440881207235003265395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123158293920804823335510263 184737440881207235003265395)
  ·
    refine ⟨277106161321810852504898093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184737440881207235003265395 277106161321810852504898093)
    ·
      refine ⟨103914810495679069689336785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 277106161321810852504898093 103914810495679069689336785)
      ·
        refine ⟨77936107871759302267002589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103914810495679069689336785 77936107871759302267002589)
        ·
          refine ⟨29226040451909738350125971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77936107871759302267002589 29226040451909738350125971)
          ·
            refine ⟨43839060677864607525188957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29226040451909738350125971 43839060677864607525188957)
            ·
              refine ⟨16439647754199227821945859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43839060677864607525188957 16439647754199227821945859)
              ·
                refine ⟨24659471631298841732918789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16439647754199227821945859 24659471631298841732918789)
                ·
                  refine ⟨4623650930868532824922273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24659471631298841732918789 4623650930868532824922273)
                  ·
                    refine ⟨3467738198151399618691705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4623650930868532824922273 3467738198151399618691705)
                    ·
                      refine ⟨2600803648613549714018779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3467738198151399618691705 2600803648613549714018779)
                      ·
                        rfl

theorem cell23_5065047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 1, 4, 2, 2].length) (baseStart_5065047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5065047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5065047 prefixEnd_5065047 := by exact prefixLift 5065047
  have htrace : WordTrace (prefixWord ++ tailWord_5065047) baseStart_5065047 baseEnd_5065047 := by
    simpa [prefixWord, tailWord_5065047, baseEnd_5065047] using wordTrace_append hprefix tailTrace_5065047
  have hstable : (prefixWord ++ tailWord_5065047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5065047).length < 2 ^ (prefixWord ++ tailWord_5065047).sum := by decide
  have hdescent : baseEnd_5065047 < baseStart_5065047 := by decide
  rcases family_descends (prefixWord ++ tailWord_5065047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5065064 : List Nat := [2, 1, 4, 2, 2, 3, 1, 1, 1, 4, 2]
def baseStart_5065064 : Nat := 118140960795 + 5065064 * 2 ^ 59
def prefixEnd_5065064 : Nat := 4983230072969 + 3 ^ 40 * 5065064 * 2
def baseEnd_5065064 : Nat := 2600812377784676147506201

theorem tailTrace_5065064 : CollatzResearch.WordTrace tailWord_5065064 prefixEnd_5065064 2600812377784676147506201 := by
  unfold tailWord_5065064
  simp only [CollatzResearch.WordTrace]
  refine ⟨92369030461072823453317123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123158707281430431271089497 92369030461072823453317123)
  ·
    refine ⟨138553545691609235179975685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92369030461072823453317123 138553545691609235179975685)
    ·
      refine ⟨25978789817176731596245441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 138553545691609235179975685 25978789817176731596245441)
      ·
        refine ⟨19484092362882548697184081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25978789817176731596245441 19484092362882548697184081)
        ·
          refine ⟨14613069272161911522888061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19484092362882548697184081 14613069272161911522888061)
          ·
            refine ⟨5479900977060716821083023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14613069272161911522888061 5479900977060716821083023)
            ·
              refine ⟨8219851465591075231624535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5479900977060716821083023 8219851465591075231624535)
              ·
                refine ⟨12329777198386612847436803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8219851465591075231624535 12329777198386612847436803)
                ·
                  refine ⟨18494665797579919271155205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12329777198386612847436803 18494665797579919271155205)
                  ·
                    refine ⟨3467749837046234863341601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18494665797579919271155205 3467749837046234863341601)
                    ·
                      refine ⟨2600812377784676147506201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3467749837046234863341601 2600812377784676147506201)
                      ·
                        rfl

theorem cell23_5065064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 1, 1, 1, 4, 2].length) (baseStart_5065064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5065064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5065064 prefixEnd_5065064 := by exact prefixLift 5065064
  have htrace : WordTrace (prefixWord ++ tailWord_5065064) baseStart_5065064 baseEnd_5065064 := by
    simpa [prefixWord, tailWord_5065064, baseEnd_5065064] using wordTrace_append hprefix tailTrace_5065064
  have hstable : (prefixWord ++ tailWord_5065064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5065064).length < 2 ^ (prefixWord ++ tailWord_5065064).sum := by decide
  have hdescent : baseEnd_5065064 < baseStart_5065064 := by decide
  rcases family_descends (prefixWord ++ tailWord_5065064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5065083 : List Nat := [1, 1, 1, 1, 1, 7, 2, 1, 1, 7]
def baseStart_5065083 : Nat := 118140960795 + 5065083 * 2 ^ 59
def prefixEnd_5065083 : Nat := 4983230072969 + 3 ^ 40 * 5065083 * 2
def baseEnd_5065083 : Nat := 866940711305703857722871

theorem tailTrace_5065083 : CollatzResearch.WordTrace tailWord_5065083 prefixEnd_5065083 866940711305703857722871 := by
  unfold tailWord_5065083
  simp only [CollatzResearch.WordTrace]
  refine ⟨184738753909076813151575903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123159169272717875434383935 184738753909076813151575903)
  ·
    refine ⟨277108130863615219727363855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184738753909076813151575903 277108130863615219727363855)
    ·
      refine ⟨415662196295422829591045783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 277108130863615219727363855 415662196295422829591045783)
      ·
        refine ⟨623493294443134244386568675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 415662196295422829591045783 623493294443134244386568675)
        ·
          refine ⟨935239941664701366579853013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 623493294443134244386568675 935239941664701366579853013)
          ·
            refine ⟨21919686132766438279215305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 935239941664701366579853013 21919686132766438279215305)
            ·
              refine ⟨16439764599574828709411479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21919686132766438279215305 16439764599574828709411479)
              ·
                refine ⟨24659646899362243064117219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16439764599574828709411479 24659646899362243064117219)
                ·
                  refine ⟨36989470349043364596175829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24659646899362243064117219 36989470349043364596175829)
                  ·
                    refine ⟨866940711305703857722871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36989470349043364596175829 866940711305703857722871)
                    ·
                      rfl

theorem cell23_5065083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 1, 1, 7].length) (baseStart_5065083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5065083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5065083 prefixEnd_5065083 := by exact prefixLift 5065083
  have htrace : WordTrace (prefixWord ++ tailWord_5065083) baseStart_5065083 baseEnd_5065083 := by
    simpa [prefixWord, tailWord_5065083, baseEnd_5065083] using wordTrace_append hprefix tailTrace_5065083
  have hstable : (prefixWord ++ tailWord_5065083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5065083).length < 2 ^ (prefixWord ++ tailWord_5065083).sum := by decide
  have hdescent : baseEnd_5065083 < baseStart_5065083 := by decide
  rcases family_descends (prefixWord ++ tailWord_5065083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5065093 : List Nat := [1, 3, 1, 1, 3, 1, 1, 4, 1, 2, 5]
def baseStart_5065093 : Nat := 118140960795 + 5065093 * 2 ^ 59
def prefixEnd_5065093 : Nat := 4983230072969 + 3 ^ 40 * 5065093 * 2
def baseEnd_5065093 : Nat := 2600827268723656534043567

theorem tailTrace_5065093 : CollatzResearch.WordTrace tailWord_5065093 prefixEnd_5065093 2600827268723656534043567 := by
  unfold tailWord_5065093
  simp only [CollatzResearch.WordTrace]
  refine ⟨184739118639040584859439933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123159412426027056572959955 184739118639040584859439933)
  ·
    refine ⟨69277169489640219322289975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 184739118639040584859439933 69277169489640219322289975)
    ·
      refine ⟨103915754234460328983434963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69277169489640219322289975 103915754234460328983434963)
      ·
        refine ⟨155873631351690493475152445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103915754234460328983434963 155873631351690493475152445)
        ·
          refine ⟨58452611756883935053182167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 155873631351690493475152445 58452611756883935053182167)
          ·
            refine ⟨87678917635325902579773251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58452611756883935053182167 87678917635325902579773251)
            ·
              refine ⟨131518376452988853869659877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87678917635325902579773251 131518376452988853869659877)
              ·
                refine ⟨24659695584935410100561227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 131518376452988853869659877 24659695584935410100561227)
                ·
                  refine ⟨36989543377403115150841841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24659695584935410100561227 36989543377403115150841841)
                  ·
                    refine ⟨27742157533052336363131381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36989543377403115150841841 27742157533052336363131381)
                    ·
                      refine ⟨2600827268723656534043567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27742157533052336363131381 2600827268723656534043567)
                      ·
                        rfl

theorem cell23_5065093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 4, 1, 2, 5].length) (baseStart_5065093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5065093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5065093 prefixEnd_5065093 := by exact prefixLift 5065093
  have htrace : WordTrace (prefixWord ++ tailWord_5065093) baseStart_5065093 baseEnd_5065093 := by
    simpa [prefixWord, tailWord_5065093, baseEnd_5065093] using wordTrace_append hprefix tailTrace_5065093
  have hstable : (prefixWord ++ tailWord_5065093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5065093).length < 2 ^ (prefixWord ++ tailWord_5065093).sum := by decide
  have hdescent : baseEnd_5065093 < baseStart_5065093 := by decide
  rcases family_descends (prefixWord ++ tailWord_5065093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5065100 : List Nat := [2, 2, 1, 2, 1, 5, 1, 2, 2, 5]
def baseStart_5065100 : Nat := 118140960795 + 5065100 * 2 ^ 59
def prefixEnd_5065100 : Nat := 4983230072969 + 3 ^ 40 * 5065100 * 2
def baseEnd_5065100 : Nat := 866943621029412668885345

theorem tailTrace_5065100 : CollatzResearch.WordTrace tailWord_5065100 prefixEnd_5065100 866943621029412668885345 := by
  unfold tailWord_5065100
  simp only [CollatzResearch.WordTrace]
  refine ⟨92369686975007612527472377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123159582633343483369963169 92369686975007612527472377)
  ·
    refine ⟨69277265231255709395604283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92369686975007612527472377 69277265231255709395604283)
    ·
      refine ⟨103915897846883564093406425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69277265231255709395604283 103915897846883564093406425)
      ·
        refine ⟨77936923385162673070054819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103915897846883564093406425 77936923385162673070054819)
        ·
          refine ⟨116905385077744009605082229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77936923385162673070054819 116905385077744009605082229)
          ·
            refine ⟨10959879851038500900476459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 116905385077744009605082229 10959879851038500900476459)
            ·
              refine ⟨16439819776557751350714689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10959879851038500900476459 16439819776557751350714689)
              ·
                refine ⟨12329864832418313513036017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16439819776557751350714689 12329864832418313513036017)
                ·
                  refine ⟨9247398624313735134777013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12329864832418313513036017 9247398624313735134777013)
                  ·
                    refine ⟨866943621029412668885345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9247398624313735134777013 866943621029412668885345)
                    ·
                      rfl

theorem cell23_5065100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 2, 2, 5].length) (baseStart_5065100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5065100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5065100 prefixEnd_5065100 := by exact prefixLift 5065100
  have htrace : WordTrace (prefixWord ++ tailWord_5065100) baseStart_5065100 baseEnd_5065100 := by
    simpa [prefixWord, tailWord_5065100, baseEnd_5065100] using wordTrace_append hprefix tailTrace_5065100
  have hstable : (prefixWord ++ tailWord_5065100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5065100).length < 2 ^ (prefixWord ++ tailWord_5065100).sum := by decide
  have hdescent : baseEnd_5065100 < baseStart_5065100 := by decide
  rcases family_descends (prefixWord ++ tailWord_5065100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5065137 : List Nat := [1, 2, 2, 4, 1, 3, 2, 1, 2, 1, 4]
def baseStart_5065137 : Nat := 118140960795 + 5065137 * 2 ^ 59
def prefixEnd_5065137 : Nat := 4983230072969 + 3 ^ 40 * 5065137 * 2
def baseEnd_5065137 : Nat := 2600849861872454361893365

theorem tailTrace_5065137 : CollatzResearch.WordTrace tailWord_5065137 prefixEnd_5065137 2600849861872454361893365 := by
  unfold tailWord_5065137
  simp only [CollatzResearch.WordTrace]
  refine ⟨184740723450881180374041665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123160482300587453582694443 184740723450881180374041665)
  ·
    refine ⟨138555542588160885280531249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184740723450881180374041665 138555542588160885280531249)
    ·
      refine ⟨103916656941120663960398437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138555542588160885280531249 103916656941120663960398437)
      ·
        refine ⟨19484373176460124492574707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 103916656941120663960398437 19484373176460124492574707)
        ·
          refine ⟨29226559764690186738862061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19484373176460124492574707 29226559764690186738862061)
          ·
            refine ⟨10959959911758820027073273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29226559764690186738862061 10959959911758820027073273)
            ·
              refine ⟨8219969933819115020304955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10959959911758820027073273 8219969933819115020304955)
              ·
                refine ⟨12329954900728672530457433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8219969933819115020304955 12329954900728672530457433)
                ·
                  refine ⟨9247466175546504397843075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12329954900728672530457433 9247466175546504397843075)
                  ·
                    refine ⟨13871199263319756596764613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9247466175546504397843075 13871199263319756596764613)
                    ·
                      refine ⟨2600849861872454361893365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13871199263319756596764613 2600849861872454361893365)
                      ·
                        rfl

theorem cell23_5065137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 2, 1, 2, 1, 4].length) (baseStart_5065137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5065137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5065137 prefixEnd_5065137 := by exact prefixLift 5065137
  have htrace : WordTrace (prefixWord ++ tailWord_5065137) baseStart_5065137 baseEnd_5065137 := by
    simpa [prefixWord, tailWord_5065137, baseEnd_5065137] using wordTrace_append hprefix tailTrace_5065137
  have hstable : (prefixWord ++ tailWord_5065137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5065137).length < 2 ^ (prefixWord ++ tailWord_5065137).sum := by decide
  have hdescent : baseEnd_5065137 < baseStart_5065137 := by decide
  rcases family_descends (prefixWord ++ tailWord_5065137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5065160 : List Nat := [2, 1, 3, 1, 3, 2, 1, 4, 6]
def baseStart_5065160 : Nat := 118140960795 + 5065160 * 2 ^ 59
def prefixEnd_5065160 : Nat := 4983230072969 + 3 ^ 40 * 5065160 * 2
def baseEnd_5065160 : Nat := 288984630214167530211751

theorem tailTrace_5065160 : CollatzResearch.WordTrace tailWord_5065160 prefixEnd_5065160 288984630214167530211751 := by
  unfold tailWord_5065160
  simp only [CollatzResearch.WordTrace]
  refine ⟨92370781164898927651064467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123161041553198570201419289 92370781164898927651064467)
  ·
    refine ⟨138556171747348391476596701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92370781164898927651064467 138556171747348391476596701)
    ·
      refine ⟨51958564405255646803723763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 138556171747348391476596701 51958564405255646803723763)
      ·
        refine ⟨77937846607883470205585645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51958564405255646803723763 77937846607883470205585645)
        ·
          refine ⟨29226692477956301327094617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77937846607883470205585645 29226692477956301327094617)
          ·
            refine ⟨21920019358467225995320963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29226692477956301327094617 21920019358467225995320963)
            ·
              refine ⟨32880029037700838992981445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21920019358467225995320963 32880029037700838992981445)
              ·
                refine ⟨6165005444568907311184021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32880029037700838992981445 6165005444568907311184021)
                ·
                  refine ⟨288984630214167530211751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6165005444568907311184021 288984630214167530211751)
                  ·
                    rfl

theorem cell23_5065160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 4, 6].length) (baseStart_5065160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5065160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5065160 prefixEnd_5065160 := by exact prefixLift 5065160
  have htrace : WordTrace (prefixWord ++ tailWord_5065160) baseStart_5065160 baseEnd_5065160 := by
    simpa [prefixWord, tailWord_5065160, baseEnd_5065160] using wordTrace_append hprefix tailTrace_5065160
  have hstable : (prefixWord ++ tailWord_5065160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5065160).length < 2 ^ (prefixWord ++ tailWord_5065160).sum := by decide
  have hdescent : baseEnd_5065160 < baseStart_5065160 := by decide
  rcases family_descends (prefixWord ++ tailWord_5065160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5065163 : List Nat := [1, 1, 1, 1, 3, 3, 1, 3, 1, 2, 6]
def baseStart_5065163 : Nat := 118140960795 + 5065163 * 2 ^ 59
def prefixEnd_5065163 : Nat := 4983230072969 + 3 ^ 40 * 5065163 * 2
def baseEnd_5065163 : Nat := 2600863212369471260168245

theorem tailTrace_5065163 : CollatzResearch.WordTrace tailWord_5065163 prefixEnd_5065163 2600863212369471260168245 := by
  unfold tailWord_5065163
  simp only [CollatzResearch.WordTrace]
  refine ⟨184741671748786986814488143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123161114499191324542992095 184741671748786986814488143)
  ·
    refine ⟨277112507623180480221732215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184741671748786986814488143 277112507623180480221732215)
    ·
      refine ⟨415668761434770720332598323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 277112507623180480221732215 415668761434770720332598323)
      ·
        refine ⟨623503142152156080498897485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 415668761434770720332598323 623503142152156080498897485)
        ·
          refine ⟨233813678307058530187086557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 623503142152156080498897485 233813678307058530187086557)
          ·
            refine ⟨87680129365146948820157459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 233813678307058530187086557 87680129365146948820157459)
            ·
              refine ⟨131520194047720423230236189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87680129365146948820157459 131520194047720423230236189)
              ·
                refine ⟨49320072767895158711338571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 131520194047720423230236189 49320072767895158711338571)
                ·
                  refine ⟨73980109151842738067007857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49320072767895158711338571 73980109151842738067007857)
                  ·
                    refine ⟨55485081863882053550255893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 73980109151842738067007857 55485081863882053550255893)
                    ·
                      refine ⟨2600863212369471260168245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 55485081863882053550255893 2600863212369471260168245)
                      ·
                        rfl

theorem cell23_5065163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 3, 1, 2, 6].length) (baseStart_5065163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5065163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5065163 prefixEnd_5065163 := by exact prefixLift 5065163
  have htrace : WordTrace (prefixWord ++ tailWord_5065163) baseStart_5065163 baseEnd_5065163 := by
    simpa [prefixWord, tailWord_5065163, baseEnd_5065163] using wordTrace_append hprefix tailTrace_5065163
  have hstable : (prefixWord ++ tailWord_5065163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5065163).length < 2 ^ (prefixWord ++ tailWord_5065163).sum := by decide
  have hdescent : baseEnd_5065163 < baseStart_5065163 := by decide
  rcases family_descends (prefixWord ++ tailWord_5065163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5065210 : List Nat := [3, 1, 1, 1, 1, 2, 2, 2, 5, 1, 4]
def baseStart_5065210 : Nat := 118140960795 + 5065210 * 2 ^ 59
def prefixEnd_5065210 : Nat := 4983230072969 + 3 ^ 40 * 5065210 * 2
def baseEnd_5065210 : Nat := 2600887345960232576280529

theorem tailTrace_5065210 : CollatzResearch.WordTrace tailWord_5065210 prefixEnd_5065210 2600887345960232576280529 := by
  unfold tailWord_5065210
  simp only [CollatzResearch.WordTrace]
  refine ⟨46185846494904178460362271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123162257319744475894299389 46185846494904178460362271)
  ·
    refine ⟨69278769742356267690543407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46185846494904178460362271 69278769742356267690543407)
    ·
      refine ⟨103918154613534401535815111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69278769742356267690543407 103918154613534401535815111)
      ·
        refine ⟨155877231920301602303722667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103918154613534401535815111 155877231920301602303722667)
        ·
          refine ⟨233815847880452403455584001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155877231920301602303722667 233815847880452403455584001)
          ·
            refine ⟨175361885910339302591688001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 233815847880452403455584001 175361885910339302591688001)
            ·
              refine ⟨131521414432754476943766001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 175361885910339302591688001 131521414432754476943766001)
              ·
                refine ⟨98641060824565857707824501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 131521414432754476943766001 98641060824565857707824501)
                ·
                  refine ⟨9247599452303049160108547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 98641060824565857707824501 9247599452303049160108547)
                  ·
                    refine ⟨13871399178454573740162821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9247599452303049160108547 13871399178454573740162821)
                    ·
                      refine ⟨2600887345960232576280529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13871399178454573740162821 2600887345960232576280529)
                      ·
                        rfl

theorem cell23_5065210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 2, 5, 1, 4].length) (baseStart_5065210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5065210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5065210 prefixEnd_5065210 := by exact prefixLift 5065210
  have htrace : WordTrace (prefixWord ++ tailWord_5065210) baseStart_5065210 baseEnd_5065210 := by
    simpa [prefixWord, tailWord_5065210, baseEnd_5065210] using wordTrace_append hprefix tailTrace_5065210
  have hstable : (prefixWord ++ tailWord_5065210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5065210).length < 2 ^ (prefixWord ++ tailWord_5065210).sum := by decide
  have hdescent : baseEnd_5065210 < baseStart_5065210 := by decide
  rcases family_descends (prefixWord ++ tailWord_5065210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5065244 : List Nat := [2, 2, 3, 1, 2, 3, 2, 2, 1, 1, 4]
def baseStart_5065244 : Nat := 118140960795 + 5065244 * 2 ^ 59
def prefixEnd_5065244 : Nat := 4983230072969 + 3 ^ 40 * 5065244 * 2
def baseEnd_5065244 : Nat := 2600904804302485443255373

theorem tailTrace_5065244 : CollatzResearch.WordTrace tailWord_5065244 prefixEnd_5065244 2600904804302485443255373 := by
  unfold tailWord_5065244
  simp only [CollatzResearch.WordTrace]
  refine ⟨92372313030746768824093393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123163084040995691765457857 92372313030746768824093393)
  ·
    refine ⟨69279234773060076618070045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92372313030746768824093393 69279234773060076618070045)
    ·
      refine ⟨25979713039897528731776267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69279234773060076618070045 25979713039897528731776267)
      ·
        refine ⟨38969569559846293097664401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25979713039897528731776267 38969569559846293097664401)
        ·
          refine ⟨29227177169884719823248301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38969569559846293097664401 29227177169884719823248301)
          ·
            refine ⟨10960191438706769933718113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29227177169884719823248301 10960191438706769933718113)
            ·
              refine ⟨8220143579030077450288585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10960191438706769933718113 8220143579030077450288585)
              ·
                refine ⟨6165107684272558087716439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8220143579030077450288585 6165107684272558087716439)
                ·
                  refine ⟨9247661526408837131574659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6165107684272558087716439 9247661526408837131574659)
                  ·
                    refine ⟨13871492289613255697361989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9247661526408837131574659 13871492289613255697361989)
                    ·
                      refine ⟨2600904804302485443255373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13871492289613255697361989 2600904804302485443255373)
                      ·
                        rfl

theorem cell23_5065244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 2, 2, 1, 1, 4].length) (baseStart_5065244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5065244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5065244 prefixEnd_5065244 := by exact prefixLift 5065244
  have htrace : WordTrace (prefixWord ++ tailWord_5065244) baseStart_5065244 baseEnd_5065244 := by
    simpa [prefixWord, tailWord_5065244, baseEnd_5065244] using wordTrace_append hprefix tailTrace_5065244
  have hstable : (prefixWord ++ tailWord_5065244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5065244).length < 2 ^ (prefixWord ++ tailWord_5065244).sum := by decide
  have hdescent : baseEnd_5065244 < baseStart_5065244 := by decide
  rcases family_descends (prefixWord ++ tailWord_5065244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5065337 : List Nat := [1, 2, 1, 3, 3, 2, 1, 1, 2, 4, 3]
def baseStart_5065337 : Nat := 118140960795 + 5065337 * 2 ^ 59
def prefixEnd_5065337 : Nat := 4983230072969 + 3 ^ 40 * 5065337 * 2
def baseEnd_5065337 : Nat := 2600952558003353579392445

theorem tailTrace_5065337 : CollatzResearch.WordTrace tailWord_5065337 prefixEnd_5065337 2600952558003353579392445 := by
  unfold tailWord_5065337
  simp only [CollatzResearch.WordTrace]
  refine ⟨184748018050156614531322265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123165345366771076354214843 184748018050156614531322265)
  ·
    refine ⟨138561013537617460898491699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184748018050156614531322265 138561013537617460898491699)
    ·
      refine ⟨207841520306426191347737549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138561013537617460898491699 207841520306426191347737549)
      ·
        refine ⟨77940570114909821755401581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 207841520306426191347737549 77940570114909821755401581)
        ·
          refine ⟨29227713793091183158275593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77940570114909821755401581 29227713793091183158275593)
          ·
            refine ⟨21920785344818387368706695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29227713793091183158275593 21920785344818387368706695)
            ·
              refine ⟨32881178017227581053060043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21920785344818387368706695 32881178017227581053060043)
              ·
                refine ⟨49321767025841371579590065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32881178017227581053060043 49321767025841371579590065)
                ·
                  refine ⟨36991325269381028684692549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49321767025841371579590065 36991325269381028684692549)
                  ·
                    refine ⟨6935873488008942878379853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36991325269381028684692549 6935873488008942878379853)
                    ·
                      refine ⟨2600952558003353579392445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6935873488008942878379853 2600952558003353579392445)
                      ·
                        rfl

theorem cell23_5065337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 1, 2, 4, 3].length) (baseStart_5065337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5065337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5065337 prefixEnd_5065337 := by exact prefixLift 5065337
  have htrace : WordTrace (prefixWord ++ tailWord_5065337) baseStart_5065337 baseEnd_5065337 := by
    simpa [prefixWord, tailWord_5065337, baseEnd_5065337] using wordTrace_append hprefix tailTrace_5065337
  have hstable : (prefixWord ++ tailWord_5065337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5065337).length < 2 ^ (prefixWord ++ tailWord_5065337).sum := by decide
  have hdescent : baseEnd_5065337 < baseStart_5065337 := by decide
  rcases family_descends (prefixWord ++ tailWord_5065337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5065351 : List Nat := [1, 1, 4, 2, 1, 2, 1, 5, 2, 2, 2]
def baseStart_5065351 : Nat := 118140960795 + 5065351 * 2 ^ 59
def prefixEnd_5065351 : Nat := 4983230072969 + 3 ^ 40 * 5065351 * 2
def baseEnd_5065351 : Nat := 2600959746732516524617381

theorem tailTrace_5065351 : CollatzResearch.WordTrace tailWord_5065351 prefixEnd_5065351 2600959746732516524617381 := by
  unfold tailWord_5065351
  simp only [CollatzResearch.WordTrace]
  refine ⟨184748528672105894922331907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123165685781403929948221271 184748528672105894922331907)
  ·
    refine ⟨277122793008158842383497861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184748528672105894922331907 277122793008158842383497861)
    ·
      refine ⟨51960523689029782946905849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 277122793008158842383497861 51960523689029782946905849)
      ·
        refine ⟨38970392766772337210179387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51960523689029782946905849 38970392766772337210179387)
        ·
          refine ⟨58455589150158505815269081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38970392766772337210179387 58455589150158505815269081)
          ·
            refine ⟨43841691862618879361451811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58455589150158505815269081 43841691862618879361451811)
            ·
              refine ⟨65762537793928319042177717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43841691862618879361451811 65762537793928319042177717)
              ·
                refine ⟨6165237918180779910204161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 65762537793928319042177717 6165237918180779910204161)
                ·
                  refine ⟨4623928438635584932653121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6165237918180779910204161 4623928438635584932653121)
                  ·
                    refine ⟨3467946328976688699489841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4623928438635584932653121 3467946328976688699489841)
                    ·
                      refine ⟨2600959746732516524617381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3467946328976688699489841 2600959746732516524617381)
                      ·
                        rfl

theorem cell23_5065351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 5, 2, 2, 2].length) (baseStart_5065351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5065351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5065351 prefixEnd_5065351 := by exact prefixLift 5065351
  have htrace : WordTrace (prefixWord ++ tailWord_5065351) baseStart_5065351 baseEnd_5065351 := by
    simpa [prefixWord, tailWord_5065351, baseEnd_5065351] using wordTrace_append hprefix tailTrace_5065351
  have hstable : (prefixWord ++ tailWord_5065351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5065351).length < 2 ^ (prefixWord ++ tailWord_5065351).sum := by decide
  have hdescent : baseEnd_5065351 < baseStart_5065351 := by decide
  rcases family_descends (prefixWord ++ tailWord_5065351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5065367 : List Nat := [1, 1, 3, 3, 2, 1, 1, 2, 1, 5, 3]
def baseStart_5065367 : Nat := 118140960795 + 5065367 * 2 ^ 59
def prefixEnd_5065367 : Nat := 4983230072969 + 3 ^ 40 * 5065367 * 2
def baseEnd_5065367 : Nat := 2600967962422988462017307

theorem tailTrace_5065367 : CollatzResearch.WordTrace tailWord_5065367 prefixEnd_5065367 2600967962422988462017307 := by
  unfold tailWord_5065367
  simp only [CollatzResearch.WordTrace]
  refine ⟨184749112240047929654914355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123166074826698619769942903 184749112240047929654914355)
  ·
    refine ⟨277123668360071894482371533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184749112240047929654914355 277123668360071894482371533)
    ·
      refine ⟨103921375635026960430889325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 277123668360071894482371533 103921375635026960430889325)
      ·
        refine ⟨38970515863135110161583497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 103921375635026960430889325 38970515863135110161583497)
        ·
          refine ⟨29227886897351332621187623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38970515863135110161583497 29227886897351332621187623)
          ·
            refine ⟨43841830346026998931781435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29227886897351332621187623 43841830346026998931781435)
            ·
              refine ⟨65762745519040498397672153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43841830346026998931781435 65762745519040498397672153)
              ·
                refine ⟨49322059139280373798254115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65762745519040498397672153 49322059139280373798254115)
                ·
                  refine ⟨73983088708920560697381173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49322059139280373798254115 73983088708920560697381173)
                  ·
                    refine ⟨6935914566461302565379485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 73983088708920560697381173 6935914566461302565379485)
                    ·
                      refine ⟨2600967962422988462017307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6935914566461302565379485 2600967962422988462017307)
                      ·
                        rfl

theorem cell23_5065367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 2, 1, 5, 3].length) (baseStart_5065367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5065367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5065367 prefixEnd_5065367 := by exact prefixLift 5065367
  have htrace : WordTrace (prefixWord ++ tailWord_5065367) baseStart_5065367 baseEnd_5065367 := by
    simpa [prefixWord, tailWord_5065367, baseEnd_5065367] using wordTrace_append hprefix tailTrace_5065367
  have hstable : (prefixWord ++ tailWord_5065367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5065367).length < 2 ^ (prefixWord ++ tailWord_5065367).sum := by decide
  have hdescent : baseEnd_5065367 < baseStart_5065367 := by decide
  rcases family_descends (prefixWord ++ tailWord_5065367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5065407 : List Nat := [1, 1, 2, 2, 2, 4, 1, 2, 1, 3, 4]
def baseStart_5065407 : Nat := 118140960795 + 5065407 * 2 ^ 59
def prefixEnd_5065407 : Nat := 4983230072969 + 3 ^ 40 * 5065407 * 2
def baseEnd_5065407 : Nat := 2600988501649168305517123

theorem tailTrace_5065407 : CollatzResearch.WordTrace tailWord_5065407 prefixEnd_5065407 2600988501649168305517123 := by
  unfold tailWord_5065407
  simp only [CollatzResearch.WordTrace]
  refine ⟨184750571159903016486370475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123167047439935344324246983 184750571159903016486370475)
  ·
    refine ⟨277125856739854524729555713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184750571159903016486370475 277125856739854524729555713)
    ·
      refine ⟨207844392554890893547166785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 277125856739854524729555713 207844392554890893547166785)
      ·
        refine ⟨155883294416168170160375089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 207844392554890893547166785 155883294416168170160375089)
        ·
          refine ⟨116912470812126127620281317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 155883294416168170160375089 116912470812126127620281317)
          ·
            refine ⟨21921088277273648928802747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 116912470812126127620281317 21921088277273648928802747)
            ·
              refine ⟨32881632415910473393204121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21921088277273648928802747 32881632415910473393204121)
              ·
                refine ⟨24661224311932855044903091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32881632415910473393204121 24661224311932855044903091)
                ·
                  refine ⟨36991836467899282567354637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24661224311932855044903091 36991836467899282567354637)
                  ·
                    refine ⟨13871938675462230962757989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36991836467899282567354637 13871938675462230962757989)
                    ·
                      refine ⟨2600988501649168305517123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13871938675462230962757989 2600988501649168305517123)
                      ·
                        rfl

theorem cell23_5065407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 2, 1, 3, 4].length) (baseStart_5065407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5065407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5065407 prefixEnd_5065407 := by exact prefixLift 5065407
  have htrace : WordTrace (prefixWord ++ tailWord_5065407) baseStart_5065407 baseEnd_5065407 := by
    simpa [prefixWord, tailWord_5065407, baseEnd_5065407] using wordTrace_append hprefix tailTrace_5065407
  have hstable : (prefixWord ++ tailWord_5065407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5065407).length < 2 ^ (prefixWord ++ tailWord_5065407).sum := by decide
  have hdescent : baseEnd_5065407 < baseStart_5065407 := by decide
  rcases family_descends (prefixWord ++ tailWord_5065407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5065444 : List Nat := [2, 3, 1, 1, 1, 4, 1, 1, 4, 2, 3]
def baseStart_5065444 : Nat := 118140960795 + 5065444 * 2 ^ 59
def prefixEnd_5065444 : Nat := 4983230072969 + 3 ^ 40 * 5065444 * 2
def baseEnd_5065444 : Nat := 2601007500433384660754453

theorem tailTrace_5065444 : CollatzResearch.WordTrace tailWord_5065444 prefixEnd_5065444 2601007500433384660754453 := by
  unfold tailWord_5065444
  simp only [CollatzResearch.WordTrace]
  refine ⟨92375960330384485902733693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123167947107179314536978257 92375960330384485902733693)
  ·
    refine ⟨34640985123894182213525135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92375960330384485902733693 34640985123894182213525135)
    ·
      refine ⟨51961477685841273320287703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34640985123894182213525135 51961477685841273320287703)
      ·
        refine ⟨77942216528761909980431555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51961477685841273320287703 77942216528761909980431555)
        ·
          refine ⟨116913324793142864970647333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77942216528761909980431555 116913324793142864970647333)
          ·
            refine ⟨21921248398714287181996375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 116913324793142864970647333 21921248398714287181996375)
            ·
              refine ⟨32881872598071430772994563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21921248398714287181996375 32881872598071430772994563)
              ·
                refine ⟨49322808897107146159491845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32881872598071430772994563 49322808897107146159491845)
                ·
                  refine ⟨9248026668207589904904721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49322808897107146159491845 9248026668207589904904721)
                  ·
                    refine ⟨6936020001155692428678541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9248026668207589904904721 6936020001155692428678541)
                    ·
                      refine ⟨2601007500433384660754453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6936020001155692428678541 2601007500433384660754453)
                      ·
                        rfl

theorem cell23_5065444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 1, 4, 2, 3].length) (baseStart_5065444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5065444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5065444 prefixEnd_5065444 := by exact prefixLift 5065444
  have htrace : WordTrace (prefixWord ++ tailWord_5065444) baseStart_5065444 baseEnd_5065444 := by
    simpa [prefixWord, tailWord_5065444, baseEnd_5065444] using wordTrace_append hprefix tailTrace_5065444
  have hstable : (prefixWord ++ tailWord_5065444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5065444).length < 2 ^ (prefixWord ++ tailWord_5065444).sum := by decide
  have hdescent : baseEnd_5065444 < baseStart_5065444 := by decide
  rcases family_descends (prefixWord ++ tailWord_5065444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5065507 : List Nat := [1, 1, 1, 4, 2, 1, 1, 1, 5, 6]
def baseStart_5065507 : Nat := 118140960795 + 5065507 * 2 ^ 59
def prefixEnd_5065507 : Nat := 4983230072969 + 3 ^ 40 * 5065507 * 2
def baseEnd_5065507 : Nat := 867013283238205971422221

theorem tailTrace_5065507 : CollatzResearch.WordTrace tailWord_5065507 prefixEnd_5065507 867013283238205971422221 := by
  unfold tailWord_5065507
  simp only [CollatzResearch.WordTrace]
  refine ⟨184754218459540733565010775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123169478973027155710007183 184754218459540733565010775)
  ·
    refine ⟨277131327689311100347516163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184754218459540733565010775 277131327689311100347516163)
    ·
      refine ⟨415696991533966650521274245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 277131327689311100347516163 415696991533966650521274245)
      ·
        refine ⟨77943185912618746972738921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 415696991533966650521274245 77943185912618746972738921)
        ·
          refine ⟨58457389434464060229554191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77943185912618746972738921 58457389434464060229554191)
          ·
            refine ⟨87686084151696090344331287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58457389434464060229554191 87686084151696090344331287)
            ·
              refine ⟨131529126227544135516496931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87686084151696090344331287 131529126227544135516496931)
              ·
                refine ⟨197293689341316203274745397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 131529126227544135516496931 197293689341316203274745397)
                ·
                  refine ⟨18496283375748394057007381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 197293689341316203274745397 18496283375748394057007381)
                  ·
                    refine ⟨867013283238205971422221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18496283375748394057007381 867013283238205971422221)
                    ·
                      rfl

theorem cell23_5065507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 1, 5, 6].length) (baseStart_5065507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5065507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5065507 prefixEnd_5065507 := by exact prefixLift 5065507
  have htrace : WordTrace (prefixWord ++ tailWord_5065507) baseStart_5065507 baseEnd_5065507 := by
    simpa [prefixWord, tailWord_5065507, baseEnd_5065507] using wordTrace_append hprefix tailTrace_5065507
  have hstable : (prefixWord ++ tailWord_5065507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5065507).length < 2 ^ (prefixWord ++ tailWord_5065507).sum := by decide
  have hdescent : baseEnd_5065507 < baseStart_5065507 := by decide
  rcases family_descends (prefixWord ++ tailWord_5065507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5065544 : List Nat := [2, 1, 3, 1, 1, 3, 1, 4, 1, 2, 4]
def baseStart_5065544 : Nat := 118140960795 + 5065544 * 2 ^ 59
def prefixEnd_5065544 : Nat := 4983230072969 + 3 ^ 40 * 5065544 * 2
def baseEnd_5065544 : Nat := 2601058848498834269503993

theorem tailTrace_5065544 : CollatzResearch.WordTrace tailWord_5065544 prefixEnd_5065544 2601058848498834269503993 := by
  unfold tailWord_5065544
  simp only [CollatzResearch.WordTrace]
  refine ⟨92377783980203344442053843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123170378640271125922738457 92377783980203344442053843)
  ·
    refine ⟨138566675970305016663080765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92377783980203344442053843 138566675970305016663080765)
    ·
      refine ⟨51962503488864381248655287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 138566675970305016663080765 51962503488864381248655287)
      ·
        refine ⟨77943755233296571872982931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51962503488864381248655287 77943755233296571872982931)
        ·
          refine ⟨116915632849944857809474397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77943755233296571872982931 116915632849944857809474397)
          ·
            refine ⟨43843362318729321678552899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 116915632849944857809474397 43843362318729321678552899)
            ·
              refine ⟨65765043478093982517829349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43843362318729321678552899 65765043478093982517829349)
              ·
                refine ⟨12330945652142621722093003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 65765043478093982517829349 12330945652142621722093003)
                ·
                  refine ⟨18496418478213932583139505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12330945652142621722093003 18496418478213932583139505)
                  ·
                    refine ⟨13872313858660449437354629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18496418478213932583139505 13872313858660449437354629)
                    ·
                      refine ⟨2601058848498834269503993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13872313858660449437354629 2601058848498834269503993)
                      ·
                        rfl

theorem cell23_5065544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 4, 1, 2, 4].length) (baseStart_5065544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5065544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5065544 prefixEnd_5065544 := by exact prefixLift 5065544
  have htrace : WordTrace (prefixWord ++ tailWord_5065544) baseStart_5065544 baseEnd_5065544 := by
    simpa [prefixWord, tailWord_5065544, baseEnd_5065544] using wordTrace_append hprefix tailTrace_5065544
  have hstable : (prefixWord ++ tailWord_5065544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5065544).length < 2 ^ (prefixWord ++ tailWord_5065544).sum := by decide
  have hdescent : baseEnd_5065544 < baseStart_5065544 := by decide
  rcases family_descends (prefixWord ++ tailWord_5065544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5065548 : List Nat := [2, 2, 1, 3, 3, 1, 4, 1, 1, 1, 4]
def baseStart_5065548 : Nat := 118140960795 + 5065548 * 2 ^ 59
def prefixEnd_5065548 : Nat := 4983230072969 + 3 ^ 40 * 5065548 * 2
def baseEnd_5065548 : Nat := 2601060902421452253853975

theorem tailTrace_5065548 : CollatzResearch.WordTrace tailWord_5065548 prefixEnd_5065548 2601060902421452253853975 := by
  unfold tailWord_5065548
  simp only [CollatzResearch.WordTrace]
  refine ⟨92377856926196098783626649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123170475901594798378168865 92377856926196098783626649)
  ·
    refine ⟨69283392694647074087719987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92377856926196098783626649 69283392694647074087719987)
    ·
      refine ⟨103925089041970611131579981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69283392694647074087719987 103925089041970611131579981)
      ·
        refine ⟨38971908390738979174342493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 103925089041970611131579981 38971908390738979174342493)
        ·
          refine ⟨14614465646527117190378435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38971908390738979174342493 14614465646527117190378435)
          ·
            refine ⟨21921698469790675785567653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14614465646527117190378435 21921698469790675785567653)
            ·
              refine ⟨4110318463085751709793935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21921698469790675785567653 4110318463085751709793935)
              ·
                refine ⟨6165477694628627564690903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4110318463085751709793935 6165477694628627564690903)
                ·
                  refine ⟨9248216541942941347036355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6165477694628627564690903 9248216541942941347036355)
                  ·
                    refine ⟨13872324812914412020554533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9248216541942941347036355 13872324812914412020554533)
                    ·
                      refine ⟨2601060902421452253853975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13872324812914412020554533 2601060902421452253853975)
                      ·
                        rfl

theorem cell23_5065548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 4, 1, 1, 1, 4].length) (baseStart_5065548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5065548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5065548 prefixEnd_5065548 := by exact prefixLift 5065548
  have htrace : WordTrace (prefixWord ++ tailWord_5065548) baseStart_5065548 baseEnd_5065548 := by
    simpa [prefixWord, tailWord_5065548, baseEnd_5065548] using wordTrace_append hprefix tailTrace_5065548
  have hstable : (prefixWord ++ tailWord_5065548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5065548).length < 2 ^ (prefixWord ++ tailWord_5065548).sum := by decide
  have hdescent : baseEnd_5065548 < baseStart_5065548 := by decide
  rcases family_descends (prefixWord ++ tailWord_5065548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5065591 : List Nat := [1, 1, 3, 1, 1, 2, 1, 5, 3, 3, 2]
def baseStart_5065591 : Nat := 118140960795 + 5065591 * 2 ^ 59
def prefixEnd_5065591 : Nat := 4983230072969 + 3 ^ 40 * 5065591 * 2
def baseEnd_5065591 : Nat := 2601082982089595585616277

theorem tailTrace_5065591 : CollatzResearch.WordTrace tailWord_5065591 prefixEnd_5065591 2601082982089595585616277 := by
  unfold tailWord_5065591
  simp only [CollatzResearch.WordTrace]
  refine ⟨184757282191236415911068627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123171521460824277274045751 184757282191236415911068627)
  ·
    refine ⟨277135923286854623866602941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184757282191236415911068627 277135923286854623866602941)
    ·
      refine ⟨103925971232570483949976103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 277135923286854623866602941 103925971232570483949976103)
      ·
        refine ⟨155888956848855725924964155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103925971232570483949976103 155888956848855725924964155)
        ·
          refine ⟨233833435273283588887446233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155888956848855725924964155 233833435273283588887446233)
          ·
            refine ⟨175375076454962691665584675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 233833435273283588887446233 175375076454962691665584675)
            ·
              refine ⟨263062614682444037498377013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 175375076454962691665584675 263062614682444037498377013)
              ·
                refine ⟨24662120126479128515472845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 263062614682444037498377013 24662120126479128515472845)
                ·
                  refine ⟨9248295047429673193302317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24662120126479128515472845 9248295047429673193302317)
                  ·
                    refine ⟨3468110642786127447488369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9248295047429673193302317 3468110642786127447488369)
                    ·
                      refine ⟨2601082982089595585616277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3468110642786127447488369 2601082982089595585616277)
                      ·
                        rfl

theorem cell23_5065591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 5, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 5, 3, 3, 2].length) (baseStart_5065591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5065591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5065591 prefixEnd_5065591 := by exact prefixLift 5065591
  have htrace : WordTrace (prefixWord ++ tailWord_5065591) baseStart_5065591 baseEnd_5065591 := by
    simpa [prefixWord, tailWord_5065591, baseEnd_5065591] using wordTrace_append hprefix tailTrace_5065591
  have hstable : (prefixWord ++ tailWord_5065591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5065591).length < 2 ^ (prefixWord ++ tailWord_5065591).sum := by decide
  have hdescent : baseEnd_5065591 < baseStart_5065591 := by decide
  rcases family_descends (prefixWord ++ tailWord_5065591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5065604 : List Nat := [2, 3, 2, 1, 1, 1, 1, 2, 1, 5, 4]
def baseStart_5065604 : Nat := 118140960795 + 5065604 * 2 ^ 59
def prefixEnd_5065604 : Nat := 4983230072969 + 3 ^ 40 * 5065604 * 2
def baseEnd_5065604 : Nat := 2601089657338104034753717

theorem tailTrace_5065604 : CollatzResearch.WordTrace tailWord_5065604 prefixEnd_5065604 2601089657338104034753717 := by
  unfold tailWord_5065604
  simp only [CollatzResearch.WordTrace]
  refine ⟨92378878170094659565645933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123171837560126212754194577 92378878170094659565645933)
  ·
    refine ⟨34642079313785497337117225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92378878170094659565645933 34642079313785497337117225)
    ·
      refine ⟨25981559485339123002837919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34642079313785497337117225 25981559485339123002837919)
      ·
        refine ⟨38972339228008684504256879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25981559485339123002837919 38972339228008684504256879)
        ·
          refine ⟨58458508842013026756385319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38972339228008684504256879 58458508842013026756385319)
          ·
            refine ⟨87687763263019540134577979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58458508842013026756385319 87687763263019540134577979)
            ·
              refine ⟨131531644894529310201866969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87687763263019540134577979 131531644894529310201866969)
              ·
                refine ⟨98648733670896982651400227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 131531644894529310201866969 98648733670896982651400227)
                ·
                  refine ⟨147973100506345473977100341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 98648733670896982651400227 147973100506345473977100341)
                  ·
                    refine ⟨13872478172469888185353157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 147973100506345473977100341 13872478172469888185353157)
                    ·
                      refine ⟨2601089657338104034753717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13872478172469888185353157 2601089657338104034753717)
                      ·
                        rfl

theorem cell23_5065604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 2, 1, 5, 4].length) (baseStart_5065604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5065604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5065604 prefixEnd_5065604 := by exact prefixLift 5065604
  have htrace : WordTrace (prefixWord ++ tailWord_5065604) baseStart_5065604 baseEnd_5065604 := by
    simpa [prefixWord, tailWord_5065604, baseEnd_5065604] using wordTrace_append hprefix tailTrace_5065604
  have hstable : (prefixWord ++ tailWord_5065604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5065604).length < 2 ^ (prefixWord ++ tailWord_5065604).sum := by decide
  have hdescent : baseEnd_5065604 < baseStart_5065604 := by decide
  rcases family_descends (prefixWord ++ tailWord_5065604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5065672 : List Nat := [2, 1, 3, 1, 5, 1, 2, 2, 2, 2, 2]
def baseStart_5065672 : Nat := 118140960795 + 5065672 * 2 ^ 59
def prefixEnd_5065672 : Nat := 4983230072969 + 3 ^ 40 * 5065672 * 2
def baseEnd_5065672 : Nat := 2601124574022609768703405

theorem tailTrace_5065672 : CollatzResearch.WordTrace tailWord_5065672 prefixEnd_5065672 2601124574022609768703405 := by
  unfold tailWord_5065672
  simp only [CollatzResearch.WordTrace]
  refine ⟨92380118251971483372383635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123173491002628644496511513 92380118251971483372383635)
  ·
    refine ⟨138570177377957225058575453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92380118251971483372383635 138570177377957225058575453)
    ·
      refine ⟨51963816516733959396965795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 138570177377957225058575453 51963816516733959396965795)
      ·
        refine ⟨77945724775100939095448693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51963816516733959396965795 77945724775100939095448693)
        ·
          refine ⟨7307411697665713040198315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 77945724775100939095448693 7307411697665713040198315)
          ·
            refine ⟨10961117546498569560297473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7307411697665713040198315 10961117546498569560297473)
            ·
              refine ⟨8220838159873927170223105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10961117546498569560297473 8220838159873927170223105)
              ·
                refine ⟨6165628619905445377667329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8220838159873927170223105 6165628619905445377667329)
                ·
                  refine ⟨4624221464929084033250497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6165628619905445377667329 4624221464929084033250497)
                  ·
                    refine ⟨3468166098696813024937873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4624221464929084033250497 3468166098696813024937873)
                    ·
                      refine ⟨2601124574022609768703405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3468166098696813024937873 2601124574022609768703405)
                      ·
                        rfl

theorem cell23_5065672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 2, 2, 2, 2, 2].length) (baseStart_5065672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5065672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5065672 prefixEnd_5065672 := by exact prefixLift 5065672
  have htrace : WordTrace (prefixWord ++ tailWord_5065672) baseStart_5065672 baseEnd_5065672 := by
    simpa [prefixWord, tailWord_5065672, baseEnd_5065672] using wordTrace_append hprefix tailTrace_5065672
  have hstable : (prefixWord ++ tailWord_5065672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5065672).length < 2 ^ (prefixWord ++ tailWord_5065672).sum := by decide
  have hdescent : baseEnd_5065672 < baseStart_5065672 := by decide
  rcases family_descends (prefixWord ++ tailWord_5065672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5065674 : List Nat := [3, 1, 2, 1, 2, 1, 1, 2, 3, 7]
def baseStart_5065674 : Nat := 118140960795 + 5065674 * 2 ^ 59
def prefixEnd_5065674 : Nat := 4983230072969 + 3 ^ 40 * 5065674 * 2
def baseEnd_5065674 : Nat := 867041866994639586959465

theorem tailTrace_5065674 : CollatzResearch.WordTrace tailWord_5065674 prefixEnd_5065674 867041866994639586959465 := by
  unfold tailWord_5065674
  simp only [CollatzResearch.WordTrace]
  refine ⟨46190077362483930271585019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123173539633290480724226717 46190077362483930271585019)
  ·
    refine ⟨69285116043725895407377529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46190077362483930271585019 69285116043725895407377529)
    ·
      refine ⟨51963837032794421555533147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69285116043725895407377529 51963837032794421555533147)
      ·
        refine ⟨77945755549191632333299721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51963837032794421555533147 77945755549191632333299721)
        ·
          refine ⟨58459316661893724249974791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77945755549191632333299721 58459316661893724249974791)
          ·
            refine ⟨87688974992840586374962187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58459316661893724249974791 87688974992840586374962187)
            ·
              refine ⟨131533462489260879562443281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87688974992840586374962187 131533462489260879562443281)
              ·
                refine ⟨98650096866945659671832461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 131533462489260879562443281 98650096866945659671832461)
                ·
                  refine ⟨36993786325104622376937173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 98650096866945659671832461 36993786325104622376937173)
                  ·
                    refine ⟨867041866994639586959465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36993786325104622376937173 867041866994639586959465)
                    ·
                      rfl

theorem cell23_5065674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 2, 3, 7].length) (baseStart_5065674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5065674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5065674 prefixEnd_5065674 := by exact prefixLift 5065674
  have htrace : WordTrace (prefixWord ++ tailWord_5065674) baseStart_5065674 baseEnd_5065674 := by
    simpa [prefixWord, tailWord_5065674, baseEnd_5065674] using wordTrace_append hprefix tailTrace_5065674
  have hstable : (prefixWord ++ tailWord_5065674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5065674).length < 2 ^ (prefixWord ++ tailWord_5065674).sum := by decide
  have hdescent : baseEnd_5065674 < baseStart_5065674 := by decide
  rcases family_descends (prefixWord ++ tailWord_5065674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5065678 : List Nat := [4, 1, 1, 1, 2, 4, 1, 4, 5]
def baseStart_5065678 : Nat := 118140960795 + 5065678 * 2 ^ 59
def prefixEnd_5065678 : Nat := 4983230072969 + 3 ^ 40 * 5065678 * 2
def baseEnd_5065678 : Nat := 289014183878504082803153

theorem tailTrace_5065678 : CollatzResearch.WordTrace tailWord_5065678 prefixEnd_5065678 289014183878504082803153 := by
  unfold tailWord_5065678
  simp only [CollatzResearch.WordTrace]
  refine ⟨23095056917740153721185711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 123173636894614153179657125 23095056917740153721185711)
  ·
    refine ⟨34642585376610230581778567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23095056917740153721185711 34642585376610230581778567)
    ·
      refine ⟨51963878064915345872667851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34642585376610230581778567 51963878064915345872667851)
      ·
        refine ⟨77945817097373018809001777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51963878064915345872667851 77945817097373018809001777)
        ·
          refine ⟨58459362823029764106751333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77945817097373018809001777 58459362823029764106751333)
          ·
            refine ⟨10961130529318080770015875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58459362823029764106751333 10961130529318080770015875)
            ·
              refine ⟨16441695793977121155023813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10961130529318080770015875 16441695793977121155023813)
              ·
                refine ⟨3082817961370710216566965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16441695793977121155023813 3082817961370710216566965)
                ·
                  refine ⟨289014183878504082803153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3082817961370710216566965 289014183878504082803153)
                  ·
                    rfl

theorem cell23_5065678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 4, 5].length) (baseStart_5065678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5065678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5065678 prefixEnd_5065678 := by exact prefixLift 5065678
  have htrace : WordTrace (prefixWord ++ tailWord_5065678) baseStart_5065678 baseEnd_5065678 := by
    simpa [prefixWord, tailWord_5065678, baseEnd_5065678] using wordTrace_append hprefix tailTrace_5065678
  have hstable : (prefixWord ++ tailWord_5065678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5065678).length < 2 ^ (prefixWord ++ tailWord_5065678).sum := by decide
  have hdescent : baseEnd_5065678 < baseStart_5065678 := by decide
  rcases family_descends (prefixWord ++ tailWord_5065678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5065681 : List Nat := [1, 2, 2, 1, 2, 1, 3, 1, 1, 7, 2]
def baseStart_5065681 : Nat := 118140960795 + 5065681 * 2 ^ 59
def prefixEnd_5065681 : Nat := 4983230072969 + 3 ^ 40 * 5065681 * 2
def baseEnd_5065681 : Nat := 2601129195348500233490863

theorem tailTrace_5065681 : CollatzResearch.WordTrace tailWord_5065681 prefixEnd_5065681 2601129195348500233490863 := by
  unfold tailWord_5065681
  simp only [CollatzResearch.WordTrace]
  refine ⟨184760564760910361281844897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123173709840606907521229931 184760564760910361281844897)
  ·
    refine ⟨138570423570682770961383673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184760564760910361281844897 138570423570682770961383673)
    ·
      refine ⟨103927817678012078221037755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138570423570682770961383673 103927817678012078221037755)
      ·
        refine ⟨155891726517018117331556633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103927817678012078221037755 155891726517018117331556633)
        ·
          refine ⟨116918794887763587998667475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 155891726517018117331556633 116918794887763587998667475)
          ·
            refine ⟨175378192331645381998001213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116918794887763587998667475 175378192331645381998001213)
            ·
              refine ⟨65766822124367018249250455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 175378192331645381998001213 65766822124367018249250455)
              ·
                refine ⟨98650233186550527373875683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65766822124367018249250455 98650233186550527373875683)
                ·
                  refine ⟨147975349779825791060813525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 98650233186550527373875683 147975349779825791060813525)
                  ·
                    refine ⟨3468172260464666977987817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 147975349779825791060813525 3468172260464666977987817)
                    ·
                      refine ⟨2601129195348500233490863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3468172260464666977987817 2601129195348500233490863)
                      ·
                        rfl

theorem cell23_5065681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 1, 1, 7, 2].length) (baseStart_5065681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5065681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5065681 prefixEnd_5065681 := by exact prefixLift 5065681
  have htrace : WordTrace (prefixWord ++ tailWord_5065681) baseStart_5065681 baseEnd_5065681 := by
    simpa [prefixWord, tailWord_5065681, baseEnd_5065681] using wordTrace_append hprefix tailTrace_5065681
  have hstable : (prefixWord ++ tailWord_5065681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5065681).length < 2 ^ (prefixWord ++ tailWord_5065681).sum := by decide
  have hdescent : baseEnd_5065681 < baseStart_5065681 := by decide
  rcases family_descends (prefixWord ++ tailWord_5065681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5065711 : List Nat := [1, 1, 2, 1, 4, 4, 1, 1, 1, 3, 4]
def baseStart_5065711 : Nat := 118140960795 + 5065711 * 2 ^ 59
def prefixEnd_5065711 : Nat := 4983230072969 + 3 ^ 40 * 5065711 * 2
def baseEnd_5065711 : Nat := 2601144599768135116115725

theorem tailTrace_5065711 : CollatzResearch.WordTrace tailWord_5065711 prefixEnd_5065711 2601144599768135116115725 := by
  unfold tailWord_5065711
  simp only [CollatzResearch.WordTrace]
  refine ⟨184761658950801676405436987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123174439300534450936957991 184761658950801676405436987)
  ·
    refine ⟨277142488426202514608155481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184761658950801676405436987 277142488426202514608155481)
    ·
      refine ⟨207856866319651885956116611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 277142488426202514608155481 207856866319651885956116611)
      ·
        refine ⟨311785299479477828934174917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 207856866319651885956116611 311785299479477828934174917)
        ·
          refine ⟨58459743652402092925157797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 311785299479477828934174917 58459743652402092925157797)
          ·
            refine ⟨10961201934825392423467087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58459743652402092925157797 10961201934825392423467087)
            ·
              refine ⟨16441802902238088635200631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10961201934825392423467087 16441802902238088635200631)
              ·
                refine ⟨24662704353357132952800947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16441802902238088635200631 24662704353357132952800947)
                ·
                  refine ⟨36994056530035699429201421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24662704353357132952800947 36994056530035699429201421)
                  ·
                    refine ⟨13872771198763387285950533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36994056530035699429201421 13872771198763387285950533)
                    ·
                      refine ⟨2601144599768135116115725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13872771198763387285950533 2601144599768135116115725)
                      ·
                        rfl

theorem cell23_5065711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 1, 1, 3, 4].length) (baseStart_5065711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5065711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5065711 prefixEnd_5065711 := by exact prefixLift 5065711
  have htrace : WordTrace (prefixWord ++ tailWord_5065711) baseStart_5065711 baseEnd_5065711 := by
    simpa [prefixWord, tailWord_5065711, baseEnd_5065711] using wordTrace_append hprefix tailTrace_5065711
  have hstable : (prefixWord ++ tailWord_5065711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5065711).length < 2 ^ (prefixWord ++ tailWord_5065711).sum := by decide
  have hdescent : baseEnd_5065711 < baseStart_5065711 := by decide
  rcases family_descends (prefixWord ++ tailWord_5065711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5065721 : List Nat := [1, 2, 1, 3, 1, 3, 1, 2, 5, 4]
def baseStart_5065721 : Nat := 118140960795 + 5065721 * 2 ^ 59
def prefixEnd_5065721 : Nat := 4983230072969 + 3 ^ 40 * 5065721 * 2
def baseEnd_5065721 : Nat := 867049911524893358996893

theorem tailTrace_5065721 : CollatzResearch.WordTrace tailWord_5065721 prefixEnd_5065721 867049911524893358996893 := by
  unfold tailWord_5065721
  simp only [CollatzResearch.WordTrace]
  refine ⟨184762023680765448113301017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123174682453843632075534011 184762023680765448113301017)
  ·
    refine ⟨138571517760574086084975763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184762023680765448113301017 138571517760574086084975763)
    ·
      refine ⟨207857276640861129127463645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138571517760574086084975763 207857276640861129127463645)
      ·
        refine ⟨77946478740322923422798867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 207857276640861129127463645 77946478740322923422798867)
        ·
          refine ⟨116919718110484385134198301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77946478740322923422798867 116919718110484385134198301)
          ·
            refine ⟨43844894291431644425324363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 116919718110484385134198301 43844894291431644425324363)
            ·
              refine ⟨65767341437147466637986545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43844894291431644425324363 65767341437147466637986545)
              ·
                refine ⟨49325506077860599978489909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65767341437147466637986545 49325506077860599978489909)
                ·
                  refine ⟨4624266194799431247983429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 49325506077860599978489909 4624266194799431247983429)
                  ·
                    refine ⟨867049911524893358996893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4624266194799431247983429 867049911524893358996893)
                    ·
                      rfl

theorem cell23_5065721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 2, 5, 4].length) (baseStart_5065721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5065721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5065721 prefixEnd_5065721 := by exact prefixLift 5065721
  have htrace : WordTrace (prefixWord ++ tailWord_5065721) baseStart_5065721 baseEnd_5065721 := by
    simpa [prefixWord, tailWord_5065721, baseEnd_5065721] using wordTrace_append hprefix tailTrace_5065721
  have hstable : (prefixWord ++ tailWord_5065721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5065721).length < 2 ^ (prefixWord ++ tailWord_5065721).sum := by decide
  have hdescent : baseEnd_5065721 < baseStart_5065721 := by decide
  rcases family_descends (prefixWord ++ tailWord_5065721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5065738 : List Nat := [3, 1, 2, 2, 3, 1, 1, 3, 3, 4]
def baseStart_5065738 : Nat := 118140960795 + 5065738 * 2 ^ 59
def prefixEnd_5065738 : Nat := 4983230072969 + 3 ^ 40 * 5065738 * 2
def baseEnd_5065738 : Nat := 867052821248602170159367

theorem tailTrace_5065738 : CollatzResearch.WordTrace tailWord_5065738 prefixEnd_5065738 867052821248602170159367 := by
  unfold tailWord_5065738
  simp only [CollatzResearch.WordTrace]
  refine ⟨46190660930425965004167467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123175095814469240011113245 46190660930425965004167467)
  ·
    refine ⟨69285991395638947506251201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46190660930425965004167467 69285991395638947506251201)
    ·
      refine ⟨51964493546729210629688401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69285991395638947506251201 51964493546729210629688401)
      ·
        refine ⟨38973370160046907972266301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51964493546729210629688401 38973370160046907972266301)
        ·
          refine ⟨14615013810017590489599863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38973370160046907972266301 14615013810017590489599863)
          ·
            refine ⟨21922520715026385734399795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14615013810017590489599863 21922520715026385734399795)
            ·
              refine ⟨32883781072539578601599693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21922520715026385734399795 32883781072539578601599693)
              ·
                refine ⟨12331417902202341975599885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32883781072539578601599693 12331417902202341975599885)
                ·
                  refine ⟨4624281713325878240849957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12331417902202341975599885 4624281713325878240849957)
                  ·
                    refine ⟨867052821248602170159367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4624281713325878240849957 867052821248602170159367)
                    ·
                      rfl

theorem cell23_5065738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 3, 3, 4].length) (baseStart_5065738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5065738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5065738 prefixEnd_5065738 := by exact prefixLift 5065738
  have htrace : WordTrace (prefixWord ++ tailWord_5065738) baseStart_5065738 baseEnd_5065738 := by
    simpa [prefixWord, tailWord_5065738, baseEnd_5065738] using wordTrace_append hprefix tailTrace_5065738
  have hstable : (prefixWord ++ tailWord_5065738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5065738).length < 2 ^ (prefixWord ++ tailWord_5065738).sum := by decide
  have hdescent : baseEnd_5065738 < baseStart_5065738 := by decide
  rcases family_descends (prefixWord ++ tailWord_5065738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5065781 : List Nat := [1, 3, 3, 1, 1, 1, 1, 2, 5, 5]
def baseStart_5065781 : Nat := 118140960795 + 5065781 * 2 ^ 59
def prefixEnd_5065781 : Nat := 4983230072969 + 3 ^ 40 * 5065781 * 2
def baseEnd_5065781 : Nat := 867060181137983280746801

theorem tailTrace_5065781 : CollatzResearch.WordTrace tailWord_5065781 prefixEnd_5065781 867060181137983280746801 := by
  unfold tailWord_5065781
  simp only [CollatzResearch.WordTrace]
  refine ⟨184764212060548078360485197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123176141373698718906990131 184764212060548078360485197)
  ·
    refine ⟨69286579522705529385181949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 184764212060548078360485197 69286579522705529385181949)
    ·
      refine ⟨25982467321014573519443231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69286579522705529385181949 25982467321014573519443231)
      ·
        refine ⟨38973700981521860279164847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25982467321014573519443231 38973700981521860279164847)
        ·
          refine ⟨58460551472282790418747271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38973700981521860279164847 58460551472282790418747271)
          ·
            refine ⟨87690827208424185628120907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58460551472282790418747271 87690827208424185628120907)
            ·
              refine ⟨131536240812636278442181361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87690827208424185628120907 131536240812636278442181361)
              ·
                refine ⟨98652180609477208831636021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 131536240812636278442181361 98652180609477208831636021)
                ·
                  refine ⟨9248641932138488327965877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 98652180609477208831636021 9248641932138488327965877)
                  ·
                    refine ⟨867060181137983280746801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9248641932138488327965877 867060181137983280746801)
                    ·
                      rfl

theorem cell23_5065781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 2, 5, 5].length) (baseStart_5065781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5065781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5065781 prefixEnd_5065781 := by exact prefixLift 5065781
  have htrace : WordTrace (prefixWord ++ tailWord_5065781) baseStart_5065781 baseEnd_5065781 := by
    simpa [prefixWord, tailWord_5065781, baseEnd_5065781] using wordTrace_append hprefix tailTrace_5065781
  have hstable : (prefixWord ++ tailWord_5065781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5065781).length < 2 ^ (prefixWord ++ tailWord_5065781).sum := by decide
  have hdescent : baseEnd_5065781 < baseStart_5065781 := by decide
  rcases family_descends (prefixWord ++ tailWord_5065781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5065818 : List Nat := [3, 1, 1, 2, 1, 1, 2, 6, 1, 1, 4]
def baseStart_5065818 : Nat := 118140960795 + 5065818 * 2 ^ 59
def prefixEnd_5065818 : Nat := 4983230072969 + 3 ^ 40 * 5065818 * 2
def baseEnd_5065818 : Nat := 2601199542198166197477733

theorem tailTrace_5065818 : CollatzResearch.WordTrace tailWord_5065818 prefixEnd_5065818 2601199542198166197477733 := by
  unfold tailWord_5065818
  simp only [CollatzResearch.WordTrace]
  refine ⟨46191390390353508419895527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123177041040942689119721405 46191390390353508419895527)
  ·
    refine ⟨69287085585530262629843291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46191390390353508419895527 69287085585530262629843291)
    ·
      refine ⟨103930628378295393944764937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69287085585530262629843291 103930628378295393944764937)
      ·
        refine ⟨77947971283721545458573703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103930628378295393944764937 77947971283721545458573703)
        ·
          refine ⟨116921956925582318187860555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77947971283721545458573703 116921956925582318187860555)
          ·
            refine ⟨175382935388373477281790833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116921956925582318187860555 175382935388373477281790833)
            ·
              refine ⟨131537201541280107961343125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 175382935388373477281790833 131537201541280107961343125)
              ·
                refine ⟨6165806322247505060687959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 131537201541280107961343125 6165806322247505060687959)
                ·
                  refine ⟨9248709483371257591031939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6165806322247505060687959 9248709483371257591031939)
                  ·
                    refine ⟨13873064225056886386547909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9248709483371257591031939 13873064225056886386547909)
                    ·
                      refine ⟨2601199542198166197477733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13873064225056886386547909 2601199542198166197477733)
                      ·
                        rfl

theorem cell23_5065818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 6, 1, 1, 4].length) (baseStart_5065818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5065818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5065818 prefixEnd_5065818 := by exact prefixLift 5065818
  have htrace : WordTrace (prefixWord ++ tailWord_5065818) baseStart_5065818 baseEnd_5065818 := by
    simpa [prefixWord, tailWord_5065818, baseEnd_5065818] using wordTrace_append hprefix tailTrace_5065818
  have hstable : (prefixWord ++ tailWord_5065818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5065818).length < 2 ^ (prefixWord ++ tailWord_5065818).sum := by decide
  have hdescent : baseEnd_5065818 < baseStart_5065818 := by decide
  rcases family_descends (prefixWord ++ tailWord_5065818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5065885 : List Nat := [1, 4, 2, 1, 1, 2, 2, 2, 4, 1, 3]
def baseStart_5065885 : Nat := 118140960795 + 5065885 * 2 ^ 59
def prefixEnd_5065885 : Nat := 4983230072969 + 3 ^ 40 * 5065885 * 2
def baseEnd_5065885 : Nat := 2601233945402017435339925

theorem tailTrace_5065885 : CollatzResearch.WordTrace tailWord_5065885 prefixEnd_5065885 2601233945402017435339925 := by
  unfold tailWord_5065885
  simp only [CollatzResearch.WordTrace]
  refine ⟨184768005252171304122271109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123178670168114202748180739 184768005252171304122271109)
  ·
    refine ⟨34644000984782119522925833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 184768005252171304122271109 34644000984782119522925833)
    ·
      refine ⟨25983000738586589642194375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34644000984782119522925833 25983000738586589642194375)
      ·
        refine ⟨38974501107879884463291563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25983000738586589642194375 38974501107879884463291563)
        ·
          refine ⟨58461751661819826694937345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38974501107879884463291563 58461751661819826694937345)
          ·
            refine ⟨43846313746364870021203009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58461751661819826694937345 43846313746364870021203009)
            ·
              refine ⟨32884735309773652515902257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43846313746364870021203009 32884735309773652515902257)
              ·
                refine ⟨24663551482330239386926693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32884735309773652515902257 24663551482330239386926693)
                ·
                  refine ⟨4624415902936919885048755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24663551482330239386926693 4624415902936919885048755)
                  ·
                    refine ⟨6936623854405379827573133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4624415902936919885048755 6936623854405379827573133)
                    ·
                      refine ⟨2601233945402017435339925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6936623854405379827573133 2601233945402017435339925)
                      ·
                        rfl

theorem cell23_5065885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 2, 4, 1, 3].length) (baseStart_5065885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5065885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5065885 prefixEnd_5065885 := by exact prefixLift 5065885
  have htrace : WordTrace (prefixWord ++ tailWord_5065885) baseStart_5065885 baseEnd_5065885 := by
    simpa [prefixWord, tailWord_5065885, baseEnd_5065885] using wordTrace_append hprefix tailTrace_5065885
  have hstable : (prefixWord ++ tailWord_5065885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5065885).length < 2 ^ (prefixWord ++ tailWord_5065885).sum := by decide
  have hdescent : baseEnd_5065885 < baseStart_5065885 := by decide
  rcases family_descends (prefixWord ++ tailWord_5065885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5065886 : List Nat := [4, 3, 1, 1, 2, 1, 1, 5, 1, 2, 2]
def baseStart_5065886 : Nat := 118140960795 + 5065886 * 2 ^ 59
def prefixEnd_5065886 : Nat := 4983230072969 + 3 ^ 40 * 5065886 * 2
def baseEnd_5065886 : Nat := 2601234458882671931427421

theorem tailTrace_5065886 : CollatzResearch.WordTrace tailWord_5065886 prefixEnd_5065886 2601234458882671931427421 := by
  unfold tailWord_5065886
  simp only [CollatzResearch.WordTrace]
  refine ⟨23096005215645960161632189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 123178694483445120862038341 23096005215645960161632189)
  ·
    refine ⟨8661001955867235060612071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23096005215645960161632189 8661001955867235060612071)
    ·
      refine ⟨12991502933800852590918107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8661001955867235060612071 12991502933800852590918107)
      ·
        refine ⟨19487254400701278886377161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12991502933800852590918107 19487254400701278886377161)
        ·
          refine ⟨14615440800525959164782871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19487254400701278886377161 14615440800525959164782871)
          ·
            refine ⟨21923161200788938747174307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14615440800525959164782871 21923161200788938747174307)
            ·
              refine ⟨32884741801183408120761461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21923161200788938747174307 32884741801183408120761461)
              ·
                refine ⟨3082944543860944511321387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32884741801183408120761461 3082944543860944511321387)
                ·
                  refine ⟨4624416815791416766982081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3082944543860944511321387 4624416815791416766982081)
                  ·
                    refine ⟨3468312611843562575236561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4624416815791416766982081 3468312611843562575236561)
                    ·
                      refine ⟨2601234458882671931427421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3468312611843562575236561 2601234458882671931427421)
                      ·
                        rfl

theorem cell23_5065886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 5, 1, 2, 2].length) (baseStart_5065886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5065886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5065886 prefixEnd_5065886 := by exact prefixLift 5065886
  have htrace : WordTrace (prefixWord ++ tailWord_5065886) baseStart_5065886 baseEnd_5065886 := by
    simpa [prefixWord, tailWord_5065886, baseEnd_5065886] using wordTrace_append hprefix tailTrace_5065886
  have hstable : (prefixWord ++ tailWord_5065886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5065886).length < 2 ^ (prefixWord ++ tailWord_5065886).sum := by decide
  have hdescent : baseEnd_5065886 < baseStart_5065886 := by decide
  rcases family_descends (prefixWord ++ tailWord_5065886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5065926 : List Nat := [6, 1, 2, 2, 1, 2, 2, 7]
def baseStart_5065926 : Nat := 118140960795 + 5065926 * 2 ^ 59
def prefixEnd_5065926 : Nat := 4983230072969 + 3 ^ 40 * 5065926 * 2
def baseEnd_5065926 : Nat := 96342777707735250923231

theorem tailTrace_5065926 : CollatzResearch.WordTrace tailWord_5065926 prefixEnd_5065926 96342777707735250923231 := by
  unfold tailWord_5065926
  simp only [CollatzResearch.WordTrace]
  refine ⟨5774046895156961503891051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 123179667096681845416342421 5774046895156961503891051)
  ·
    refine ⟨8661070342735442255836577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5774046895156961503891051 8661070342735442255836577)
    ·
      refine ⟨6495802757051581691877433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8661070342735442255836577 6495802757051581691877433)
      ·
        refine ⟨4871852067788686268908075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6495802757051581691877433 4871852067788686268908075)
        ·
          refine ⟨7307778101683029403362113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4871852067788686268908075 7307778101683029403362113)
          ·
            refine ⟨5480833576262272052521585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7307778101683029403362113 5480833576262272052521585)
            ·
              refine ⟨4110625182196704039391189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5480833576262272052521585 4110625182196704039391189)
              ·
                refine ⟨96342777707735250923231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4110625182196704039391189 96342777707735250923231)
                ·
                  rfl

theorem cell23_5065926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 2, 7].length) (baseStart_5065926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5065926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5065926 prefixEnd_5065926 := by exact prefixLift 5065926
  have htrace : WordTrace (prefixWord ++ tailWord_5065926) baseStart_5065926 baseEnd_5065926 := by
    simpa [prefixWord, tailWord_5065926, baseEnd_5065926] using wordTrace_append hprefix tailTrace_5065926
  have hstable : (prefixWord ++ tailWord_5065926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5065926).length < 2 ^ (prefixWord ++ tailWord_5065926).sum := by decide
  have hdescent : baseEnd_5065926 < baseStart_5065926 := by decide
  rcases family_descends (prefixWord ++ tailWord_5065926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5065928 : List Nat := [2, 1, 3, 1, 2, 1, 2, 2, 2, 4, 3]
def baseStart_5065928 : Nat := 118140960795 + 5065928 * 2 ^ 59
def prefixEnd_5065928 : Nat := 4983230072969 + 3 ^ 40 * 5065928 * 2
def baseEnd_5065928 : Nat := 2601256025070160767102227

theorem tailTrace_5065928 : CollatzResearch.WordTrace tailWord_5065928 prefixEnd_5065928 2601256025070160767102227 := by
  unfold tailWord_5065928
  simp only [CollatzResearch.WordTrace]
  refine ⟨92384786795507761233043219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123179715727343681644057625 92384786795507761233043219)
  ·
    refine ⟨138577180193261641849564829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92384786795507761233043219 138577180193261641849564829)
    ·
      refine ⟨51966442572473115693586811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 138577180193261641849564829 51966442572473115693586811)
      ·
        refine ⟨77949663858709673540380217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51966442572473115693586811 77949663858709673540380217)
        ·
          refine ⟨58462247894032255155285163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77949663858709673540380217 58462247894032255155285163)
          ·
            refine ⟨87693371841048382732927745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58462247894032255155285163 87693371841048382732927745)
            ·
              refine ⟨65770028880786287049695809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87693371841048382732927745 65770028880786287049695809)
              ·
                refine ⟨49327521660589715287271857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65770028880786287049695809 49327521660589715287271857)
                ·
                  refine ⟨36995641245442286465453893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49327521660589715287271857 36995641245442286465453893)
                  ·
                    refine ⟨6936682733520428712272605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36995641245442286465453893 6936682733520428712272605)
                    ·
                      refine ⟨2601256025070160767102227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6936682733520428712272605 2601256025070160767102227)
                      ·
                        rfl

theorem cell23_5065928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 2, 2, 4, 3].length) (baseStart_5065928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5065928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5065928 prefixEnd_5065928 := by exact prefixLift 5065928
  have htrace : WordTrace (prefixWord ++ tailWord_5065928) baseStart_5065928 baseEnd_5065928 := by
    simpa [prefixWord, tailWord_5065928, baseEnd_5065928] using wordTrace_append hprefix tailTrace_5065928
  have hstable : (prefixWord ++ tailWord_5065928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5065928).length < 2 ^ (prefixWord ++ tailWord_5065928).sum := by decide
  have hdescent : baseEnd_5065928 < baseStart_5065928 := by decide
  rcases family_descends (prefixWord ++ tailWord_5065928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5065931 : List Nat := [1, 1, 1, 1, 3, 2, 2, 3, 9]
def baseStart_5065931 : Nat := 118140960795 + 5065931 * 2 ^ 59
def prefixEnd_5065931 : Nat := 4983230072969 + 3 ^ 40 * 5065931 * 2
def baseEnd_5065931 : Nat := 289028618390236028373857

theorem tailTrace_5065931 : CollatzResearch.WordTrace tailWord_5065931 prefixEnd_5065931 289028618390236028373857 := by
  unfold tailWord_5065931
  simp only [CollatzResearch.WordTrace]
  refine ⟨184769683010004653978445647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123179788673336435985630431 184769683010004653978445647)
  ·
    refine ⟨277154524515006980967668471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184769683010004653978445647 277154524515006980967668471)
    ·
      refine ⟨415731786772510471451502707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 277154524515006980967668471 415731786772510471451502707)
      ·
        refine ⟨623597680158765707177254061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 415731786772510471451502707 623597680158765707177254061)
        ·
          refine ⟨233849130059537140191470273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 623597680158765707177254061 233849130059537140191470273)
          ·
            refine ⟨175386847544652855143602705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 233849130059537140191470273 175386847544652855143602705)
            ·
              refine ⟨131540135658489641357702029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 175386847544652855143602705 131540135658489641357702029)
              ·
                refine ⟨49327550871933615509138261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 131540135658489641357702029 49327550871933615509138261)
                ·
                  refine ⟨289028618390236028373857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 49327550871933615509138261 289028618390236028373857)
                  ·
                    rfl

theorem cell23_5065931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 3, 9].length) (baseStart_5065931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5065931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5065931 prefixEnd_5065931 := by exact prefixLift 5065931
  have htrace : WordTrace (prefixWord ++ tailWord_5065931) baseStart_5065931 baseEnd_5065931 := by
    simpa [prefixWord, tailWord_5065931, baseEnd_5065931] using wordTrace_append hprefix tailTrace_5065931
  have hstable : (prefixWord ++ tailWord_5065931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5065931).length < 2 ^ (prefixWord ++ tailWord_5065931).sum := by decide
  have hdescent : baseEnd_5065931 < baseStart_5065931 := by decide
  rcases family_descends (prefixWord ++ tailWord_5065931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5065965 : List Nat := [1, 5, 1, 2, 2, 1, 3, 1, 7]
def baseStart_5065965 : Nat := 118140960795 + 5065965 * 2 ^ 59
def prefixEnd_5065965 : Nat := 4983230072969 + 3 ^ 40 * 5065965 * 2
def baseEnd_5065965 : Nat := 289030558206041902482173

theorem tailTrace_5065965 : CollatzResearch.WordTrace tailWord_5065965 prefixEnd_5065965 289030558206041902482173 := by
  unfold tailWord_5065965
  simp only [CollatzResearch.WordTrace]
  refine ⟨184770923091881477785183349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123180615394587651856788899 184770923091881477785183349)
  ·
    refine ⟨17322274039863888542360939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 184770923091881477785183349 17322274039863888542360939)
    ·
      refine ⟨25983411059795832813541409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17322274039863888542360939 25983411059795832813541409)
      ·
        refine ⟨19487558294846874610156057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25983411059795832813541409 19487558294846874610156057)
        ·
          refine ⟨14615668721135155957617043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19487558294846874610156057 14615668721135155957617043)
          ·
            refine ⟨21923503081702733936425565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14615668721135155957617043 21923503081702733936425565)
            ·
              refine ⟨8221313655638525226159587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21923503081702733936425565 8221313655638525226159587)
              ·
                refine ⟨12331970483457787839239381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8221313655638525226159587 12331970483457787839239381)
                ·
                  refine ⟨289030558206041902482173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12331970483457787839239381 289030558206041902482173)
                  ·
                    rfl

theorem cell23_5065965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 3, 1, 7].length) (baseStart_5065965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5065965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5065965 prefixEnd_5065965 := by exact prefixLift 5065965
  have htrace : WordTrace (prefixWord ++ tailWord_5065965) baseStart_5065965 baseEnd_5065965 := by
    simpa [prefixWord, tailWord_5065965, baseEnd_5065965] using wordTrace_append hprefix tailTrace_5065965
  have hstable : (prefixWord ++ tailWord_5065965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5065965).length < 2 ^ (prefixWord ++ tailWord_5065965).sum := by decide
  have hdescent : baseEnd_5065965 < baseStart_5065965 := by decide
  rcases family_descends (prefixWord ++ tailWord_5065965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5065978 : List Nat := [3, 1, 1, 1, 1, 4, 1, 2, 4, 5]
def baseStart_5065978 : Nat := 118140960795 + 5065978 * 2 ^ 59
def prefixEnd_5065978 : Nat := 4983230072969 + 3 ^ 40 * 5065978 * 2
def baseEnd_5065978 : Nat := 867093899700961857158999

theorem tailTrace_5065978 : CollatzResearch.WordTrace tailWord_5065978 prefixEnd_5065978 867093899700961857158999 := by
  unfold tailWord_5065978
  simp only [CollatzResearch.WordTrace]
  refine ⟨46192849310208595251351647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123180931493889587336937725 46192849310208595251351647)
  ·
    refine ⟨69289273965312892877027471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46192849310208595251351647 69289273965312892877027471)
    ·
      refine ⟨103933910947969339315541207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69289273965312892877027471 103933910947969339315541207)
      ·
        refine ⟨155900866421954008973311811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103933910947969339315541207 155900866421954008973311811)
        ·
          refine ⟨233851299632931013459967717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155900866421954008973311811 233851299632931013459967717)
          ·
            refine ⟨43847118681174565023743947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 233851299632931013459967717 43847118681174565023743947)
            ·
              refine ⟨65770678021761847535615921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43847118681174565023743947 65770678021761847535615921)
              ·
                refine ⟨49328008516321385651711941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65770678021761847535615921 49328008516321385651711941)
                ·
                  refine ⟨9249001596810259809695989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49328008516321385651711941 9249001596810259809695989)
                  ·
                    refine ⟨867093899700961857158999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9249001596810259809695989 867093899700961857158999)
                    ·
                      rfl

theorem cell23_5065978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 2, 4, 5].length) (baseStart_5065978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5065978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5065978 prefixEnd_5065978 := by exact prefixLift 5065978
  have htrace : WordTrace (prefixWord ++ tailWord_5065978) baseStart_5065978 baseEnd_5065978 := by
    simpa [prefixWord, tailWord_5065978, baseEnd_5065978] using wordTrace_append hprefix tailTrace_5065978
  have hstable : (prefixWord ++ tailWord_5065978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5065978).length < 2 ^ (prefixWord ++ tailWord_5065978).sum := by decide
  have hdescent : baseEnd_5065978 < baseStart_5065978 := by decide
  rcases family_descends (prefixWord ++ tailWord_5065978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5065995 : List Nat := [1, 1, 1, 1, 5, 4, 2, 1, 2, 5]
def baseStart_5065995 : Nat := 118140960795 + 5065995 * 2 ^ 59
def prefixEnd_5065995 : Nat := 4983230072969 + 3 ^ 40 * 5065995 * 2
def baseEnd_5065995 : Nat := 867096809424670668321473

theorem tailTrace_5065995 : CollatzResearch.WordTrace tailWord_5065995 prefixEnd_5065995 867096809424670668321473 := by
  unfold tailWord_5065995
  simp only [CollatzResearch.WordTrace]
  refine ⟨184772017281772792908775439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123181344854515195272516959 184772017281772792908775439)
  ·
    refine ⟨277158025922659189363163159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184772017281772792908775439 277158025922659189363163159)
    ·
      refine ⟨415737038883988784044744739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 277158025922659189363163159 415737038883988784044744739)
      ·
        refine ⟨623605558325983176067117109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 415737038883988784044744739 623605558325983176067117109)
        ·
          refine ⟨58463021093060922756292229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 623605558325983176067117109 58463021093060922756292229)
          ·
            refine ⟨10961816454948923016804793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58463021093060922756292229 10961816454948923016804793)
            ·
              refine ⟨8221362341211692262603595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10961816454948923016804793 8221362341211692262603595)
              ·
                refine ⟨12332043511817538393905393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8221362341211692262603595 12332043511817538393905393)
                ·
                  refine ⟨9249032633863153795429045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12332043511817538393905393 9249032633863153795429045)
                  ·
                    refine ⟨867096809424670668321473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9249032633863153795429045 867096809424670668321473)
                    ·
                      rfl

theorem cell23_5065995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 2, 1, 2, 5].length) (baseStart_5065995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5065995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5065995 prefixEnd_5065995 := by exact prefixLift 5065995
  have htrace : WordTrace (prefixWord ++ tailWord_5065995) baseStart_5065995 baseEnd_5065995 := by
    simpa [prefixWord, tailWord_5065995, baseEnd_5065995] using wordTrace_append hprefix tailTrace_5065995
  have hstable : (prefixWord ++ tailWord_5065995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5065995).length < 2 ^ (prefixWord ++ tailWord_5065995).sum := by decide
  have hdescent : baseEnd_5065995 < baseStart_5065995 := by decide
  rcases family_descends (prefixWord ++ tailWord_5065995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5066016 : List Nat := [2, 1, 1, 5, 4, 1, 2, 2, 5]
def baseStart_5066016 : Nat := 118140960795 + 5066016 * 2 ^ 59
def prefixEnd_5066016 : Nat := 4983230072969 + 3 ^ 40 * 5066016 * 2
def baseEnd_5066016 : Nat := 289033467929750713644647

theorem tailTrace_5066016 : CollatzResearch.WordTrace tailWord_5066016 prefixEnd_5066016 289033467929750713644647 := by
  unfold tailWord_5066016
  simp only [CollatzResearch.WordTrace]
  refine ⟨92386391607348356747644951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123181855476464475663526601 92386391607348356747644951)
  ·
    refine ⟨138579587411022535121467427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92386391607348356747644951 138579587411022535121467427)
    ·
      refine ⟨207869381116533802682201141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138579587411022535121467427 207869381116533802682201141)
      ·
        refine ⟨19487754479675044001456357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 207869381116533802682201141 19487754479675044001456357)
        ·
          refine ⟨3653953964939070750273067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19487754479675044001456357 3653953964939070750273067)
          ·
            refine ⟨5480930947408606125409601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3653953964939070750273067 5480930947408606125409601)
            ·
              refine ⟨4110698210556454594057201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5480930947408606125409601 4110698210556454594057201)
              ·
                refine ⟨3083023657917340945542901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4110698210556454594057201 3083023657917340945542901)
                ·
                  refine ⟨289033467929750713644647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3083023657917340945542901 289033467929750713644647)
                  ·
                    rfl

theorem cell23_5066016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 2, 2, 5].length) (baseStart_5066016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5066016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5066016 prefixEnd_5066016 := by exact prefixLift 5066016
  have htrace : WordTrace (prefixWord ++ tailWord_5066016) baseStart_5066016 baseEnd_5066016 := by
    simpa [prefixWord, tailWord_5066016, baseEnd_5066016] using wordTrace_append hprefix tailTrace_5066016
  have hstable : (prefixWord ++ tailWord_5066016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5066016).length < 2 ^ (prefixWord ++ tailWord_5066016).sum := by decide
  have hdescent : baseEnd_5066016 < baseStart_5066016 := by decide
  rcases family_descends (prefixWord ++ tailWord_5066016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5066028 : List Nat := [2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 4]
def baseStart_5066028 : Nat := 118140960795 + 5066028 * 2 ^ 59
def prefixEnd_5066028 : Nat := 4983230072969 + 3 ^ 40 * 5066028 * 2
def baseEnd_5066028 : Nat := 2601307373135610375851767

theorem tailTrace_5066028 : CollatzResearch.WordTrace tailWord_5066028 prefixEnd_5066028 2601307373135610375851767 := by
  unfold tailWord_5066028
  simp only [CollatzResearch.WordTrace]
  refine ⟨92386610445326619772363369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123182147260435493029817825 92386610445326619772363369)
  ·
    refine ⟨69289957833994964829272527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92386610445326619772363369 69289957833994964829272527)
    ·
      refine ⟨103934936750992447243908791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69289957833994964829272527 103934936750992447243908791)
      ·
        refine ⟨155902405126488670865863187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103934936750992447243908791 155902405126488670865863187)
        ·
          refine ⟨233853607689733006298794781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155902405126488670865863187 233853607689733006298794781)
          ·
            refine ⟨87695102883649877362048043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 233853607689733006298794781 87695102883649877362048043)
            ·
              refine ⟨131542654325474816043072065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87695102883649877362048043 131542654325474816043072065)
              ·
                refine ⟨98656990744106112032304049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 131542654325474816043072065 98656990744106112032304049)
                ·
                  refine ⟨73992743058079584024228037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 98656990744106112032304049 73992743058079584024228037)
                  ·
                    refine ⟨13873639323389922004542757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 73992743058079584024228037 13873639323389922004542757)
                    ·
                      refine ⟨2601307373135610375851767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13873639323389922004542757 2601307373135610375851767)
                      ·
                        rfl

theorem cell23_5066028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 4].length) (baseStart_5066028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5066028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5066028 prefixEnd_5066028 := by exact prefixLift 5066028
  have htrace : WordTrace (prefixWord ++ tailWord_5066028) baseStart_5066028 baseEnd_5066028 := by
    simpa [prefixWord, tailWord_5066028, baseEnd_5066028] using wordTrace_append hprefix tailTrace_5066028
  have hstable : (prefixWord ++ tailWord_5066028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5066028).length < 2 ^ (prefixWord ++ tailWord_5066028).sum := by decide
  have hdescent : baseEnd_5066028 < baseStart_5066028 := by decide
  rcases family_descends (prefixWord ++ tailWord_5066028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5066049 : List Nat := [1, 2, 5, 2, 1, 3, 1, 1, 2, 1, 4]
def baseStart_5066049 : Nat := 118140960795 + 5066049 * 2 ^ 59
def prefixEnd_5066049 : Nat := 4983230072969 + 3 ^ 40 * 5066049 * 2
def baseEnd_5066049 : Nat := 2601318156229354793689171

theorem tailTrace_5066049 : CollatzResearch.WordTrace tailWord_5066049 prefixEnd_5066049 2601318156229354793689171 := by
  unfold tailWord_5066049
  simp only [CollatzResearch.WordTrace]
  refine ⟨184773986823577160131241201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123182657882384773420827467 184773986823577160131241201)
  ·
    refine ⟨138580490117682870098430901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184773986823577160131241201 138580490117682870098430901)
    ·
      refine ⟨12991920948532769071727897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 138580490117682870098430901 12991920948532769071727897)
      ·
        refine ⟨9743940711399576803795923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12991920948532769071727897 9743940711399576803795923)
        ·
          refine ⟨14615911067099365205693885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9743940711399576803795923 14615911067099365205693885)
          ·
            refine ⟨5480966650162261952135207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14615911067099365205693885 5480966650162261952135207)
            ·
              refine ⟨8221449975243392928202811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5480966650162261952135207 8221449975243392928202811)
              ·
                refine ⟨12332174962865089392304217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8221449975243392928202811 12332174962865089392304217)
                ·
                  refine ⟨9249131222148817044228163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12332174962865089392304217 9249131222148817044228163)
                  ·
                    refine ⟨13873696833223225566342245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9249131222148817044228163 13873696833223225566342245)
                    ·
                      refine ⟨2601318156229354793689171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13873696833223225566342245 2601318156229354793689171)
                      ·
                        rfl

theorem cell23_5066049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 1, 1, 2, 1, 4].length) (baseStart_5066049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5066049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5066049 prefixEnd_5066049 := by exact prefixLift 5066049
  have htrace : WordTrace (prefixWord ++ tailWord_5066049) baseStart_5066049 baseEnd_5066049 := by
    simpa [prefixWord, tailWord_5066049, baseEnd_5066049] using wordTrace_append hprefix tailTrace_5066049
  have hstable : (prefixWord ++ tailWord_5066049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5066049).length < 2 ^ (prefixWord ++ tailWord_5066049).sum := by decide
  have hdescent : baseEnd_5066049 < baseStart_5066049 := by decide
  rcases family_descends (prefixWord ++ tailWord_5066049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5066058 : List Nat := [3, 1, 2, 1, 1, 1, 1, 2, 3, 2, 6]
def baseStart_5066058 : Nat := 118140960795 + 5066058 * 2 ^ 59
def prefixEnd_5066058 : Nat := 4983230072969 + 3 ^ 40 * 5066058 * 2
def baseEnd_5066058 : Nat := 2601322777555245258476629

theorem tailTrace_5066058 : CollatzResearch.WordTrace tailWord_5066058 prefixEnd_5066058 2601322777555245258476629 := by
  unfold tailWord_5066058
  simp only [CollatzResearch.WordTrace]
  refine ⟨46193578770136138667079707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123182876720363036445545885 46193578770136138667079707)
  ·
    refine ⟨69290368155204208000619561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46193578770136138667079707 69290368155204208000619561)
    ·
      refine ⟨51967776116403156000464671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69290368155204208000619561 51967776116403156000464671)
      ·
        refine ⟨77951664174604734000697007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51967776116403156000464671 77951664174604734000697007)
        ·
          refine ⟨116927496261907101001045511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77951664174604734000697007 116927496261907101001045511)
          ·
            refine ⟨175391244392860651501568267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116927496261907101001045511 175391244392860651501568267)
            ·
              refine ⟨263086866589290977252352401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 175391244392860651501568267 263086866589290977252352401)
              ·
                refine ⟨197315149941968232939264301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 263086866589290977252352401 197315149941968232939264301)
                ·
                  refine ⟨73993181228238087352224113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 197315149941968232939264301 73993181228238087352224113)
                  ·
                    refine ⟨55494885921178565514168085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 73993181228238087352224113 55494885921178565514168085)
                    ·
                      refine ⟨2601322777555245258476629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 55494885921178565514168085 2601322777555245258476629)
                      ·
                        rfl

theorem cell23_5066058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 2, 3, 2, 6].length) (baseStart_5066058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5066058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5066058 prefixEnd_5066058 := by exact prefixLift 5066058
  have htrace : WordTrace (prefixWord ++ tailWord_5066058) baseStart_5066058 baseEnd_5066058 := by
    simpa [prefixWord, tailWord_5066058, baseEnd_5066058] using wordTrace_append hprefix tailTrace_5066058
  have hstable : (prefixWord ++ tailWord_5066058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5066058).length < 2 ^ (prefixWord ++ tailWord_5066058).sum := by decide
  have hdescent : baseEnd_5066058 < baseStart_5066058 := by decide
  rcases family_descends (prefixWord ++ tailWord_5066058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5066092 : List Nat := [2, 2, 1, 1, 5, 1, 1, 2, 1, 5, 2]
def baseStart_5066092 : Nat := 118140960795 + 5066092 * 2 ^ 59
def prefixEnd_5066092 : Nat := 4983230072969 + 3 ^ 40 * 5066092 * 2
def baseEnd_5066092 : Nat := 2601340235897498125451473

theorem tailTrace_5066092 : CollatzResearch.WordTrace tailWord_5066092 prefixEnd_5066092 2601340235897498125451473 := by
  unfold tailWord_5066092
  simp only [CollatzResearch.WordTrace]
  refine ⟨92387777581210689237528265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123183703441614252316704353 92387777581210689237528265)
  ·
    refine ⟨69290833185908016928146199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92387777581210689237528265 69290833185908016928146199)
    ·
      refine ⟨103936249778862025392219299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69290833185908016928146199 103936249778862025392219299)
      ·
        refine ⟨155904374668293038088328949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103936249778862025392219299 155904374668293038088328949)
        ·
          refine ⟨14616035125152472320780839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 155904374668293038088328949 14616035125152472320780839)
          ·
            refine ⟨21924052687728708481171259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14616035125152472320780839 21924052687728708481171259)
            ·
              refine ⟨32886079031593062721756889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21924052687728708481171259 32886079031593062721756889)
              ·
                refine ⟨24664559273694797041317667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32886079031593062721756889 24664559273694797041317667)
                ·
                  refine ⟨36996838910542195561976501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24664559273694797041317667 36996838910542195561976501)
                  ·
                    refine ⟨3468453647863330833935297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 36996838910542195561976501 3468453647863330833935297)
                    ·
                      refine ⟨2601340235897498125451473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3468453647863330833935297 2601340235897498125451473)
                      ·
                        rfl

theorem cell23_5066092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 5, 2].length) (baseStart_5066092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5066092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5066092 prefixEnd_5066092 := by exact prefixLift 5066092
  have htrace : WordTrace (prefixWord ++ tailWord_5066092) baseStart_5066092 baseEnd_5066092 := by
    simpa [prefixWord, tailWord_5066092, baseEnd_5066092] using wordTrace_append hprefix tailTrace_5066092
  have hstable : (prefixWord ++ tailWord_5066092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5066092).length < 2 ^ (prefixWord ++ tailWord_5066092).sum := by decide
  have hdescent : baseEnd_5066092 < baseStart_5066092 := by decide
  rcases family_descends (prefixWord ++ tailWord_5066092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
