import V185TrunkScan23Chunk1190

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7056898 : List Nat := [3, 4, 1, 2, 1, 1, 2, 1, 3, 1, 4]
def baseStart_7056898 : Nat := 118140960795 + 7056898 * 2 ^ 59
def prefixEnd_7056898 : Nat := 4983230072969 + 3 ^ 40 * 7056898 * 2
def baseEnd_7056898 : Nat := 3623580603752236087820923

theorem tailTrace_7056898 : CollatzResearch.WordTrace tailWord_7056898 prefixEnd_7056898 3623580603752236087820923 := by
  unfold tailWord_7056898
  simp only [CollatzResearch.WordTrace]
  refine ⟨64346553797017810767716837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171590810125380828713911565 64346553797017810767716837)
  ·
    refine ⟨12064978836940839518946907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64346553797017810767716837 12064978836940839518946907)
    ·
      refine ⟨18097468255411259278420361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12064978836940839518946907 18097468255411259278420361)
      ·
        refine ⟨13573101191558444458815271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18097468255411259278420361 13573101191558444458815271)
        ·
          refine ⟨20359651787337666688222907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13573101191558444458815271 20359651787337666688222907)
          ·
            refine ⟨30539477681006500032334361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20359651787337666688222907 30539477681006500032334361)
            ·
              refine ⟨22904608260754875024250771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30539477681006500032334361 22904608260754875024250771)
              ·
                refine ⟨34356912391132312536376157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22904608260754875024250771 34356912391132312536376157)
                ·
                  refine ⟨12883842146674617201141059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34356912391132312536376157 12883842146674617201141059)
                  ·
                    refine ⟨19325763220011925801711589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12883842146674617201141059 19325763220011925801711589)
                    ·
                      refine ⟨3623580603752236087820923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19325763220011925801711589 3623580603752236087820923)
                      ·
                        rfl

theorem cell23_7056898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_7056898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7056898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7056898 prefixEnd_7056898 := by exact prefixLift 7056898
  have htrace : WordTrace (prefixWord ++ tailWord_7056898) baseStart_7056898 baseEnd_7056898 := by
    simpa [prefixWord, tailWord_7056898, baseEnd_7056898] using wordTrace_append hprefix tailTrace_7056898
  have hstable : (prefixWord ++ tailWord_7056898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7056898).length < 2 ^ (prefixWord ++ tailWord_7056898).sum := by decide
  have hdescent : baseEnd_7056898 < baseStart_7056898 := by decide
  rcases family_descends (prefixWord ++ tailWord_7056898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7056901 : List Nat := [1, 3, 1, 1, 2, 2, 1, 6, 1, 2, 3]
def baseStart_7056901 : Nat := 118140960795 + 7056901 * 2 ^ 59
def prefixEnd_7056901 : Nat := 4983230072969 + 3 ^ 40 * 7056901 * 2
def baseEnd_7056901 : Nat := 3623582144194199576083409

theorem tailTrace_7056901 : CollatzResearch.WordTrace tailWord_7056901 prefixEnd_7056901 3623582144194199576083409 := by
  unfold tailWord_7056901
  simp only [CollatzResearch.WordTrace]
  refine ⟨257386324607060374583226557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171590883071373583055484371 257386324607060374583226557)
  ·
    refine ⟨96519871727647640468709959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 257386324607060374583226557 96519871727647640468709959)
    ·
      refine ⟨144779807591471460703064939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96519871727647640468709959 144779807591471460703064939)
      ·
        refine ⟨217169711387207191054597409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144779807591471460703064939 217169711387207191054597409)
        ·
          refine ⟨162877283540405393290948057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 217169711387207191054597409 162877283540405393290948057)
          ·
            refine ⟨122157962655304044968211043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162877283540405393290948057 122157962655304044968211043)
            ·
              refine ⟨183236943982956067452316565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122157962655304044968211043 183236943982956067452316565)
              ·
                refine ⟨8589231749201065661827339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 183236943982956067452316565 8589231749201065661827339)
                ·
                  refine ⟨12883847623801598492741009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8589231749201065661827339 12883847623801598492741009)
                  ·
                    refine ⟨9662885717851198869555757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12883847623801598492741009 9662885717851198869555757)
                    ·
                      refine ⟨3623582144194199576083409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9662885717851198869555757 3623582144194199576083409)
                      ·
                        rfl

theorem cell23_7056901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 6, 1, 2, 3].length) (baseStart_7056901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7056901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7056901 prefixEnd_7056901 := by exact prefixLift 7056901
  have htrace : WordTrace (prefixWord ++ tailWord_7056901) baseStart_7056901 baseEnd_7056901 := by
    simpa [prefixWord, tailWord_7056901, baseEnd_7056901] using wordTrace_append hprefix tailTrace_7056901
  have hstable : (prefixWord ++ tailWord_7056901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7056901).length < 2 ^ (prefixWord ++ tailWord_7056901).sum := by decide
  have hdescent : baseEnd_7056901 < baseStart_7056901 := by decide
  rcases family_descends (prefixWord ++ tailWord_7056901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7056915 : List Nat := [1, 1, 1, 2, 1, 6, 1, 5, 1, 2, 2]
def baseStart_7056915 : Nat := 118140960795 + 7056915 * 2 ^ 59
def prefixEnd_7056915 : Nat := 4983230072969 + 3 ^ 40 * 7056915 * 2
def baseEnd_7056915 : Nat := 3623589332923362521308345

theorem tailTrace_7056915 : CollatzResearch.WordTrace tailWord_7056915 prefixEnd_7056915 3623589332923362521308345 := by
  unfold tailWord_7056915
  simp only [CollatzResearch.WordTrace]
  refine ⟨257386835229009654974236199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171591223486006436649490799 257386835229009654974236199)
  ·
    refine ⟨386080252843514482461354299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257386835229009654974236199 386080252843514482461354299)
    ·
      refine ⟨579120379265271723692031449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 386080252843514482461354299 579120379265271723692031449)
      ·
        refine ⟨434340284448953792769023587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 579120379265271723692031449 434340284448953792769023587)
        ·
          refine ⟨651510426673430689153535381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 434340284448953792769023587 651510426673430689153535381)
          ·
            refine ⟨30539551250317063554071971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 651510426673430689153535381 30539551250317063554071971)
            ·
              refine ⟨45809326875475595331107957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30539551250317063554071971 45809326875475595331107957)
              ·
                refine ⟨4294624394575837062291371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45809326875475595331107957 4294624394575837062291371)
                ·
                  refine ⟨6441936591863755593437057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4294624394575837062291371 6441936591863755593437057)
                  ·
                    refine ⟨4831452443897816695077793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6441936591863755593437057 4831452443897816695077793)
                    ·
                      refine ⟨3623589332923362521308345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4831452443897816695077793 3623589332923362521308345)
                      ·
                        rfl

theorem cell23_7056915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 5, 1, 2, 2].length) (baseStart_7056915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7056915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7056915 prefixEnd_7056915 := by exact prefixLift 7056915
  have htrace : WordTrace (prefixWord ++ tailWord_7056915) baseStart_7056915 baseEnd_7056915 := by
    simpa [prefixWord, tailWord_7056915, baseEnd_7056915] using wordTrace_append hprefix tailTrace_7056915
  have hstable : (prefixWord ++ tailWord_7056915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7056915).length < 2 ^ (prefixWord ++ tailWord_7056915).sum := by decide
  have hdescent : baseEnd_7056915 < baseStart_7056915 := by decide
  rcases family_descends (prefixWord ++ tailWord_7056915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7056971 : List Nat := [1, 1, 1, 1, 3, 1, 3, 3, 3, 4, 2]
def baseStart_7056971 : Nat := 118140960795 + 7056971 * 2 ^ 59
def prefixEnd_7056971 : Nat := 4983230072969 + 3 ^ 40 * 7056971 * 2
def baseEnd_7056971 : Nat := 3623618087840014302208087

theorem tailTrace_7056971 : CollatzResearch.WordTrace tailWord_7056971 prefixEnd_7056971 3623618087840014302208087 := by
  unfold tailWord_7056971
  simp only [CollatzResearch.WordTrace]
  refine ⟨257388877716806776538274767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171592585144537851025516511 257388877716806776538274767)
  ·
    refine ⟨386083316575210164807412151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257388877716806776538274767 386083316575210164807412151)
    ·
      refine ⟨579124974862815247211118227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 386083316575210164807412151 579124974862815247211118227)
      ·
        refine ⟨868687462294222870816677341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 579124974862815247211118227 868687462294222870816677341)
        ·
          refine ⟨325757798360333576556254003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 868687462294222870816677341 325757798360333576556254003)
          ·
            refine ⟨488636697540500364834381005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 325757798360333576556254003 488636697540500364834381005)
            ·
              refine ⟨183238761577687636812892877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 488636697540500364834381005 183238761577687636812892877)
              ·
                refine ⟨68714535591632863804834829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 183238761577687636812892877 68714535591632863804834829)
                ·
                  refine ⟨25767950846862323926813061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68714535591632863804834829 25767950846862323926813061)
                  ·
                    refine ⟨4831490783786685736277449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25767950846862323926813061 4831490783786685736277449)
                    ·
                      refine ⟨3623618087840014302208087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4831490783786685736277449 3623618087840014302208087)
                      ·
                        rfl

theorem cell23_7056971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 3, 3, 4, 2].length) (baseStart_7056971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7056971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7056971 prefixEnd_7056971 := by exact prefixLift 7056971
  have htrace : WordTrace (prefixWord ++ tailWord_7056971) baseStart_7056971 baseEnd_7056971 := by
    simpa [prefixWord, tailWord_7056971, baseEnd_7056971] using wordTrace_append hprefix tailTrace_7056971
  have hstable : (prefixWord ++ tailWord_7056971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7056971).length < 2 ^ (prefixWord ++ tailWord_7056971).sum := by decide
  have hdescent : baseEnd_7056971 < baseStart_7056971 := by decide
  rcases family_descends (prefixWord ++ tailWord_7056971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7057048 : List Nat := [2, 1, 2, 4, 1, 2, 1, 1, 2, 5, 2]
def baseStart_7057048 : Nat := 118140960795 + 7057048 * 2 ^ 59
def prefixEnd_7057048 : Nat := 4983230072969 + 3 ^ 40 * 7057048 * 2
def baseEnd_7057048 : Nat := 3623657625850410500945233

theorem tailTrace_7057048 : CollatzResearch.WordTrace tailWord_7057048 prefixEnd_7057048 3623657625850410500945233 := by
  unfold tailWord_7057048
  simp only [CollatzResearch.WordTrace]
  refine ⟨128695843068763909344413899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171594457425018545792551865 128695843068763909344413899)
  ·
    refine ⟨193043764603145864016620849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128695843068763909344413899 193043764603145864016620849)
    ·
      refine ⟨144782823452359398012465637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193043764603145864016620849 144782823452359398012465637)
      ·
        refine ⟨27146779397317387127337307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 144782823452359398012465637 27146779397317387127337307)
        ·
          refine ⟨40720169095976080691005961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27146779397317387127337307 40720169095976080691005961)
          ·
            refine ⟨30540126821982060518254471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40720169095976080691005961 30540126821982060518254471)
            ·
              refine ⟨45810190232973090777381707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30540126821982060518254471 45810190232973090777381707)
              ·
                refine ⟨68715285349459636166072561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45810190232973090777381707 68715285349459636166072561)
                ·
                  refine ⟨51536464012094727124554421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68715285349459636166072561 51536464012094727124554421)
                  ·
                    refine ⟨4831543501133880667926977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51536464012094727124554421 4831543501133880667926977)
                    ·
                      refine ⟨3623657625850410500945233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4831543501133880667926977 3623657625850410500945233)
                      ·
                        rfl

theorem cell23_7057048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 1, 2, 5, 2].length) (baseStart_7057048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7057048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7057048 prefixEnd_7057048 := by exact prefixLift 7057048
  have htrace : WordTrace (prefixWord ++ tailWord_7057048) baseStart_7057048 baseEnd_7057048 := by
    simpa [prefixWord, tailWord_7057048, baseEnd_7057048] using wordTrace_append hprefix tailTrace_7057048
  have hstable : (prefixWord ++ tailWord_7057048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7057048).length < 2 ^ (prefixWord ++ tailWord_7057048).sum := by decide
  have hdescent : baseEnd_7057048 < baseStart_7057048 := by decide
  rcases family_descends (prefixWord ++ tailWord_7057048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7057055 : List Nat := [1, 1, 2, 7, 1, 1, 1, 1, 2, 3, 3]
def baseStart_7057055 : Nat := 118140960795 + 7057055 * 2 ^ 59
def prefixEnd_7057055 : Nat := 4983230072969 + 3 ^ 40 * 7057055 * 2
def baseEnd_7057055 : Nat := 3623661220214991973557701

theorem tailTrace_7057055 : CollatzResearch.WordTrace tailWord_7057055 prefixEnd_7057055 3623661220214991973557701 := by
  unfold tailWord_7057055
  simp only [CollatzResearch.WordTrace]
  refine ⟨257391941448502458884332619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171594627632334972589555079 257391941448502458884332619)
  ·
    refine ⟨386087912172753688326498929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257391941448502458884332619 386087912172753688326498929)
    ·
      refine ⟨289565934129565266244874197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 386087912172753688326498929 289565934129565266244874197)
      ·
        refine ⟨6786701581161685927614239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 289565934129565266244874197 6786701581161685927614239)
        ·
          refine ⟨10180052371742528891421359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6786701581161685927614239 10180052371742528891421359)
          ·
            refine ⟨15270078557613793337132039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10180052371742528891421359 15270078557613793337132039)
            ·
              refine ⟨22905117836420690005698059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15270078557613793337132039 22905117836420690005698059)
              ·
                refine ⟨34357676754631035008547089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22905117836420690005698059 34357676754631035008547089)
                ·
                  refine ⟨25768257565973276256410317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34357676754631035008547089 25768257565973276256410317)
                  ·
                    refine ⟨9663096587239978596153869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25768257565973276256410317 9663096587239978596153869)
                    ·
                      refine ⟨3623661220214991973557701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9663096587239978596153869 3623661220214991973557701)
                      ·
                        rfl

theorem cell23_7057055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_7057055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7057055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7057055 prefixEnd_7057055 := by exact prefixLift 7057055
  have htrace : WordTrace (prefixWord ++ tailWord_7057055) baseStart_7057055 baseEnd_7057055 := by
    simpa [prefixWord, tailWord_7057055, baseEnd_7057055] using wordTrace_append hprefix tailTrace_7057055
  have hstable : (prefixWord ++ tailWord_7057055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7057055).length < 2 ^ (prefixWord ++ tailWord_7057055).sum := by decide
  have hdescent : baseEnd_7057055 < baseStart_7057055 := by decide
  rcases family_descends (prefixWord ++ tailWord_7057055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7057061 : List Nat := [1, 3, 1, 2, 1, 2, 2, 2, 4, 1, 4]
def baseStart_7057061 : Nat := 118140960795 + 7057061 * 2 ^ 59
def prefixEnd_7057061 : Nat := 4983230072969 + 3 ^ 40 * 7057061 * 2
def baseEnd_7057061 : Nat := 3623664301098918950082673

theorem tailTrace_7057061 : CollatzResearch.WordTrace tailWord_7057061 prefixEnd_7057061 3623664301098918950082673 := by
  unfold tailWord_7057061
  simp only [CollatzResearch.WordTrace]
  refine ⟨257392160286480721909051037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171594773524320481272700691 257392160286480721909051037)
  ·
    refine ⟨96522060107430270715894139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 257392160286480721909051037 96522060107430270715894139)
    ·
      refine ⟨144783090161145406073841209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96522060107430270715894139 144783090161145406073841209)
      ·
        refine ⟨108587317620859054555380907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144783090161145406073841209 108587317620859054555380907)
        ·
          refine ⟨162880976431288581833071361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108587317620859054555380907 162880976431288581833071361)
          ·
            refine ⟨122160732323466436374803521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162880976431288581833071361 122160732323466436374803521)
            ·
              refine ⟨91620549242599827281102641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122160732323466436374803521 91620549242599827281102641)
              ·
                refine ⟨68715411931949870460826981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91620549242599827281102641 68715411931949870460826981)
                ·
                  refine ⟨12884139737240600711405059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 68715411931949870460826981 12884139737240600711405059)
                  ·
                    refine ⟨19326209605860901067107589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12884139737240600711405059 19326209605860901067107589)
                    ·
                      refine ⟨3623664301098918950082673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19326209605860901067107589 3623664301098918950082673)
                      ·
                        rfl

theorem cell23_7057061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 2, 4, 1, 4].length) (baseStart_7057061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7057061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7057061 prefixEnd_7057061 := by exact prefixLift 7057061
  have htrace : WordTrace (prefixWord ++ tailWord_7057061) baseStart_7057061 baseEnd_7057061 := by
    simpa [prefixWord, tailWord_7057061, baseEnd_7057061] using wordTrace_append hprefix tailTrace_7057061
  have hstable : (prefixWord ++ tailWord_7057061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7057061).length < 2 ^ (prefixWord ++ tailWord_7057061).sum := by decide
  have hdescent : baseEnd_7057061 < baseStart_7057061 := by decide
  rcases family_descends (prefixWord ++ tailWord_7057061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7057090 : List Nat := [3, 5, 1, 2, 2, 1, 1, 2, 2, 2, 2]
def baseStart_7057090 : Nat := 118140960795 + 7057090 * 2 ^ 59
def prefixEnd_7057090 : Nat := 4983230072969 + 3 ^ 40 * 7057090 * 2
def baseEnd_7057090 : Nat := 3623679192037899336620041

theorem tailTrace_7057090 : CollatzResearch.WordTrace tailWord_7057090 prefixEnd_7057090 3623679192037899336620041 := by
  unfold tailWord_7057090
  simp only [CollatzResearch.WordTrace]
  refine ⟨64348304500843914965464181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171595478668917106574571149 64348304500843914965464181)
  ·
    refine ⟨6032653546954117028012267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 64348304500843914965464181 6032653546954117028012267)
    ·
      refine ⟨9048980320431175542018401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6032653546954117028012267 9048980320431175542018401)
      ·
        refine ⟨6786735240323381656513801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9048980320431175542018401 6786735240323381656513801)
        ·
          refine ⟨5090051430242536242385351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6786735240323381656513801 5090051430242536242385351)
          ·
            refine ⟨7635077145363804363578027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5090051430242536242385351 7635077145363804363578027)
            ·
              refine ⟨11452615718045706545367041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7635077145363804363578027 11452615718045706545367041)
              ·
                refine ⟨8589461788534279909025281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11452615718045706545367041 8589461788534279909025281)
                ·
                  refine ⟨6442096341400709931768961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8589461788534279909025281 6442096341400709931768961)
                  ·
                    refine ⟨4831572256050532448826721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6442096341400709931768961 4831572256050532448826721)
                    ·
                      refine ⟨3623679192037899336620041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4831572256050532448826721 3623679192037899336620041)
                      ·
                        rfl

theorem cell23_7057090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 1, 2, 2, 2, 2].length) (baseStart_7057090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7057090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7057090 prefixEnd_7057090 := by exact prefixLift 7057090
  have htrace : WordTrace (prefixWord ++ tailWord_7057090) baseStart_7057090 baseEnd_7057090 := by
    simpa [prefixWord, tailWord_7057090, baseEnd_7057090] using wordTrace_append hprefix tailTrace_7057090
  have hstable : (prefixWord ++ tailWord_7057090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7057090).length < 2 ^ (prefixWord ++ tailWord_7057090).sum := by decide
  have hdescent : baseEnd_7057090 < baseStart_7057090 := by decide
  rcases family_descends (prefixWord ++ tailWord_7057090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7057105 : List Nat := [1, 2, 2, 1, 2, 4, 2, 4, 1, 4]
def baseStart_7057105 : Nat := 118140960795 + 7057105 * 2 ^ 59
def prefixEnd_7057105 : Nat := 4983230072969 + 3 ^ 40 * 7057105 * 2
def baseEnd_7057105 : Nat := 1207895631415905592644157

theorem tailTrace_7057105 : CollatzResearch.WordTrace tailWord_7057105 prefixEnd_7057105 1207895631415905592644157 := by
  unfold tailWord_7057105
  simp only [CollatzResearch.WordTrace]
  refine ⟨257393765098321317423652769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171595843398880878282435179 257393765098321317423652769)
  ·
    refine ⟨193045323823740988067739577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257393765098321317423652769 193045323823740988067739577)
    ·
      refine ⟨144783992867805741050804683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193045323823740988067739577 144783992867805741050804683)
      ·
        refine ⟨217175989301708611576207025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144783992867805741050804683 217175989301708611576207025)
        ·
          refine ⟨162881991976281458682155269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 217175989301708611576207025 162881991976281458682155269)
          ·
            refine ⟨30540373495552773502904113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 162881991976281458682155269 30540373495552773502904113)
            ·
              refine ⟨22905280121664580127178085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30540373495552773502904113 22905280121664580127178085)
              ·
                refine ⟨4294740022812108773845891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22905280121664580127178085 4294740022812108773845891)
                ·
                  refine ⟨6442110034218163160768837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4294740022812108773845891 6442110034218163160768837)
                  ·
                    refine ⟨1207895631415905592644157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6442110034218163160768837 1207895631415905592644157)
                    ·
                      rfl

theorem cell23_7057105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 4, 1, 4].length) (baseStart_7057105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7057105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7057105 prefixEnd_7057105 := by exact prefixLift 7057105
  have htrace : WordTrace (prefixWord ++ tailWord_7057105) baseStart_7057105 baseEnd_7057105 := by
    simpa [prefixWord, tailWord_7057105, baseEnd_7057105] using wordTrace_append hprefix tailTrace_7057105
  have hstable : (prefixWord ++ tailWord_7057105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7057105).length < 2 ^ (prefixWord ++ tailWord_7057105).sum := by decide
  have hdescent : baseEnd_7057105 < baseStart_7057105 := by decide
  rcases family_descends (prefixWord ++ tailWord_7057105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7057131 : List Nat := [1, 1, 1, 1, 2, 4, 2, 3, 3, 5]
def baseStart_7057131 : Nat := 118140960795 + 7057131 * 2 ^ 59
def prefixEnd_7057131 : Nat := 4983230072969 + 3 ^ 40 * 7057131 * 2
def baseEnd_7057131 : Nat := 1207900081581577892069117

theorem tailTrace_7057131 : CollatzResearch.WordTrace tailWord_7057131 prefixEnd_7057131 1207900081581577892069117 := by
  unfold tailWord_7057131
  simp only [CollatzResearch.WordTrace]
  refine ⟨257394713396227123864099247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171596475597484749242732831 257394713396227123864099247)
  ·
    refine ⟨386092070094340685796148871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257394713396227123864099247 386092070094340685796148871)
    ·
      refine ⟨579138105141511028694223307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 386092070094340685796148871 579138105141511028694223307)
      ·
        refine ⟨868707157712266543041334961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 579138105141511028694223307 868707157712266543041334961)
        ·
          refine ⟨651530368284199907281001221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 868707157712266543041334961 651530368284199907281001221)
          ·
            refine ⟨122161944053287482615187729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 651530368284199907281001221 122161944053287482615187729)
            ·
              refine ⟨91621458039965611961390797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122161944053287482615187729 91621458039965611961390797)
              ·
                refine ⟨34358046764987104485521549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91621458039965611961390797 34358046764987104485521549)
                ·
                  refine ⟨12884267536870164182070581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34358046764987104485521549 12884267536870164182070581)
                  ·
                    refine ⟨1207900081581577892069117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12884267536870164182070581 1207900081581577892069117)
                    ·
                      rfl

theorem cell23_7057131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 3, 3, 5].length) (baseStart_7057131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7057131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7057131 prefixEnd_7057131 := by exact prefixLift 7057131
  have htrace : WordTrace (prefixWord ++ tailWord_7057131) baseStart_7057131 baseEnd_7057131 := by
    simpa [prefixWord, tailWord_7057131, baseEnd_7057131] using wordTrace_append hprefix tailTrace_7057131
  have hstable : (prefixWord ++ tailWord_7057131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7057131).length < 2 ^ (prefixWord ++ tailWord_7057131).sum := by decide
  have hdescent : baseEnd_7057131 < baseStart_7057131 := by decide
  rcases family_descends (prefixWord ++ tailWord_7057131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7057148 : List Nat := [2, 2, 2, 1, 3, 1, 1, 5, 1, 5]
def baseStart_7057148 : Nat := 118140960795 + 7057148 * 2 ^ 59
def prefixEnd_7057148 : Nat := 4983230072969 + 3 ^ 40 * 7057148 * 2
def baseEnd_7057148 : Nat := 1207902991305286703231591

theorem tailTrace_7057148 : CollatzResearch.WordTrace tailWord_7057148 prefixEnd_7057148 1207902991305286703231591 := by
  unfold tailWord_7057148
  simp only [CollatzResearch.WordTrace]
  refine ⟨128697666718582767883734049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171596888958110357178312065 128697666718582767883734049)
  ·
    refine ⟨96523250038937075912800537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128697666718582767883734049 96523250038937075912800537)
    ·
      refine ⟨72392437529202806934600403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96523250038937075912800537 72392437529202806934600403)
      ·
        refine ⟨108588656293804210401900605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72392437529202806934600403 108588656293804210401900605)
        ·
          refine ⟨40720746110176578900712727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108588656293804210401900605 40720746110176578900712727)
          ·
            refine ⟨61081119165264868351069091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40720746110176578900712727 61081119165264868351069091)
            ·
              refine ⟨91621678747897302526603637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61081119165264868351069091 91621678747897302526603637)
              ·
                refine ⟨8589532382615372111869091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 91621678747897302526603637 8589532382615372111869091)
                ·
                  refine ⟨12884298573923058167803637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8589532382615372111869091 12884298573923058167803637)
                  ·
                    refine ⟨1207902991305286703231591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12884298573923058167803637 1207902991305286703231591)
                    ·
                      rfl

theorem cell23_7057148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 5, 1, 5].length) (baseStart_7057148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7057148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7057148 prefixEnd_7057148 := by exact prefixLift 7057148
  have htrace : WordTrace (prefixWord ++ tailWord_7057148) baseStart_7057148 baseEnd_7057148 := by
    simpa [prefixWord, tailWord_7057148, baseEnd_7057148] using wordTrace_append hprefix tailTrace_7057148
  have hstable : (prefixWord ++ tailWord_7057148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7057148).length < 2 ^ (prefixWord ++ tailWord_7057148).sum := by decide
  have hdescent : baseEnd_7057148 < baseStart_7057148 := by decide
  rcases family_descends (prefixWord ++ tailWord_7057148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7057162 : List Nat := [3, 1, 2, 2, 1, 5, 1, 1, 3, 1, 3]
def baseStart_7057162 : Nat := 118140960795 + 7057162 * 2 ^ 59
def prefixEnd_7057162 : Nat := 4983230072969 + 3 ^ 40 * 7057162 * 2
def baseEnd_7057162 : Nat := 3623716162645023054919709

theorem tailTrace_7057162 : CollatzResearch.WordTrace tailWord_7057162 prefixEnd_7057162 3623716162645023054919709 := by
  unfold tailWord_7057162
  simp only [CollatzResearch.WordTrace]
  refine ⟨64348961014778704039619435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171597229372743210772318493 64348961014778704039619435)
  ·
    refine ⟨96523441522168056059429153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64348961014778704039619435 96523441522168056059429153)
    ·
      refine ⟨72392581141626042044571865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96523441522168056059429153 72392581141626042044571865)
      ·
        refine ⟨54294435856219531533428899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72392581141626042044571865 54294435856219531533428899)
        ·
          refine ⟨81441653784329297300143349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54294435856219531533428899 81441653784329297300143349)
          ·
            refine ⟨7635155042280871621888439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 81441653784329297300143349 7635155042280871621888439)
            ·
              refine ⟨11452732563421307432832659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7635155042280871621888439 11452732563421307432832659)
              ·
                refine ⟨17179098845131961149248989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11452732563421307432832659 17179098845131961149248989)
                ·
                  refine ⟨6442162066924485430968371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17179098845131961149248989 6442162066924485430968371)
                  ·
                    refine ⟨9663243100386728146452557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6442162066924485430968371 9663243100386728146452557)
                    ·
                      refine ⟨3623716162645023054919709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9663243100386728146452557 3623716162645023054919709)
                      ·
                        rfl

theorem cell23_7057162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 1, 1, 3, 1, 3].length) (baseStart_7057162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7057162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7057162 prefixEnd_7057162 := by exact prefixLift 7057162
  have htrace : WordTrace (prefixWord ++ tailWord_7057162) baseStart_7057162 baseEnd_7057162 := by
    simpa [prefixWord, tailWord_7057162, baseEnd_7057162] using wordTrace_append hprefix tailTrace_7057162
  have hstable : (prefixWord ++ tailWord_7057162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7057162).length < 2 ^ (prefixWord ++ tailWord_7057162).sum := by decide
  have hdescent : baseEnd_7057162 < baseStart_7057162 := by decide
  rcases family_descends (prefixWord ++ tailWord_7057162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7057171 : List Nat := [1, 1, 1, 2, 1, 3, 2, 3, 3, 1, 5]
def baseStart_7057171 : Nat := 118140960795 + 7057171 * 2 ^ 59
def prefixEnd_7057171 : Nat := 4983230072969 + 3 ^ 40 * 7057171 * 2
def baseEnd_7057171 : Nat := 3623720783970913519707167

theorem tailTrace_7057171 : CollatzResearch.WordTrace tailWord_7057171 prefixEnd_7057171 3623720783970913519707167 := by
  unfold tailWord_7057171
  simp only [CollatzResearch.WordTrace]
  refine ⟨257396172316082210695555367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171597448210721473797036911 257396172316082210695555367)
  ·
    refine ⟨386094258474123316043333051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257396172316082210695555367 386094258474123316043333051)
    ·
      refine ⟨579141387711184974064999577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 386094258474123316043333051 579141387711184974064999577)
      ·
        refine ⟨434356040783388730548749683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 579141387711184974064999577 434356040783388730548749683)
        ·
          refine ⟨651534061175083095823124525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 434356040783388730548749683 651534061175083095823124525)
          ·
            refine ⟨244325272940656160933671697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 651534061175083095823124525 244325272940656160933671697)
            ·
              refine ⟨183243954705492120700253773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 244325272940656160933671697 183243954705492120700253773)
              ·
                refine ⟨68716483014559545262595165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 183243954705492120700253773 68716483014559545262595165)
                ·
                  refine ⟨25768681130459829473473187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68716483014559545262595165 25768681130459829473473187)
                  ·
                    refine ⟨38653021695689744210209781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25768681130459829473473187 38653021695689744210209781)
                    ·
                      refine ⟨3623720783970913519707167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38653021695689744210209781 3623720783970913519707167)
                      ·
                        rfl

theorem cell23_7057171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 3, 3, 1, 5].length) (baseStart_7057171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7057171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7057171 prefixEnd_7057171 := by exact prefixLift 7057171
  have htrace : WordTrace (prefixWord ++ tailWord_7057171) baseStart_7057171 baseEnd_7057171 := by
    simpa [prefixWord, tailWord_7057171, baseEnd_7057171] using wordTrace_append hprefix tailTrace_7057171
  have hstable : (prefixWord ++ tailWord_7057171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7057171).length < 2 ^ (prefixWord ++ tailWord_7057171).sum := by decide
  have hdescent : baseEnd_7057171 < baseStart_7057171 := by decide
  rcases family_descends (prefixWord ++ tailWord_7057171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7057185 : List Nat := [1, 2, 3, 2, 1, 3, 3, 2, 1, 1, 4]
def baseStart_7057185 : Nat := 118140960795 + 7057185 * 2 ^ 59
def prefixEnd_7057185 : Nat := 4983230072969 + 3 ^ 40 * 7057185 * 2
def baseEnd_7057185 : Nat := 3623727972700076464932103

theorem tailTrace_7057185 : CollatzResearch.WordTrace tailWord_7057185 prefixEnd_7057185 3623727972700076464932103 := by
  unfold tailWord_7057185
  simp only [CollatzResearch.WordTrace]
  refine ⟨257396682938031491086565009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171597788625354327391043339 257396682938031491086565009)
  ·
    refine ⟨193047512203523618314923757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257396682938031491086565009 193047512203523618314923757)
    ·
      refine ⟨72392817076321356868096409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 193047512203523618314923757 72392817076321356868096409)
      ·
        refine ⟨54294612807241017651072307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72392817076321356868096409 54294612807241017651072307)
        ·
          refine ⟨81441919210861526476608461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54294612807241017651072307 81441919210861526476608461)
          ·
            refine ⟨30540719704073072428728173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81441919210861526476608461 30540719704073072428728173)
            ·
              refine ⟨11452769889027402160773065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30540719704073072428728173 11452769889027402160773065)
              ·
                refine ⟨8589577416770551620579799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11452769889027402160773065 8589577416770551620579799)
                ·
                  refine ⟨12884366125155827430869699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8589577416770551620579799 12884366125155827430869699)
                  ·
                    refine ⟨19326549187733741146304549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12884366125155827430869699 19326549187733741146304549)
                    ·
                      refine ⟨3623727972700076464932103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19326549187733741146304549 3623727972700076464932103)
                      ·
                        rfl

theorem cell23_7057185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 3, 2, 1, 1, 4].length) (baseStart_7057185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7057185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7057185 prefixEnd_7057185 := by exact prefixLift 7057185
  have htrace : WordTrace (prefixWord ++ tailWord_7057185) baseStart_7057185 baseEnd_7057185 := by
    simpa [prefixWord, tailWord_7057185, baseEnd_7057185] using wordTrace_append hprefix tailTrace_7057185
  have hstable : (prefixWord ++ tailWord_7057185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7057185).length < 2 ^ (prefixWord ++ tailWord_7057185).sum := by decide
  have hdescent : baseEnd_7057185 < baseStart_7057185 := by decide
  rcases family_descends (prefixWord ++ tailWord_7057185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7057202 : List Nat := [3, 2, 1, 1, 3, 3, 3, 1, 1, 1, 4]
def baseStart_7057202 : Nat := 118140960795 + 7057202 * 2 ^ 59
def prefixEnd_7057202 : Nat := 4983230072969 + 3 ^ 40 * 7057202 * 2
def baseEnd_7057202 : Nat := 3623736701871202898419525

theorem tailTrace_7057202 : CollatzResearch.WordTrace tailWord_7057202 prefixEnd_7057202 3623736701871202898419525 := by
  unfold tailWord_7057202
  simp only [CollatzResearch.WordTrace]
  refine ⟨64349325744742475747483465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171598201985979935326622573 64349325744742475747483465)
  ·
    refine ⟨48261994308556856810612599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64349325744742475747483465 48261994308556856810612599)
    ·
      refine ⟨72392991462835285215918899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48261994308556856810612599 72392991462835285215918899)
      ·
        refine ⟨108589487194252927823878349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72392991462835285215918899 108589487194252927823878349)
        ·
          refine ⟨40721057697844847933954381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108589487194252927823878349 40721057697844847933954381)
          ·
            refine ⟨15270396636691817975232893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40721057697844847933954381 15270396636691817975232893)
            ·
              refine ⟨5726398738759431740712335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15270396636691817975232893 5726398738759431740712335)
              ·
                refine ⟨8589598108139147611068503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5726398738759431740712335 8589598108139147611068503)
                ·
                  refine ⟨12884397162208721416602755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8589598108139147611068503 12884397162208721416602755)
                  ·
                    refine ⟨19326595743313082124904133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12884397162208721416602755 19326595743313082124904133)
                    ·
                      refine ⟨3623736701871202898419525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19326595743313082124904133 3623736701871202898419525)
                      ·
                        rfl

theorem cell23_7057202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 3, 1, 1, 1, 4].length) (baseStart_7057202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7057202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7057202 prefixEnd_7057202 := by exact prefixLift 7057202
  have htrace : WordTrace (prefixWord ++ tailWord_7057202) baseStart_7057202 baseEnd_7057202 := by
    simpa [prefixWord, tailWord_7057202, baseEnd_7057202] using wordTrace_append hprefix tailTrace_7057202
  have hstable : (prefixWord ++ tailWord_7057202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7057202).length < 2 ^ (prefixWord ++ tailWord_7057202).sum := by decide
  have hdescent : baseEnd_7057202 < baseStart_7057202 := by decide
  rcases family_descends (prefixWord ++ tailWord_7057202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7057219 : List Nat := [1, 1, 1, 3, 1, 6, 1, 4, 1, 2, 2]
def baseStart_7057219 : Nat := 118140960795 + 7057219 * 2 ^ 59
def prefixEnd_7057219 : Nat := 4983230072969 + 3 ^ 40 * 7057219 * 2
def baseEnd_7057219 : Nat := 3623745431042329331906947

theorem tailTrace_7057219 : CollatzResearch.WordTrace tailWord_7057219 prefixEnd_7057219 3623745431042329331906947 := by
  unfold tailWord_7057219
  simp only [CollatzResearch.WordTrace]
  refine ⟨257397923019908314893302711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171598615346605543262201807 257397923019908314893302711)
  ·
    refine ⟨386096884529862472339954067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257397923019908314893302711 386096884529862472339954067)
    ·
      refine ⟨579145326794793708509931101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 386096884529862472339954067 579145326794793708509931101)
      ·
        refine ⟨217179497548047640691224163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 579145326794793708509931101 217179497548047640691224163)
        ·
          refine ⟨325769246322071461036836245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217179497548047640691224163 325769246322071461036836245)
          ·
            refine ⟨15270433421347099736101699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 325769246322071461036836245 15270433421347099736101699)
            ·
              refine ⟨22905650132020649604152549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15270433421347099736101699 22905650132020649604152549)
              ·
                refine ⟨4294809399753871800778603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22905650132020649604152549 4294809399753871800778603)
                ·
                  refine ⟨6442214099630807701167905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4294809399753871800778603 6442214099630807701167905)
                  ·
                    refine ⟨4831660574723105775875929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6442214099630807701167905 4831660574723105775875929)
                    ·
                      refine ⟨3623745431042329331906947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4831660574723105775875929 3623745431042329331906947)
                      ·
                        rfl

theorem cell23_7057219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 4, 1, 2, 2].length) (baseStart_7057219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7057219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7057219 prefixEnd_7057219 := by exact prefixLift 7057219
  have htrace : WordTrace (prefixWord ++ tailWord_7057219) baseStart_7057219 baseEnd_7057219 := by
    simpa [prefixWord, tailWord_7057219, baseEnd_7057219] using wordTrace_append hprefix tailTrace_7057219
  have hstable : (prefixWord ++ tailWord_7057219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7057219).length < 2 ^ (prefixWord ++ tailWord_7057219).sum := by decide
  have hdescent : baseEnd_7057219 < baseStart_7057219 := by decide
  rcases family_descends (prefixWord ++ tailWord_7057219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7057221 : List Nat := [1, 3, 1, 1, 1, 2, 3, 1, 1, 9]
def baseStart_7057221 : Nat := 118140960795 + 7057221 * 2 ^ 59
def prefixEnd_7057221 : Nat := 4983230072969 + 3 ^ 40 * 7057221 * 2
def baseEnd_7057221 : Nat := 1207915486001212774693979

theorem tailTrace_7057221 : CollatzResearch.WordTrace tailWord_7057221 prefixEnd_7057221 1207915486001212774693979 := by
  unfold tailWord_7057221
  simp only [CollatzResearch.WordTrace]
  refine ⟨257397995965901069234875517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171598663977267379489917011 257397995965901069234875517)
  ·
    refine ⟨96524248487212900963078319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 257397995965901069234875517 96524248487212900963078319)
    ·
      refine ⟨144786372730819351444617479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96524248487212900963078319 144786372730819351444617479)
      ·
        refine ⟨217179559096229027166926219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144786372730819351444617479 217179559096229027166926219)
        ·
          refine ⟨325769338644343540750389329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217179559096229027166926219 325769338644343540750389329)
          ·
            refine ⟨244327003983257655562791997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 325769338644343540750389329 244327003983257655562791997)
            ·
              refine ⟨91622626493721620836046999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 244327003983257655562791997 91622626493721620836046999)
              ·
                refine ⟨137433939740582431254070499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91622626493721620836046999 137433939740582431254070499)
                ·
                  refine ⟨206150909610873646881105749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 137433939740582431254070499 206150909610873646881105749)
                  ·
                    refine ⟨1207915486001212774693979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 206150909610873646881105749 1207915486001212774693979)
                    ·
                      rfl

theorem cell23_7057221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 1, 1, 9].length) (baseStart_7057221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7057221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7057221 prefixEnd_7057221 := by exact prefixLift 7057221
  have htrace : WordTrace (prefixWord ++ tailWord_7057221) baseStart_7057221 baseEnd_7057221 := by
    simpa [prefixWord, tailWord_7057221, baseEnd_7057221] using wordTrace_append hprefix tailTrace_7057221
  have hstable : (prefixWord ++ tailWord_7057221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7057221).length < 2 ^ (prefixWord ++ tailWord_7057221).sum := by decide
  have hdescent : baseEnd_7057221 < baseStart_7057221 := by decide
  rcases family_descends (prefixWord ++ tailWord_7057221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7057335 : List Nat := [1, 1, 3, 1, 3, 1, 1, 3, 2, 5, 2]
def baseStart_7057335 : Nat := 118140960795 + 7057335 * 2 ^ 59
def prefixEnd_7057335 : Nat := 4983230072969 + 3 ^ 40 * 7057335 * 2
def baseEnd_7057335 : Nat := 3623804994798250878056413

theorem tailTrace_7057335 : CollatzResearch.WordTrace tailWord_7057335 prefixEnd_7057335 3623804994798250878056413 := by
  unfold tailWord_7057335
  simp only [CollatzResearch.WordTrace]
  refine ⟨257402153887488066704525459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171601435924992044469683639 257402153887488066704525459)
  ·
    refine ⟨386103230831232100056788189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257402153887488066704525459 386103230831232100056788189)
    ·
      refine ⟨144788711561712037521295571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 386103230831232100056788189 144788711561712037521295571)
      ·
        refine ⟨217183067342568056281943357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144788711561712037521295571 217183067342568056281943357)
        ·
          refine ⟨81443650253463021105728759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 217183067342568056281943357 81443650253463021105728759)
          ·
            refine ⟨122165475380194531658593139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81443650253463021105728759 122165475380194531658593139)
            ·
              refine ⟨183248213070291797487889709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122165475380194531658593139 183248213070291797487889709)
              ·
                refine ⟨68718079901359424057958641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 183248213070291797487889709 68718079901359424057958641)
                ·
                  refine ⟨51538559926019568043468981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68718079901359424057958641 51538559926019568043468981)
                  ·
                    refine ⟨4831739993064334504075217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51538559926019568043468981 4831739993064334504075217)
                    ·
                      refine ⟨3623804994798250878056413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4831739993064334504075217 3623804994798250878056413)
                      ·
                        rfl

theorem cell23_7057335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 3, 2, 5, 2].length) (baseStart_7057335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7057335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7057335 prefixEnd_7057335 := by exact prefixLift 7057335
  have htrace : WordTrace (prefixWord ++ tailWord_7057335) baseStart_7057335 baseEnd_7057335 := by
    simpa [prefixWord, tailWord_7057335, baseEnd_7057335] using wordTrace_append hprefix tailTrace_7057335
  have hstable : (prefixWord ++ tailWord_7057335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7057335).length < 2 ^ (prefixWord ++ tailWord_7057335).sum := by decide
  have hdescent : baseEnd_7057335 < baseStart_7057335 := by decide
  rcases family_descends (prefixWord ++ tailWord_7057335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7057388 : List Nat := [2, 2, 1, 1, 2, 1, 1, 5, 8]
def baseStart_7057388 : Nat := 118140960795 + 7057388 * 2 ^ 59
def prefixEnd_7057388 : Nat := 4983230072969 + 3 ^ 40 * 7057388 * 2
def baseEnd_7057388 : Nat := 402648023252548796743741

theorem tailTrace_7057388 : CollatzResearch.WordTrace tailWord_7057388 prefixEnd_7057388 402648023252548796743741 := by
  unfold tailWord_7057388
  simp only [CollatzResearch.WordTrace]
  refine ⟨128702043478148028378102409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171602724637530704504136545 128702043478148028378102409)
  ·
    refine ⟨96526532608611021283576807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128702043478148028378102409 96526532608611021283576807)
    ·
      refine ⟨144789798912916531925365211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96526532608611021283576807 144789798912916531925365211)
      ·
        refine ⟨217184698369374797888047817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144789798912916531925365211 217184698369374797888047817)
        ·
          refine ⟨162888523777031098416035863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 217184698369374797888047817 162888523777031098416035863)
          ·
            refine ⟨244332785665546647624053795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162888523777031098416035863 244332785665546647624053795)
            ·
              refine ⟨366499178498319971436080693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 244332785665546647624053795 366499178498319971436080693)
              ·
                refine ⟨34359297984217497322132565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 366499178498319971436080693 34359297984217497322132565)
                ·
                  refine ⟨402648023252548796743741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34359297984217497322132565 402648023252548796743741)
                  ·
                    rfl

theorem cell23_7057388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 8].length) (baseStart_7057388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7057388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7057388 prefixEnd_7057388 := by exact prefixLift 7057388
  have htrace : WordTrace (prefixWord ++ tailWord_7057388) baseStart_7057388 baseEnd_7057388 := by
    simpa [prefixWord, tailWord_7057388, baseEnd_7057388] using wordTrace_append hprefix tailTrace_7057388
  have hstable : (prefixWord ++ tailWord_7057388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7057388).length < 2 ^ (prefixWord ++ tailWord_7057388).sum := by decide
  have hdescent : baseEnd_7057388 < baseStart_7057388 := by decide
  rcases family_descends (prefixWord ++ tailWord_7057388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7057405 : List Nat := [1, 4, 1, 1, 1, 2, 4, 3, 6]
def baseStart_7057405 : Nat := 118140960795 + 7057405 * 2 ^ 59
def prefixEnd_7057405 : Nat := 4983230072969 + 3 ^ 40 * 7057405 * 2
def baseEnd_7057405 : Nat := 402648993160451733797899

theorem tailTrace_7057405 : CollatzResearch.WordTrace tailWord_7057405 prefixEnd_7057405 402648993160451733797899 := by
  unfold tailWord_7057405
  simp only [CollatzResearch.WordTrace]
  refine ⟨257404706997234468659573669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171603137998156312439715779 257404706997234468659573669)
  ·
    refine ⟨48263382561981462873670063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 257404706997234468659573669 48263382561981462873670063)
    ·
      refine ⟨72395073842972194310505095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48263382561981462873670063 72395073842972194310505095)
      ·
        refine ⟨108592610764458291465757643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72395073842972194310505095 108592610764458291465757643)
        ·
          refine ⟨162888916146687437198636465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108592610764458291465757643 162888916146687437198636465)
          ·
            refine ⟨122166687110015577898977349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162888916146687437198636465 122166687110015577898977349)
            ·
              refine ⟨22906253833127920856058253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 122166687110015577898977349 22906253833127920856058253)
              ·
                refine ⟨8589845187422970321021845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22906253833127920856058253 8589845187422970321021845)
                ·
                  refine ⟨402648993160451733797899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8589845187422970321021845 402648993160451733797899)
                  ·
                    rfl

theorem cell23_7057405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 3, 6].length) (baseStart_7057405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7057405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7057405 prefixEnd_7057405 := by exact prefixLift 7057405
  have htrace : WordTrace (prefixWord ++ tailWord_7057405) baseStart_7057405 baseEnd_7057405 := by
    simpa [prefixWord, tailWord_7057405, baseEnd_7057405] using wordTrace_append hprefix tailTrace_7057405
  have hstable : (prefixWord ++ tailWord_7057405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7057405).length < 2 ^ (prefixWord ++ tailWord_7057405).sum := by decide
  have hdescent : baseEnd_7057405 < baseStart_7057405 := by decide
  rcases family_descends (prefixWord ++ tailWord_7057405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7057408 : List Nat := [2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 6]
def baseStart_7057408 : Nat := 118140960795 + 7057408 * 2 ^ 59
def prefixEnd_7057408 : Nat := 4983230072969 + 3 ^ 40 * 7057408 * 2
def baseEnd_7057408 : Nat := 3623842478886029092443577

theorem tailTrace_7057408 : CollatzResearch.WordTrace tailWord_7057408 prefixEnd_7057408 3623842478886029092443577 := by
  unfold tailWord_7057408
  simp only [CollatzResearch.WordTrace]
  refine ⟨128702408208111800085966439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171603210944149066781288585 128702408208111800085966439)
  ·
    refine ⟨193053612312167700128949659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128702408208111800085966439 193053612312167700128949659)
    ·
      refine ⟨289580418468251550193424489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193053612312167700128949659 289580418468251550193424489)
      ·
        refine ⟨217185313851188662645068367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 289580418468251550193424489 217185313851188662645068367)
        ·
          refine ⟨325777970776782993967602551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217185313851188662645068367 325777970776782993967602551)
          ·
            refine ⟨488666956165174490951403827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 325777970776782993967602551 488666956165174490951403827)
            ·
              refine ⟨733000434247761736427105741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 488666956165174490951403827 733000434247761736427105741)
              ·
                refine ⟨274875162842910651160164653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 733000434247761736427105741 274875162842910651160164653)
                ·
                  refine ⟨103078186066091494185061745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 274875162842910651160164653 103078186066091494185061745)
                  ·
                    refine ⟨77308639549568620638796309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 103078186066091494185061745 77308639549568620638796309)
                    ·
                      refine ⟨3623842478886029092443577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 77308639549568620638796309 3623842478886029092443577)
                      ·
                        rfl

theorem cell23_7057408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 6].length) (baseStart_7057408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7057408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7057408 prefixEnd_7057408 := by exact prefixLift 7057408
  have htrace : WordTrace (prefixWord ++ tailWord_7057408) baseStart_7057408 baseEnd_7057408 := by
    simpa [prefixWord, tailWord_7057408, baseEnd_7057408] using wordTrace_append hprefix tailTrace_7057408
  have hstable : (prefixWord ++ tailWord_7057408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7057408).length < 2 ^ (prefixWord ++ tailWord_7057408).sum := by decide
  have hdescent : baseEnd_7057408 < baseStart_7057408 := by decide
  rcases family_descends (prefixWord ++ tailWord_7057408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7057432 : List Nat := [2, 1, 2, 3, 2, 1, 1, 2, 5, 1, 3]
def baseStart_7057432 : Nat := 118140960795 + 7057432 * 2 ^ 59
def prefixEnd_7057432 : Nat := 4983230072969 + 3 ^ 40 * 7057432 * 2
def baseEnd_7057432 : Nat := 3623854802421736998543467

theorem tailTrace_7057432 : CollatzResearch.WordTrace tailWord_7057432 prefixEnd_7057432 3623854802421736998543467 := by
  unfold tailWord_7057432
  simp only [CollatzResearch.WordTrace]
  refine ⟨128702845884068326135403275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171603794512091101513871033 128702845884068326135403275)
  ·
    refine ⟨193054268826102489203104913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128702845884068326135403275 193054268826102489203104913)
    ·
      refine ⟨144790701619576866902328685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193054268826102489203104913 144790701619576866902328685)
      ·
        refine ⟨54296513107341325088373257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144790701619576866902328685 54296513107341325088373257)
        ·
          refine ⟨40722384830505993816279943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54296513107341325088373257 40722384830505993816279943)
          ·
            refine ⟨61083577245758990724419915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40722384830505993816279943 61083577245758990724419915)
            ·
              refine ⟨91625365868638486086629873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61083577245758990724419915 91625365868638486086629873)
              ·
                refine ⟨68719024401478864564972405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91625365868638486086629873 68719024401478864564972405)
                ·
                  refine ⟨6442408537638643552966163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 68719024401478864564972405 6442408537638643552966163)
                  ·
                    refine ⟨9663612806457965329449245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6442408537638643552966163 9663612806457965329449245)
                    ·
                      refine ⟨3623854802421736998543467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9663612806457965329449245 3623854802421736998543467)
                      ·
                        rfl

theorem cell23_7057432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 2, 5, 1, 3].length) (baseStart_7057432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7057432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7057432 prefixEnd_7057432 := by exact prefixLift 7057432
  have htrace : WordTrace (prefixWord ++ tailWord_7057432) baseStart_7057432 baseEnd_7057432 := by
    simpa [prefixWord, tailWord_7057432, baseEnd_7057432] using wordTrace_append hprefix tailTrace_7057432
  have hstable : (prefixWord ++ tailWord_7057432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7057432).length < 2 ^ (prefixWord ++ tailWord_7057432).sum := by decide
  have hdescent : baseEnd_7057432 < baseStart_7057432 := by decide
  rcases family_descends (prefixWord ++ tailWord_7057432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7057455 : List Nat := [1, 1, 2, 1, 2, 1, 1, 6, 3, 1, 4]
def baseStart_7057455 : Nat := 118140960795 + 7057455 * 2 ^ 59
def prefixEnd_7057455 : Nat := 4983230072969 + 3 ^ 40 * 7057455 * 2
def baseEnd_7057455 : Nat := 3623866612476790408555861

theorem tailTrace_7057455 : CollatzResearch.WordTrace tailWord_7057455 prefixEnd_7057455 3623866612476790408555861 := by
  unfold tailWord_7057455
  simp only [CollatzResearch.WordTrace]
  refine ⟨257406530647053327198893819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171604353764702218132595879 257406530647053327198893819)
  ·
    refine ⟨386109795970579990798340729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257406530647053327198893819 386109795970579990798340729)
    ·
      refine ⟨289582346977934993098755547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 386109795970579990798340729 289582346977934993098755547)
      ·
        refine ⟨434373520466902489648133321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 289582346977934993098755547 434373520466902489648133321)
        ·
          refine ⟨325780140350176867236099991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 434373520466902489648133321 325780140350176867236099991)
          ·
            refine ⟨488670210525265300854149987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 325780140350176867236099991 488670210525265300854149987)
            ·
              refine ⟨733005315787897951281224981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 488670210525265300854149987 733005315787897951281224981)
              ·
                refine ⟨34359624177557716466307421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 733005315787897951281224981 34359624177557716466307421)
                ·
                  refine ⟨12884859066584143674865283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34359624177557716466307421 12884859066584143674865283)
                  ·
                    refine ⟨19327288599876215512297925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12884859066584143674865283 19327288599876215512297925)
                    ·
                      refine ⟨3623866612476790408555861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19327288599876215512297925 3623866612476790408555861)
                      ·
                        rfl

theorem cell23_7057455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 6, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 6, 3, 1, 4].length) (baseStart_7057455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7057455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7057455 prefixEnd_7057455 := by exact prefixLift 7057455
  have htrace : WordTrace (prefixWord ++ tailWord_7057455) baseStart_7057455 baseEnd_7057455 := by
    simpa [prefixWord, tailWord_7057455, baseEnd_7057455] using wordTrace_append hprefix tailTrace_7057455
  have hstable : (prefixWord ++ tailWord_7057455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7057455).length < 2 ^ (prefixWord ++ tailWord_7057455).sum := by decide
  have hdescent : baseEnd_7057455 < baseStart_7057455 := by decide
  rcases family_descends (prefixWord ++ tailWord_7057455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7057472 : List Nat := [2, 1, 1, 2, 2, 4, 1, 4, 1, 1, 4]
def baseStart_7057472 : Nat := 118140960795 + 7057472 * 2 ^ 59
def prefixEnd_7057472 : Nat := 4983230072969 + 3 ^ 40 * 7057472 * 2
def baseEnd_7057472 : Nat := 3623875341647916842043283

theorem tailTrace_7057472 : CollatzResearch.WordTrace tailWord_7057472 prefixEnd_7057472 3623875341647916842043283 := by
  unfold tailWord_7057472
  simp only [CollatzResearch.WordTrace]
  refine ⟨128703575343995869551131335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171604767125327826068175113 128703575343995869551131335)
  ·
    refine ⟨193055363015993804326697003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128703575343995869551131335 193055363015993804326697003)
    ·
      refine ⟨289583044523990706490045505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193055363015993804326697003 289583044523990706490045505)
      ·
        refine ⟨217187283392993029867534129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 289583044523990706490045505 217187283392993029867534129)
        ·
          refine ⟨162890462544744772400650597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 217187283392993029867534129 162890462544744772400650597)
          ·
            refine ⟨30541961727139644825121987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 162890462544744772400650597 30541961727139644825121987)
            ·
              refine ⟨45812942590709467237682981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30541961727139644825121987 45812942590709467237682981)
              ·
                refine ⟨8589926735758025107065559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45812942590709467237682981 8589926735758025107065559)
                ·
                  refine ⟨12884890103637037660598339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8589926735758025107065559 12884890103637037660598339)
                  ·
                    refine ⟨19327335155455556490897509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12884890103637037660598339 19327335155455556490897509)
                    ·
                      refine ⟨3623875341647916842043283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19327335155455556490897509 3623875341647916842043283)
                      ·
                        rfl

theorem cell23_7057472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 4, 1, 1, 4].length) (baseStart_7057472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7057472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7057472 prefixEnd_7057472 := by exact prefixLift 7057472
  have htrace : WordTrace (prefixWord ++ tailWord_7057472) baseStart_7057472 baseEnd_7057472 := by
    simpa [prefixWord, tailWord_7057472, baseEnd_7057472] using wordTrace_append hprefix tailTrace_7057472
  have hstable : (prefixWord ++ tailWord_7057472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7057472).length < 2 ^ (prefixWord ++ tailWord_7057472).sum := by decide
  have hdescent : baseEnd_7057472 < baseStart_7057472 := by decide
  rcases family_descends (prefixWord ++ tailWord_7057472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7057492 : List Nat := [2, 4, 1, 1, 1, 1, 1, 2, 5, 2, 3]
def baseStart_7057492 : Nat := 118140960795 + 7057492 * 2 ^ 59
def prefixEnd_7057492 : Nat := 4983230072969 + 3 ^ 40 * 7057492 * 2
def baseEnd_7057492 : Nat := 3623885611261006763793191

theorem tailTrace_7057492 : CollatzResearch.WordTrace tailWord_7057492 prefixEnd_7057492 3623885611261006763793191 := by
  unfold tailWord_7057492
  simp only [CollatzResearch.WordTrace]
  refine ⟨128703940073959641258995365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171605253431946188345327153 128703940073959641258995365)
  ·
    refine ⟨24131988763867432736061631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 128703940073959641258995365 24131988763867432736061631)
    ·
      refine ⟨36197983145801149104092447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24131988763867432736061631 36197983145801149104092447)
      ·
        refine ⟨54296974718701723656138671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36197983145801149104092447 54296974718701723656138671)
        ·
          refine ⟨81445462078052585484208007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54296974718701723656138671 81445462078052585484208007)
          ·
            refine ⟨122168193117078878226312011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81445462078052585484208007 122168193117078878226312011)
            ·
              refine ⟨183252289675618317339468017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122168193117078878226312011 183252289675618317339468017)
              ·
                refine ⟨137439217256713738004601013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 183252289675618317339468017 137439217256713738004601013)
                ·
                  refine ⟨12884926617816912937931345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 137439217256713738004601013 12884926617816912937931345)
                  ·
                    refine ⟨9663694963362684703448509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12884926617816912937931345 9663694963362684703448509)
                    ·
                      refine ⟨3623885611261006763793191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9663694963362684703448509 3623885611261006763793191)
                      ·
                        rfl

theorem cell23_7057492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 2, 5, 2, 3].length) (baseStart_7057492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7057492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7057492 prefixEnd_7057492 := by exact prefixLift 7057492
  have htrace : WordTrace (prefixWord ++ tailWord_7057492) baseStart_7057492 baseEnd_7057492 := by
    simpa [prefixWord, tailWord_7057492, baseEnd_7057492] using wordTrace_append hprefix tailTrace_7057492
  have hstable : (prefixWord ++ tailWord_7057492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7057492).length < 2 ^ (prefixWord ++ tailWord_7057492).sum := by decide
  have hdescent : baseEnd_7057492 < baseStart_7057492 := by decide
  rcases family_descends (prefixWord ++ tailWord_7057492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7057516 : List Nat := [2, 2, 1, 1, 3, 5, 2, 1, 2, 4]
def baseStart_7057516 : Nat := 118140960795 + 7057516 * 2 ^ 59
def prefixEnd_7057516 : Nat := 4983230072969 + 3 ^ 40 * 7057516 * 2
def baseEnd_7057516 : Nat := 1207965978265571556631027

theorem tailTrace_7057516 : CollatzResearch.WordTrace tailWord_7057516 prefixEnd_7057516 1207965978265571556631027 := by
  unfold tailWord_7057516
  simp only [CollatzResearch.WordTrace]
  refine ⟨128704377749916167308432201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171605836999888223077909601 128704377749916167308432201)
  ·
    refine ⟨96528283312437125481324151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128704377749916167308432201 96528283312437125481324151)
    ·
      refine ⟨144792424968655688221986227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96528283312437125481324151 144792424968655688221986227)
      ·
        refine ⟨217188637452983532332979341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144792424968655688221986227 217188637452983532332979341)
        ·
          refine ⟨81445739044868824624867253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 217188637452983532332979341 81445739044868824624867253)
          ·
            refine ⟨7635538035456452308581305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 81445739044868824624867253 7635538035456452308581305)
            ·
              refine ⟨5726653526592339231435979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7635538035456452308581305 5726653526592339231435979)
              ·
                refine ⟨8589980289888508847153969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5726653526592339231435979 8589980289888508847153969)
                ·
                  refine ⟨6442485217416381635365477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8589980289888508847153969 6442485217416381635365477)
                  ·
                    refine ⟨1207965978265571556631027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6442485217416381635365477 1207965978265571556631027)
                    ·
                      rfl

theorem cell23_7057516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 4].length) (baseStart_7057516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7057516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7057516 prefixEnd_7057516 := by exact prefixLift 7057516
  have htrace : WordTrace (prefixWord ++ tailWord_7057516) baseStart_7057516 baseEnd_7057516 := by
    simpa [prefixWord, tailWord_7057516, baseEnd_7057516] using wordTrace_append hprefix tailTrace_7057516
  have hstable : (prefixWord ++ tailWord_7057516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7057516).length < 2 ^ (prefixWord ++ tailWord_7057516).sum := by decide
  have hdescent : baseEnd_7057516 < baseStart_7057516 := by decide
  rcases family_descends (prefixWord ++ tailWord_7057516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7057526 : List Nat := [5, 1, 1, 2, 1, 2, 3, 2, 1, 2, 3]
def baseStart_7057526 : Nat := 118140960795 + 7057526 * 2 ^ 59
def prefixEnd_7057526 : Nat := 4983230072969 + 3 ^ 40 * 7057526 * 2
def baseEnd_7057526 : Nat := 3623903069603259630768035

theorem tailTrace_7057526 : CollatzResearch.WordTrace tailWord_7057526 prefixEnd_7057526 3623903069603259630768035 := by
  unfold tailWord_7057526
  simp only [CollatzResearch.WordTrace]
  refine ⟨16088070014362256645295527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 171606080153197404216485621 16088070014362256645295527)
  ·
    refine ⟨24132105021543384967943291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16088070014362256645295527 24132105021543384967943291)
    ·
      refine ⟨36198157532315077451914937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24132105021543384967943291 36198157532315077451914937)
      ·
        refine ⟨27148618149236308088936203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36198157532315077451914937 27148618149236308088936203)
        ·
          refine ⟨40722927223854462133404305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27148618149236308088936203 40722927223854462133404305)
          ·
            refine ⟨30542195417890846600053229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40722927223854462133404305 30542195417890846600053229)
            ·
              refine ⟨11453323281709067475019961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30542195417890846600053229 11453323281709067475019961)
              ·
                refine ⟨8589992461281800606264971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11453323281709067475019961 8589992461281800606264971)
                ·
                  refine ⟨12884988691922700909397457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8589992461281800606264971 12884988691922700909397457)
                  ·
                    refine ⟨9663741518942025682048093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12884988691922700909397457 9663741518942025682048093)
                    ·
                      refine ⟨3623903069603259630768035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9663741518942025682048093 3623903069603259630768035)
                      ·
                        rfl

theorem cell23_7057526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 3, 2, 1, 2, 3].length) (baseStart_7057526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7057526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7057526 prefixEnd_7057526 := by exact prefixLift 7057526
  have htrace : WordTrace (prefixWord ++ tailWord_7057526) baseStart_7057526 baseEnd_7057526 := by
    simpa [prefixWord, tailWord_7057526, baseEnd_7057526] using wordTrace_append hprefix tailTrace_7057526
  have hstable : (prefixWord ++ tailWord_7057526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7057526).length < 2 ^ (prefixWord ++ tailWord_7057526).sum := by decide
  have hdescent : baseEnd_7057526 < baseStart_7057526 := by decide
  rcases family_descends (prefixWord ++ tailWord_7057526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7057555 : List Nat := [1, 1, 1, 2, 1, 2, 3, 4, 2, 6]
def baseStart_7057555 : Nat := 118140960795 + 7057555 * 2 ^ 59
def prefixEnd_7057555 : Nat := 4983230072969 + 3 ^ 40 * 7057555 * 2
def baseEnd_7057555 : Nat := 1207972653514080005768467

theorem tailTrace_7057555 : CollatzResearch.WordTrace tailWord_7057555 prefixEnd_7057555 1207972653514080005768467 := by
  unfold tailWord_7057555
  simp only [CollatzResearch.WordTrace]
  refine ⟨257410177946691044277534119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171606785297794029518356079 257410177946691044277534119)
  ·
    refine ⟨386115266920036566416301179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257410177946691044277534119 386115266920036566416301179)
    ·
      refine ⟨579172900380054849624451769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 386115266920036566416301179 579172900380054849624451769)
      ·
        refine ⟨434379675285041137218338827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 579172900380054849624451769 434379675285041137218338827)
        ·
          refine ⟨651569512927561705827508241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 434379675285041137218338827 651569512927561705827508241)
          ·
            refine ⟨488677134695671279370631181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 651569512927561705827508241 488677134695671279370631181)
            ·
              refine ⟨183253925510876729763986693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 488677134695671279370631181 183253925510876729763986693)
              ·
                refine ⟨34360111033289386830747505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 183253925510876729763986693 34360111033289386830747505)
                ·
                  refine ⟨25770083274967040123060629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34360111033289386830747505 25770083274967040123060629)
                  ·
                    refine ⟨1207972653514080005768467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25770083274967040123060629 1207972653514080005768467)
                    ·
                      rfl

theorem cell23_7057555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 4, 2, 6].length) (baseStart_7057555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7057555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7057555 prefixEnd_7057555 := by exact prefixLift 7057555
  have htrace : WordTrace (prefixWord ++ tailWord_7057555) baseStart_7057555 baseEnd_7057555 := by
    simpa [prefixWord, tailWord_7057555, baseEnd_7057555] using wordTrace_append hprefix tailTrace_7057555
  have hstable : (prefixWord ++ tailWord_7057555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7057555).length < 2 ^ (prefixWord ++ tailWord_7057555).sum := by decide
  have hdescent : baseEnd_7057555 < baseStart_7057555 := by decide
  rcases family_descends (prefixWord ++ tailWord_7057555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7057666 : List Nat := [3, 4, 1, 1, 2, 2, 1, 2, 2, 5]
def baseStart_7057666 : Nat := 118140960795 + 7057666 * 2 ^ 59
def prefixEnd_7057666 : Nat := 4983230072969 + 3 ^ 40 * 7057666 * 2
def baseEnd_7057666 : Nat := 1207991652298296361005797

theorem tailTrace_7057666 : CollatzResearch.WordTrace tailWord_7057666 prefixEnd_7057666 1207991652298296361005797 := by
  unfold tailWord_7057666
  simp only [CollatzResearch.WordTrace]
  refine ⟨64353556612322227558706213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171609484299525940156549901 64353556612322227558706213)
  ·
    refine ⟨12066291864810417667257415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64353556612322227558706213 12066291864810417667257415)
    ·
      refine ⟨18099437797215626500886123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12066291864810417667257415 18099437797215626500886123)
      ·
        refine ⟨27149156695823439751329185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18099437797215626500886123 27149156695823439751329185)
        ·
          refine ⟨20361867521867579813496889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27149156695823439751329185 20361867521867579813496889)
          ·
            refine ⟨15271400641400684860122667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20361867521867579813496889 15271400641400684860122667)
            ·
              refine ⟨22907100962101027290184001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15271400641400684860122667 22907100962101027290184001)
              ·
                refine ⟨17180325721575770467638001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22907100962101027290184001 17180325721575770467638001)
                ·
                  refine ⟨12885244291181827850728501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17180325721575770467638001 12885244291181827850728501)
                  ·
                    refine ⟨1207991652298296361005797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12885244291181827850728501 1207991652298296361005797)
                    ·
                      rfl

theorem cell23_7057666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 2, 2, 5].length) (baseStart_7057666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7057666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7057666 prefixEnd_7057666 := by exact prefixLift 7057666
  have htrace : WordTrace (prefixWord ++ tailWord_7057666) baseStart_7057666 baseEnd_7057666 := by
    simpa [prefixWord, tailWord_7057666, baseEnd_7057666] using wordTrace_append hprefix tailTrace_7057666
  have hstable : (prefixWord ++ tailWord_7057666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7057666).length < 2 ^ (prefixWord ++ tailWord_7057666).sum := by decide
  have hdescent : baseEnd_7057666 < baseStart_7057666 := by decide
  rcases family_descends (prefixWord ++ tailWord_7057666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7057669 : List Nat := [1, 3, 1, 1, 2, 1, 2, 4, 2, 4, 2]
def baseStart_7057669 : Nat := 118140960795 + 7057669 * 2 ^ 59
def prefixEnd_7057669 : Nat := 4983230072969 + 3 ^ 40 * 7057669 * 2
def baseEnd_7057669 : Nat := 3623976497336852571279877

theorem tailTrace_7057669 : CollatzResearch.WordTrace tailWord_7057669 prefixEnd_7057669 3623976497336852571279877 := by
  unfold tailWord_7057669
  simp only [CollatzResearch.WordTrace]
  refine ⟨257414335868278041747184061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171609557245518694498122707 257414335868278041747184061)
  ·
    refine ⟨96530375950604265655194023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 257414335868278041747184061 96530375950604265655194023)
    ·
      refine ⟨144795563925906398482791035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96530375950604265655194023 144795563925906398482791035)
      ·
        refine ⟨217193345888859597724186553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144795563925906398482791035 217193345888859597724186553)
        ·
          refine ⟨162895009416644698293139915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 217193345888859597724186553 162895009416644698293139915)
          ·
            refine ⟨244342514124967047439709873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162895009416644698293139915 244342514124967047439709873)
            ·
              refine ⟨183256885593725285579782405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 244342514124967047439709873 183256885593725285579782405)
              ·
                refine ⟨34360666048823491046209201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 183256885593725285579782405 34360666048823491046209201)
                ·
                  refine ⟨25770499536617618284656901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34360666048823491046209201 25770499536617618284656901)
                  ·
                    refine ⟨4831968663115803428373169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25770499536617618284656901 4831968663115803428373169)
                    ·
                      refine ⟨3623976497336852571279877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4831968663115803428373169 3623976497336852571279877)
                      ·
                        rfl

theorem cell23_7057669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 4, 2, 4, 2].length) (baseStart_7057669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7057669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7057669 prefixEnd_7057669 := by exact prefixLift 7057669
  have htrace : WordTrace (prefixWord ++ tailWord_7057669) baseStart_7057669 baseEnd_7057669 := by
    simpa [prefixWord, tailWord_7057669, baseEnd_7057669] using wordTrace_append hprefix tailTrace_7057669
  have hstable : (prefixWord ++ tailWord_7057669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7057669).length < 2 ^ (prefixWord ++ tailWord_7057669).sum := by decide
  have hdescent : baseEnd_7057669 < baseStart_7057669 := by decide
  rcases family_descends (prefixWord ++ tailWord_7057669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7057726 : List Nat := [4, 2, 1, 2, 1, 3, 2, 2, 6]
def baseStart_7057726 : Nat := 118140960795 + 7057726 * 2 ^ 59
def prefixEnd_7057726 : Nat := 4983230072969 + 3 ^ 40 * 7057726 * 2
def baseEnd_7057726 : Nat := 402667307303795427585235

theorem tailTrace_7057726 : CollatzResearch.WordTrace tailWord_7057726 prefixEnd_7057726 402667307303795427585235 := by
  unfold tailWord_7057726
  simp only [CollatzResearch.WordTrace]
  refine ⟨32177051853633942560251129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 171610943219381026988006021 32177051853633942560251129)
  ·
    refine ⟨24132788890225456920188347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32177051853633942560251129 24132788890225456920188347)
    ·
      refine ⟨36199183335338185380282521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24132788890225456920188347 36199183335338185380282521)
      ·
        refine ⟨27149387501503639035211891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36199183335338185380282521 27149387501503639035211891)
        ·
          refine ⟨40724081252255458552817837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27149387501503639035211891 40724081252255458552817837)
          ·
            refine ⟨15271530469595796957306689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40724081252255458552817837 15271530469595796957306689)
            ·
              refine ⟨11453647852196847717980017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15271530469595796957306689 11453647852196847717980017)
              ·
                refine ⟨8590235889147635788485013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11453647852196847717980017 8590235889147635788485013)
                ·
                  refine ⟨402667307303795427585235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8590235889147635788485013 402667307303795427585235)
                  ·
                    rfl

theorem cell23_7057726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 2, 2, 6].length) (baseStart_7057726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7057726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7057726 prefixEnd_7057726 := by exact prefixLift 7057726
  have htrace : WordTrace (prefixWord ++ tailWord_7057726) baseStart_7057726 baseEnd_7057726 := by
    simpa [prefixWord, tailWord_7057726, baseEnd_7057726] using wordTrace_append hprefix tailTrace_7057726
  have hstable : (prefixWord ++ tailWord_7057726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7057726).length < 2 ^ (prefixWord ++ tailWord_7057726).sum := by decide
  have hdescent : baseEnd_7057726 < baseStart_7057726 := by decide
  rcases family_descends (prefixWord ++ tailWord_7057726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7057746 : List Nat := [3, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2]
def baseStart_7057746 : Nat := 118140960795 + 7057746 * 2 ^ 59
def prefixEnd_7057746 : Nat := 4983230072969 + 3 ^ 40 * 7057746 * 2
def baseEnd_7057746 : Nat := 3624016035347248770017023

theorem tailTrace_7057746 : CollatzResearch.WordTrace tailWord_7057746 prefixEnd_7057746 3624016035347248770017023 := by
  unfold tailWord_7057746
  simp only [CollatzResearch.WordTrace]
  refine ⟨64354286072249770974434273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171611429525999389265158061 64354286072249770974434273)
  ·
    refine ⟨48265714554187328230825705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64354286072249770974434273 48265714554187328230825705)
    ·
      refine ⟨36199285915640496173119279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48265714554187328230825705 36199285915640496173119279)
      ·
        refine ⟨54298928873460744259678919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36199285915640496173119279 54298928873460744259678919)
        ·
          refine ⟨81448393310191116389518379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54298928873460744259678919 81448393310191116389518379)
          ·
            refine ⟨122172589965286674584277569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81448393310191116389518379 122172589965286674584277569)
            ·
              refine ⟨91629442473965005938208177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122172589965286674584277569 91629442473965005938208177)
              ·
                refine ⟨68722081855473754453656133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91629442473965005938208177 68722081855473754453656133)
                ·
                  refine ⟨12885390347901328960060525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 68722081855473754453656133 12885390347901328960060525)
                  ·
                    refine ⟨4832021380462998360022697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12885390347901328960060525 4832021380462998360022697)
                    ·
                      refine ⟨3624016035347248770017023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4832021380462998360022697 3624016035347248770017023)
                      ·
                        rfl

theorem cell23_7057746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2].length) (baseStart_7057746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7057746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7057746 prefixEnd_7057746 := by exact prefixLift 7057746
  have htrace : WordTrace (prefixWord ++ tailWord_7057746) baseStart_7057746 baseEnd_7057746 := by
    simpa [prefixWord, tailWord_7057746, baseEnd_7057746] using wordTrace_append hprefix tailTrace_7057746
  have hstable : (prefixWord ++ tailWord_7057746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7057746).length < 2 ^ (prefixWord ++ tailWord_7057746).sum := by decide
  have hdescent : baseEnd_7057746 < baseStart_7057746 := by decide
  rcases family_descends (prefixWord ++ tailWord_7057746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7057759 : List Nat := [1, 1, 2, 3, 1, 2, 4, 1, 3, 1, 4]
def baseStart_7057759 : Nat := 118140960795 + 7057759 * 2 ^ 59
def prefixEnd_7057759 : Nat := 4983230072969 + 3 ^ 40 * 7057759 * 2
def baseEnd_7057759 : Nat := 3624022710595757219154463

theorem tailTrace_7057759 : CollatzResearch.WordTrace tailWord_7057759 prefixEnd_7057759 3624022710595757219154463 := by
  unfold tailWord_7057759
  simp only [CollatzResearch.WordTrace]
  refine ⟨257417618437951987117960331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171611745625301324745306887 257417618437951987117960331)
  ·
    refine ⟨386126427656927980676940497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257417618437951987117960331 386126427656927980676940497)
    ·
      refine ⟨289594820742695985507705373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 386126427656927980676940497 289594820742695985507705373)
      ·
        refine ⟨108598057778510994565389515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 289594820742695985507705373 108598057778510994565389515)
        ·
          refine ⟨162897086667766491848084273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108598057778510994565389515 162897086667766491848084273)
          ·
            refine ⟨122172815000824868886063205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162897086667766491848084273 122172815000824868886063205)
            ·
              refine ⟨22907402812654662916136851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 122172815000824868886063205 22907402812654662916136851)
              ·
                refine ⟨34361104218981994374205277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22907402812654662916136851 34361104218981994374205277)
                ·
                  refine ⟨12885414082118247890326979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34361104218981994374205277 12885414082118247890326979)
                  ·
                    refine ⟨19328121123177371835490469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12885414082118247890326979 19328121123177371835490469)
                    ·
                      refine ⟨3624022710595757219154463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19328121123177371835490469 3624022710595757219154463)
                      ·
                        rfl

theorem cell23_7057759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 1, 3, 1, 4].length) (baseStart_7057759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7057759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7057759 prefixEnd_7057759 := by exact prefixLift 7057759
  have htrace : WordTrace (prefixWord ++ tailWord_7057759) baseStart_7057759 baseEnd_7057759 := by
    simpa [prefixWord, tailWord_7057759, baseEnd_7057759] using wordTrace_append hprefix tailTrace_7057759
  have hstable : (prefixWord ++ tailWord_7057759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7057759).length < 2 ^ (prefixWord ++ tailWord_7057759).sum := by decide
  have hdescent : baseEnd_7057759 < baseStart_7057759 := by decide
  rcases family_descends (prefixWord ++ tailWord_7057759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7057769 : List Nat := [1, 2, 1, 1, 1, 3, 4, 2, 4, 4]
def baseStart_7057769 : Nat := 118140960795 + 7057769 * 2 ^ 59
def prefixEnd_7057769 : Nat := 4983230072969 + 3 ^ 40 * 7057769 * 2
def baseEnd_7057769 : Nat := 1208009281800767393343139

theorem tailTrace_7057769 : CollatzResearch.WordTrace tailWord_7057769 prefixEnd_7057769 1208009281800767393343139 := by
  unfold tailWord_7057769
  simp only [CollatzResearch.WordTrace]
  refine ⟨257417983167915758825824361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171611988778610505883882907 257417983167915758825824361)
  ·
    refine ⟨193063487375936819119368271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257417983167915758825824361 193063487375936819119368271)
    ·
      refine ⟨289595231063905228679052407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193063487375936819119368271 289595231063905228679052407)
      ·
        refine ⟨434392846595857843018578611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 289595231063905228679052407 434392846595857843018578611)
        ·
          refine ⟨651589269893786764527867917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 434392846595857843018578611 651589269893786764527867917)
          ·
            refine ⟨244345976210170036697950469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 651589269893786764527867917 244345976210170036697950469)
            ·
              refine ⟨45814870539406881880865713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 244345976210170036697950469 45814870539406881880865713)
              ·
                refine ⟨34361152904555161410649285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45814870539406881880865713 34361152904555161410649285)
                ·
                  refine ⟨6442716169604092764496741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34361152904555161410649285 6442716169604092764496741)
                  ·
                    refine ⟨1208009281800767393343139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6442716169604092764496741 1208009281800767393343139)
                    ·
                      rfl

theorem cell23_7057769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 2, 4, 4].length) (baseStart_7057769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7057769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7057769 prefixEnd_7057769 := by exact prefixLift 7057769
  have htrace : WordTrace (prefixWord ++ tailWord_7057769) baseStart_7057769 baseEnd_7057769 := by
    simpa [prefixWord, tailWord_7057769, baseEnd_7057769] using wordTrace_append hprefix tailTrace_7057769
  have hstable : (prefixWord ++ tailWord_7057769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7057769).length < 2 ^ (prefixWord ++ tailWord_7057769).sum := by decide
  have hdescent : baseEnd_7057769 < baseStart_7057769 := by decide
  rcases family_descends (prefixWord ++ tailWord_7057769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7057770 : List Nat := [3, 1, 3, 3, 1, 1, 1, 5, 1, 1, 3]
def baseStart_7057770 : Nat := 118140960795 + 7057770 * 2 ^ 59
def prefixEnd_7057770 : Nat := 4983230072969 + 3 ^ 40 * 7057770 * 2
def baseEnd_7057770 : Nat := 3624028358882956676116913

theorem tailTrace_7057770 : CollatzResearch.WordTrace tailWord_7057770 prefixEnd_7057770 3624028358882956676116913 := by
  unfold tailWord_7057770
  simp only [CollatzResearch.WordTrace]
  refine ⟨64354504910228033999152691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171612013093941423997740509 64354504910228033999152691)
  ·
    refine ⟨96531757365342050998729037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64354504910228033999152691 96531757365342050998729037)
    ·
      refine ⟨36199409012003269124523389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96531757365342050998729037 36199409012003269124523389)
      ·
        refine ⟨13574778379501225921696271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36199409012003269124523389 13574778379501225921696271)
        ·
          refine ⟨20362167569251838882544407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13574778379501225921696271 20362167569251838882544407)
          ·
            refine ⟨30543251353877758323816611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20362167569251838882544407 30543251353877758323816611)
            ·
              refine ⟨45814877030816637485724917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30543251353877758323816611 45814877030816637485724917)
              ·
                refine ⟨4295144721639059764286711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45814877030816637485724917 4295144721639059764286711)
                ·
                  refine ⟨6442717082458589646430067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4295144721639059764286711 6442717082458589646430067)
                  ·
                    refine ⟨9664075623687884469645101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6442717082458589646430067 9664075623687884469645101)
                    ·
                      refine ⟨3624028358882956676116913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9664075623687884469645101 3624028358882956676116913)
                      ·
                        rfl

theorem cell23_7057770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 5, 1, 1, 3].length) (baseStart_7057770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7057770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7057770 prefixEnd_7057770 := by exact prefixLift 7057770
  have htrace : WordTrace (prefixWord ++ tailWord_7057770) baseStart_7057770 baseEnd_7057770 := by
    simpa [prefixWord, tailWord_7057770, baseEnd_7057770] using wordTrace_append hprefix tailTrace_7057770
  have hstable : (prefixWord ++ tailWord_7057770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7057770).length < 2 ^ (prefixWord ++ tailWord_7057770).sum := by decide
  have hdescent : baseEnd_7057770 < baseStart_7057770 := by decide
  rcases family_descends (prefixWord ++ tailWord_7057770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7057776 : List Nat := [2, 1, 1, 1, 4, 4, 1, 3, 1, 1, 4]
def baseStart_7057776 : Nat := 118140960795 + 7057776 * 2 ^ 59
def prefixEnd_7057776 : Nat := 4983230072969 + 3 ^ 40 * 7057776 * 2
def baseEnd_7057776 : Nat := 3624031439766883652641885

theorem tailTrace_7057776 : CollatzResearch.WordTrace tailWord_7057776 prefixEnd_7057776 3624031439766883652641885 := by
  unfold tailWord_7057776
  simp only [CollatzResearch.WordTrace]
  refine ⟨128709119239445199510664591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171612158985926932680886121 128709119239445199510664591)
  ·
    refine ⟨193063678859167799265996887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128709119239445199510664591 193063678859167799265996887)
    ·
      refine ⟨289595518288751698898995331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193063678859167799265996887 289595518288751698898995331)
      ·
        refine ⟨434393277433127548348492997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 289595518288751698898995331 434393277433127548348492997)
        ·
          refine ⟨81448739518711415315342437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 434393277433127548348492997 81448739518711415315342437)
          ·
            refine ⟨15271638659758390371626707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 81448739518711415315342437 15271638659758390371626707)
            ·
              refine ⟨22907457989637585557440061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15271638659758390371626707 22907457989637585557440061)
              ·
                refine ⟨8590296746114094584040023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22907457989637585557440061 8590296746114094584040023)
                ·
                  refine ⟨12885445119171141876060035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8590296746114094584040023 12885445119171141876060035)
                  ·
                    refine ⟨19328167678756712814090053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12885445119171141876060035 19328167678756712814090053)
                    ·
                      refine ⟨3624031439766883652641885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19328167678756712814090053 3624031439766883652641885)
                      ·
                        rfl

theorem cell23_7057776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 3, 1, 1, 4].length) (baseStart_7057776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7057776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7057776 prefixEnd_7057776 := by exact prefixLift 7057776
  have htrace : WordTrace (prefixWord ++ tailWord_7057776) baseStart_7057776 baseEnd_7057776 := by
    simpa [prefixWord, tailWord_7057776, baseEnd_7057776] using wordTrace_append hprefix tailTrace_7057776
  have hstable : (prefixWord ++ tailWord_7057776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7057776).length < 2 ^ (prefixWord ++ tailWord_7057776).sum := by decide
  have hdescent : baseEnd_7057776 < baseStart_7057776 := by decide
  rcases family_descends (prefixWord ++ tailWord_7057776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7057792 : List Nat := [2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 7]
def baseStart_7057792 : Nat := 118140960795 + 7057792 * 2 ^ 59
def prefixEnd_7057792 : Nat := 4983230072969 + 3 ^ 40 * 7057792 * 2
def baseEnd_7057792 : Nat := 3624039655457355590041811

theorem tailTrace_7057792 : CollatzResearch.WordTrace tailWord_7057792 prefixEnd_7057792 3624039655457355590041811 := by
  unfold tailWord_7057792
  simp only [CollatzResearch.WordTrace]
  refine ⟨128709411023416216876955815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171612548031221622502607753 128709411023416216876955815)
  ·
    refine ⟨193064116535124325315433723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128709411023416216876955815 193064116535124325315433723)
    ·
      refine ⟨289596174802686487973150585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193064116535124325315433723 289596174802686487973150585)
      ·
        refine ⟨217197131102014865979862939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 289596174802686487973150585 217197131102014865979862939)
        ·
          refine ⟨325795696653022298969794409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217197131102014865979862939 325795696653022298969794409)
          ·
            refine ⟨244346772489766724227345807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 325795696653022298969794409 244346772489766724227345807)
            ·
              refine ⟨366520158734650086341018711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 244346772489766724227345807 366520158734650086341018711)
              ·
                refine ⟨549780238101975129511528067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 366520158734650086341018711 549780238101975129511528067)
                ·
                  refine ⟨824670357152962694267292101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 549780238101975129511528067 824670357152962694267292101)
                  ·
                    refine ⟨154625691966180505175117269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 824670357152962694267292101 154625691966180505175117269)
                    ·
                      refine ⟨3624039655457355590041811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 154625691966180505175117269 3624039655457355590041811)
                      ·
                        rfl

theorem cell23_7057792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 7].length) (baseStart_7057792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7057792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7057792 prefixEnd_7057792 := by exact prefixLift 7057792
  have htrace : WordTrace (prefixWord ++ tailWord_7057792) baseStart_7057792 baseEnd_7057792 := by
    simpa [prefixWord, tailWord_7057792, baseEnd_7057792] using wordTrace_append hprefix tailTrace_7057792
  have hstable : (prefixWord ++ tailWord_7057792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7057792).length < 2 ^ (prefixWord ++ tailWord_7057792).sum := by decide
  have hdescent : baseEnd_7057792 < baseStart_7057792 := by decide
  rcases family_descends (prefixWord ++ tailWord_7057792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7057803 : List Nat := [1, 1, 1, 1, 4, 5, 3, 1, 2, 4]
def baseStart_7057803 : Nat := 118140960795 + 7057803 * 2 ^ 59
def prefixEnd_7057803 : Nat := 4983230072969 + 3 ^ 40 * 7057803 * 2
def baseEnd_7057803 : Nat := 1208015101248185015668087

theorem tailTrace_7057803 : CollatzResearch.WordTrace tailWord_7057803 prefixEnd_7057803 1208015101248185015668087 := by
  unfold tailWord_7057803
  simp only [CollatzResearch.WordTrace]
  refine ⟨257419223249792582632562063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171612815499861721755041375 257419223249792582632562063)
  ·
    refine ⟨386128834874688873948843095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257419223249792582632562063 386128834874688873948843095)
    ·
      refine ⟨579193252312033310923264643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 386128834874688873948843095 579193252312033310923264643)
      ·
        refine ⟨868789878468049966384896965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 579193252312033310923264643 868789878468049966384896965)
        ·
          refine ⟨162898102212759368697168181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 868789878468049966384896965 162898102212759368697168181)
          ·
            refine ⟨15271697082446190815359517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 162898102212759368697168181 15271697082446190815359517)
            ·
              refine ⟨5726886405917321555759819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15271697082446190815359517 5726886405917321555759819)
              ·
                refine ⟨8590329608875982333639729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5726886405917321555759819 8590329608875982333639729)
                ·
                  refine ⟨6442747206656986750229797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8590329608875982333639729 6442747206656986750229797)
                  ·
                    refine ⟨1208015101248185015668087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6442747206656986750229797 1208015101248185015668087)
                    ·
                      rfl

theorem cell23_7057803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 3, 1, 2, 4].length) (baseStart_7057803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7057803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7057803 prefixEnd_7057803 := by exact prefixLift 7057803
  have htrace : WordTrace (prefixWord ++ tailWord_7057803) baseStart_7057803 baseEnd_7057803 := by
    simpa [prefixWord, tailWord_7057803, baseEnd_7057803] using wordTrace_append hprefix tailTrace_7057803
  have hstable : (prefixWord ++ tailWord_7057803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7057803).length < 2 ^ (prefixWord ++ tailWord_7057803).sum := by decide
  have hdescent : baseEnd_7057803 < baseStart_7057803 := by decide
  rcases family_descends (prefixWord ++ tailWord_7057803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7057806 : List Nat := [4, 1, 1, 4, 1, 2, 1, 1, 1, 1, 6]
def baseStart_7057806 : Nat := 118140960795 + 7057806 * 2 ^ 59
def prefixEnd_7057806 : Nat := 4983230072969 + 3 ^ 40 * 7057806 * 2
def baseEnd_7057806 : Nat := 3624046844186518535266747

theorem tailTrace_7057806 : CollatzResearch.WordTrace tailWord_7057806 prefixEnd_7057806 3624046844186518535266747 := by
  unfold tailWord_7057806
  simp only [CollatzResearch.WordTrace]
  refine ⟨32177416583597714268115159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 171612888445854476096614181 32177416583597714268115159)
  ·
    refine ⟨48266124875396571402172739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32177416583597714268115159 48266124875396571402172739)
    ·
      refine ⟨72399187313094857103259109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48266124875396571402172739 72399187313094857103259109)
      ·
        refine ⟨13574847621205285706861083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72399187313094857103259109 13574847621205285706861083)
        ·
          refine ⟨20362271431807928560291625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13574847621205285706861083 20362271431807928560291625)
          ·
            refine ⟨15271703573855946420218719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20362271431807928560291625 15271703573855946420218719)
            ·
              refine ⟨22907555360783919630328079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15271703573855946420218719 22907555360783919630328079)
              ·
                refine ⟨34361333041175879445492119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22907555360783919630328079 34361333041175879445492119)
                ·
                  refine ⟨51541999561763819168238179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34361333041175879445492119 51541999561763819168238179)
                  ·
                    refine ⟨77312999342645728752357269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51541999561763819168238179 77312999342645728752357269)
                    ·
                      refine ⟨3624046844186518535266747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 77312999342645728752357269 3624046844186518535266747)
                      ·
                        rfl

theorem cell23_7057806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_7057806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7057806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7057806 prefixEnd_7057806 := by exact prefixLift 7057806
  have htrace : WordTrace (prefixWord ++ tailWord_7057806) baseStart_7057806 baseEnd_7057806 := by
    simpa [prefixWord, tailWord_7057806, baseEnd_7057806] using wordTrace_append hprefix tailTrace_7057806
  have hstable : (prefixWord ++ tailWord_7057806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7057806).length < 2 ^ (prefixWord ++ tailWord_7057806).sum := by decide
  have hdescent : baseEnd_7057806 < baseStart_7057806 := by decide
  rcases family_descends (prefixWord ++ tailWord_7057806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7057816 : List Nat := [2, 1, 2, 5, 1, 1, 4, 7]
def baseStart_7057816 : Nat := 118140960795 + 7057816 * 2 ^ 59
def prefixEnd_7057816 : Nat := 4983230072969 + 3 ^ 40 * 7057816 * 2
def baseEnd_7057816 : Nat := 134224147370113462820063

theorem tailTrace_7057816 : CollatzResearch.WordTrace tailWord_7057816 prefixEnd_7057816 134224147370113462820063 := by
  unfold tailWord_7057816
  simp only [CollatzResearch.WordTrace]
  refine ⟨128709848699372742926392651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171613131599163657235190201 128709848699372742926392651)
  ·
    refine ⟨193064773049059114389588977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128709848699372742926392651 193064773049059114389588977)
    ·
      refine ⟨144798579786794335792191733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193064773049059114389588977 144798579786794335792191733)
      ·
        refine ⟨13574866855011968980517975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 144798579786794335792191733 13574866855011968980517975)
        ·
          refine ⟨20362300282517953470776963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13574866855011968980517975 20362300282517953470776963)
          ·
            refine ⟨30543450423776930206165445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20362300282517953470776963 30543450423776930206165445)
            ·
              refine ⟨5726896954458174413656021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30543450423776930206165445 5726896954458174413656021)
              ·
                refine ⟨134224147370113462820063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5726896954458174413656021 134224147370113462820063)
                ·
                  rfl

theorem cell23_7057816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 4, 7].length) (baseStart_7057816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7057816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7057816 prefixEnd_7057816 := by exact prefixLift 7057816
  have htrace : WordTrace (prefixWord ++ tailWord_7057816) baseStart_7057816 baseEnd_7057816 := by
    simpa [prefixWord, tailWord_7057816, baseEnd_7057816] using wordTrace_append hprefix tailTrace_7057816
  have hstable : (prefixWord ++ tailWord_7057816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7057816).length < 2 ^ (prefixWord ++ tailWord_7057816).sum := by decide
  have hdescent : baseEnd_7057816 < baseStart_7057816 := by decide
  rcases family_descends (prefixWord ++ tailWord_7057816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7057826 : List Nat := [3, 3, 1, 2, 1, 1, 2, 1, 3, 3, 3]
def baseStart_7057826 : Nat := 118140960795 + 7057826 * 2 ^ 59
def prefixEnd_7057826 : Nat := 4983230072969 + 3 ^ 40 * 7057826 * 2
def baseEnd_7057826 : Nat := 3624057113799608457016655

theorem tailTrace_7057826 : CollatzResearch.WordTrace tailWord_7057826 prefixEnd_7057826 3624057113799608457016655 := by
  unfold tailWord_7057826
  simp only [CollatzResearch.WordTrace]
  refine ⟨64355015532177314390162333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171613374752472838373766221 64355015532177314390162333)
  ·
    refine ⟨24133130824566492896310875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64355015532177314390162333 24133130824566492896310875)
    ·
      refine ⟨36199696236849739344466313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24133130824566492896310875 36199696236849739344466313)
      ·
        refine ⟨27149772177637304508349735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36199696236849739344466313 27149772177637304508349735)
        ·
          refine ⟨40724658266455956762524603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27149772177637304508349735 40724658266455956762524603)
          ·
            refine ⟨61086987399683935143786905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40724658266455956762524603 61086987399683935143786905)
            ·
              refine ⟨45815240549762951357840179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61086987399683935143786905 45815240549762951357840179)
              ·
                refine ⟨68722860824644427036760269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45815240549762951357840179 68722860824644427036760269)
                ·
                  refine ⟨25771072809241660138785101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68722860824644427036760269 25771072809241660138785101)
                  ·
                    refine ⟨9664152303465622552044413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25771072809241660138785101 9664152303465622552044413)
                    ·
                      refine ⟨3624057113799608457016655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9664152303465622552044413 3624057113799608457016655)
                      ·
                        rfl

theorem cell23_7057826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 1, 3, 3, 3].length) (baseStart_7057826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7057826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7057826 prefixEnd_7057826 := by exact prefixLift 7057826
  have htrace : WordTrace (prefixWord ++ tailWord_7057826) baseStart_7057826 baseEnd_7057826 := by
    simpa [prefixWord, tailWord_7057826, baseEnd_7057826] using wordTrace_append hprefix tailTrace_7057826
  have hstable : (prefixWord ++ tailWord_7057826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7057826).length < 2 ^ (prefixWord ++ tailWord_7057826).sum := by decide
  have hdescent : baseEnd_7057826 < baseStart_7057826 := by decide
  rcases family_descends (prefixWord ++ tailWord_7057826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7057827 : List Nat := [1, 1, 1, 4, 1, 6, 1, 3, 1, 2, 2]
def baseStart_7057827 : Nat := 118140960795 + 7057827 * 2 ^ 59
def prefixEnd_7057827 : Nat := 4983230072969 + 3 ^ 40 * 7057827 * 2
def baseEnd_7057827 : Nat := 3624057627280262953104151

theorem tailTrace_7057827 : CollatzResearch.WordTrace tailWord_7057827 prefixEnd_7057827 3624057627280262953104151 := by
  unfold tailWord_7057827
  simp only [CollatzResearch.WordTrace]
  refine ⟨257420098601705634731435735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171613399067803756487623823 257420098601705634731435735)
  ·
    refine ⟨386130147902558452097153603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257420098601705634731435735 386130147902558452097153603)
    ·
      refine ⟨579195221853837678145730405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 386130147902558452097153603 579195221853837678145730405)
      ·
        refine ⟨108599104097594564652324451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 579195221853837678145730405 108599104097594564652324451)
        ·
          refine ⟨162898656146391846978486677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108599104097594564652324451 162898656146391846978486677)
          ·
            refine ⟨7635874506862117827116563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 162898656146391846978486677 7635874506862117827116563)
            ·
              refine ⟨11453811760293176740674845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7635874506862117827116563 11453811760293176740674845)
              ·
                refine ⟨4295179410109941277753067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11453811760293176740674845 4295179410109941277753067)
                ·
                  refine ⟨6442769115164911916629601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4295179410109941277753067 6442769115164911916629601)
                  ·
                    refine ⟨4832076836373683937472201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6442769115164911916629601 4832076836373683937472201)
                    ·
                      refine ⟨3624057627280262953104151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4832076836373683937472201 3624057627280262953104151)
                      ·
                        rfl

theorem cell23_7057827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 1, 3, 1, 2, 2].length) (baseStart_7057827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7057827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7057827 prefixEnd_7057827 := by exact prefixLift 7057827
  have htrace : WordTrace (prefixWord ++ tailWord_7057827) baseStart_7057827 baseEnd_7057827 := by
    simpa [prefixWord, tailWord_7057827, baseEnd_7057827] using wordTrace_append hprefix tailTrace_7057827
  have hstable : (prefixWord ++ tailWord_7057827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7057827).length < 2 ^ (prefixWord ++ tailWord_7057827).sum := by decide
  have hdescent : baseEnd_7057827 < baseStart_7057827 := by decide
  rcases family_descends (prefixWord ++ tailWord_7057827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7057836 : List Nat := [2, 2, 1, 1, 1, 1, 3, 2, 5, 3, 2]
def baseStart_7057836 : Nat := 118140960795 + 7057836 * 2 ^ 59
def prefixEnd_7057836 : Nat := 4983230072969 + 3 ^ 40 * 7057836 * 2
def baseEnd_7057836 : Nat := 3624062248606153417891609

theorem tailTrace_7057836 : CollatzResearch.WordTrace tailWord_7057836 prefixEnd_7057836 3624062248606153417891609 := by
  unfold tailWord_7057836
  simp only [CollatzResearch.WordTrace]
  refine ⟨128710213429336514634256681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171613617905782019512342241 128710213429336514634256681)
  ·
    refine ⟨96532660072002385975692511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128710213429336514634256681 96532660072002385975692511)
    ·
      refine ⟨144798990108003578963538767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96532660072002385975692511 144798990108003578963538767)
      ·
        refine ⟨217198485162005368445308151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144798990108003578963538767 217198485162005368445308151)
        ·
          refine ⟨325797727743008052667962227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217198485162005368445308151 325797727743008052667962227)
          ·
            refine ⟨488696591614512079001943341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 325797727743008052667962227 488696591614512079001943341)
            ·
              refine ⟨183261221855442029625728753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 488696591614512079001943341 183261221855442029625728753)
              ·
                refine ⟨137445916391581522219296565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 183261221855442029625728753 137445916391581522219296565)
                ·
                  refine ⟨12885554661710767708059053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 137445916391581522219296565 12885554661710767708059053)
                  ·
                    refine ⟨4832082998141537890522145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12885554661710767708059053 4832082998141537890522145)
                    ·
                      refine ⟨3624062248606153417891609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4832082998141537890522145 3624062248606153417891609)
                      ·
                        rfl

theorem cell23_7057836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 3, 2].length) (baseStart_7057836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7057836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7057836 prefixEnd_7057836 := by exact prefixLift 7057836
  have htrace : WordTrace (prefixWord ++ tailWord_7057836) baseStart_7057836 baseEnd_7057836 := by
    simpa [prefixWord, tailWord_7057836, baseEnd_7057836] using wordTrace_append hprefix tailTrace_7057836
  have hstable : (prefixWord ++ tailWord_7057836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7057836).length < 2 ^ (prefixWord ++ tailWord_7057836).sum := by decide
  have hdescent : baseEnd_7057836 < baseStart_7057836 := by decide
  rcases family_descends (prefixWord ++ tailWord_7057836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7057879 : List Nat := [1, 1, 3, 2, 1, 1, 1, 1, 6, 2, 4]
def baseStart_7057879 : Nat := 118140960795 + 7057879 * 2 ^ 59
def prefixEnd_7057879 : Nat := 4983230072969 + 3 ^ 40 * 7057879 * 2
def baseEnd_7057879 : Nat := 3624084328274296749653911

theorem tailTrace_7057879 : CollatzResearch.WordTrace tailWord_7057879 prefixEnd_7057879 3624084328274296749653911 := by
  unfold tailWord_7057879
  simp only [CollatzResearch.WordTrace]
  refine ⟨257421995197517247612328691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171614663465011498408219127 257421995197517247612328691)
  ·
    refine ⟨386132992796275871418493037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257421995197517247612328691 386132992796275871418493037)
    ·
      refine ⟨144799872298603451781934889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 386132992796275871418493037 144799872298603451781934889)
      ·
        refine ⟨108599904223952588836451167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144799872298603451781934889 108599904223952588836451167)
        ·
          refine ⟨162899856335928883254676751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108599904223952588836451167 162899856335928883254676751)
          ·
            refine ⟨244349784503893324882015127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162899856335928883254676751 244349784503893324882015127)
            ·
              refine ⟨366524676755839987323022691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 244349784503893324882015127 366524676755839987323022691)
              ·
                refine ⟨549787015133759980984534037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 366524676755839987323022691 549787015133759980984534037)
                ·
                  refine ⟨25771266334394999108650033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 549787015133759980984534037 25771266334394999108650033)
                  ·
                    refine ⟨19328449750796249331487525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25771266334394999108650033 19328449750796249331487525)
                    ·
                      refine ⟨3624084328274296749653911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19328449750796249331487525 3624084328274296749653911)
                      ·
                        rfl

theorem cell23_7057879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 6, 2, 4].length) (baseStart_7057879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7057879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7057879 prefixEnd_7057879 := by exact prefixLift 7057879
  have htrace : WordTrace (prefixWord ++ tailWord_7057879) baseStart_7057879 baseEnd_7057879 := by
    simpa [prefixWord, tailWord_7057879, baseEnd_7057879] using wordTrace_append hprefix tailTrace_7057879
  have hstable : (prefixWord ++ tailWord_7057879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7057879).length < 2 ^ (prefixWord ++ tailWord_7057879).sum := by decide
  have hdescent : baseEnd_7057879 < baseStart_7057879 := by decide
  rcases family_descends (prefixWord ++ tailWord_7057879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7057900 : List Nat := [2, 2, 1, 1, 2, 1, 6, 2, 2, 2, 2]
def baseStart_7057900 : Nat := 118140960795 + 7057900 * 2 ^ 59
def prefixEnd_7057900 : Nat := 4983230072969 + 3 ^ 40 * 7057900 * 2
def baseEnd_7057900 : Nat := 3624095111368041167491315

theorem tailTrace_7057900 : CollatzResearch.WordTrace tailWord_7057900 prefixEnd_7057900 3624095111368041167491315 := by
  unfold tailWord_7057900
  simp only [CollatzResearch.WordTrace]
  refine ⟨128711380565220584099421577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171615174086960778799228769 128711380565220584099421577)
  ·
    refine ⟨96533535423915438074566183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128711380565220584099421577 96533535423915438074566183)
    ·
      refine ⟨144800303135873157111849275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96533535423915438074566183 144800303135873157111849275)
      ·
        refine ⟨217200454703809735667773913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144800303135873157111849275 217200454703809735667773913)
        ·
          refine ⟨162900341027857301750830435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 217200454703809735667773913 162900341027857301750830435)
          ·
            refine ⟨244350511541785952626245653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162900341027857301750830435 244350511541785952626245653)
            ·
              refine ⟨11453930228521216529355265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 244350511541785952626245653 11453930228521216529355265)
              ·
                refine ⟨8590447671390912397016449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11453930228521216529355265 8590447671390912397016449)
                ·
                  refine ⟨6442835753543184297762337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8590447671390912397016449 6442835753543184297762337)
                  ·
                    refine ⟨4832126815157388223321753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6442835753543184297762337 4832126815157388223321753)
                    ·
                      refine ⟨3624095111368041167491315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4832126815157388223321753 3624095111368041167491315)
                      ·
                        rfl

theorem cell23_7057900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 2, 2].length) (baseStart_7057900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7057900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7057900 prefixEnd_7057900 := by exact prefixLift 7057900
  have htrace : WordTrace (prefixWord ++ tailWord_7057900) baseStart_7057900 baseEnd_7057900 := by
    simpa [prefixWord, tailWord_7057900, baseEnd_7057900] using wordTrace_append hprefix tailTrace_7057900
  have hstable : (prefixWord ++ tailWord_7057900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7057900).length < 2 ^ (prefixWord ++ tailWord_7057900).sum := by decide
  have hdescent : baseEnd_7057900 < baseStart_7057900 := by decide
  rcases family_descends (prefixWord ++ tailWord_7057900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7057919 : List Nat := [1, 1, 2, 2, 1, 2, 4, 2, 1, 7]
def baseStart_7057919 : Nat := 118140960795 + 7057919 * 2 ^ 59
def prefixEnd_7057919 : Nat := 4983230072969 + 3 ^ 40 * 7057919 * 2
def baseEnd_7057919 : Nat := 1208034955833492197717909

theorem tailTrace_7057919 : CollatzResearch.WordTrace tailWord_7057919 prefixEnd_7057919 1208034955833492197717909 := by
  unfold tailWord_7057919
  simp only [CollatzResearch.WordTrace]
  refine ⟨257423454117372334443784811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171615636078248222962523207 257423454117372334443784811)
  ·
    refine ⟨386135181176058501665677217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257423454117372334443784811 386135181176058501665677217)
    ·
      refine ⟨289601385882043876249257913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 386135181176058501665677217 289601385882043876249257913)
      ·
        refine ⟨217201039411532907186943435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 289601385882043876249257913 217201039411532907186943435)
        ·
          refine ⟨325801559117299360780415153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217201039411532907186943435 325801559117299360780415153)
          ·
            refine ⟨244351169337974520585311365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 325801559117299360780415153 244351169337974520585311365)
            ·
              refine ⟨45815844250870222609745881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 244351169337974520585311365 45815844250870222609745881)
              ·
                refine ⟨34361883188152666957309411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45815844250870222609745881 34361883188152666957309411)
                ·
                  refine ⟨51542824782229000435964117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34361883188152666957309411 51542824782229000435964117)
                  ·
                    refine ⟨1208034955833492197717909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51542824782229000435964117 1208034955833492197717909)
                    ·
                      rfl

theorem cell23_7057919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 2, 1, 7].length) (baseStart_7057919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7057919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7057919 prefixEnd_7057919 := by exact prefixLift 7057919
  have htrace : WordTrace (prefixWord ++ tailWord_7057919) baseStart_7057919 baseEnd_7057919 := by
    simpa [prefixWord, tailWord_7057919, baseEnd_7057919] using wordTrace_append hprefix tailTrace_7057919
  have hstable : (prefixWord ++ tailWord_7057919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7057919).length < 2 ^ (prefixWord ++ tailWord_7057919).sum := by decide
  have hdescent : baseEnd_7057919 < baseStart_7057919 := by decide
  rcases family_descends (prefixWord ++ tailWord_7057919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7057929 : List Nat := [1, 2, 1, 1, 3, 1, 2, 2, 3, 2, 5]
def baseStart_7057929 : Nat := 118140960795 + 7057929 * 2 ^ 59
def prefixEnd_7057929 : Nat := 4983230072969 + 3 ^ 40 * 7057929 * 2
def baseEnd_7057929 : Nat := 3624110002307021554028681

theorem tailTrace_7057929 : CollatzResearch.WordTrace tailWord_7057929 prefixEnd_7057929 3624110002307021554028681 := by
  unfold tailWord_7057929
  simp only [CollatzResearch.WordTrace]
  refine ⟨257423818847336106151648841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171615879231557404101099227 257423818847336106151648841)
  ·
    refine ⟨193067864135502079613736631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257423818847336106151648841 193067864135502079613736631)
    ·
      refine ⟨289601796203253119420604947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193067864135502079613736631 289601796203253119420604947)
      ·
        refine ⟨434402694304879679130907421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 289601796203253119420604947 434402694304879679130907421)
        ·
          refine ⟨162901010364329879674090283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 434402694304879679130907421 162901010364329879674090283)
          ·
            refine ⟨244351515546494819511135425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162901010364329879674090283 244351515546494819511135425)
            ·
              refine ⟨183263636659871114633351569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 244351515546494819511135425 183263636659871114633351569)
              ·
                refine ⟨137447727494903335975013677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 183263636659871114633351569 137447727494903335975013677)
                ·
                  refine ⟨51542897810588750990630129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 137447727494903335975013677 51542897810588750990630129)
                  ·
                    refine ⟨38657173357941563242972597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51542897810588750990630129 38657173357941563242972597)
                    ·
                      refine ⟨3624110002307021554028681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38657173357941563242972597 3624110002307021554028681)
                      ·
                        rfl

theorem cell23_7057929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 2, 3, 2, 5].length) (baseStart_7057929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7057929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7057929 prefixEnd_7057929 := by exact prefixLift 7057929
  have htrace : WordTrace (prefixWord ++ tailWord_7057929) baseStart_7057929 baseEnd_7057929 := by
    simpa [prefixWord, tailWord_7057929, baseEnd_7057929] using wordTrace_append hprefix tailTrace_7057929
  have hstable : (prefixWord ++ tailWord_7057929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7057929).length < 2 ^ (prefixWord ++ tailWord_7057929).sum := by decide
  have hdescent : baseEnd_7057929 < baseStart_7057929 := by decide
  rcases family_descends (prefixWord ++ tailWord_7057929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7057940 : List Nat := [2, 4, 3, 1, 1, 1, 1, 5, 5]
def baseStart_7057940 : Nat := 118140960795 + 7057940 * 2 ^ 59
def prefixEnd_7057940 : Nat := 4983230072969 + 3 ^ 40 * 7057940 * 2
def baseEnd_7057940 : Nat := 402679516732691223443459

theorem tailTrace_7057940 : CollatzResearch.WordTrace tailWord_7057940 prefixEnd_7057940 402679516732691223443459 := by
  unfold tailWord_7057940
  simp only [CollatzResearch.WordTrace]
  refine ⟨128712110025148127515149637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171616146700197503353532849 128712110025148127515149637)
  ·
    refine ⟨24133520629715273909090557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 128712110025148127515149637 24133520629715273909090557)
    ·
      refine ⟨9050070236143227715908959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24133520629715273909090557 9050070236143227715908959)
      ·
        refine ⟨13575105354214841573863439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9050070236143227715908959 13575105354214841573863439)
        ·
          refine ⟨20362658031322262360795159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13575105354214841573863439 20362658031322262360795159)
          ·
            refine ⟨30543987046983393541192739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20362658031322262360795159 30543987046983393541192739)
            ·
              refine ⟨45815980570475090311789109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30543987046983393541192739 45815980570475090311789109)
              ·
                refine ⟨4295248178482039716730229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45815980570475090311789109 4295248178482039716730229)
                ·
                  refine ⟨402679516732691223443459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4295248178482039716730229 402679516732691223443459)
                  ·
                    rfl

theorem cell23_7057940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 5, 5].length) (baseStart_7057940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7057940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7057940 prefixEnd_7057940 := by exact prefixLift 7057940
  have htrace : WordTrace (prefixWord ++ tailWord_7057940) baseStart_7057940 baseEnd_7057940 := by
    simpa [prefixWord, tailWord_7057940, baseEnd_7057940] using wordTrace_append hprefix tailTrace_7057940
  have hstable : (prefixWord ++ tailWord_7057940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7057940).length < 2 ^ (prefixWord ++ tailWord_7057940).sum := by decide
  have hdescent : baseEnd_7057940 < baseStart_7057940 := by decide
  rcases family_descends (prefixWord ++ tailWord_7057940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7057973 : List Nat := [1, 3, 3, 1, 1, 2, 1, 3, 2, 4, 2]
def baseStart_7057973 : Nat := 118140960795 + 7057973 * 2 ^ 59
def prefixEnd_7057973 : Nat := 4983230072969 + 3 ^ 40 * 7057973 * 2
def baseEnd_7057973 : Nat := 3624132595455819381878479

theorem tailTrace_7057973 : CollatzResearch.WordTrace tailWord_7057973 prefixEnd_7057973 3624132595455819381878479 := by
  unfold tailWord_7057973
  simp only [CollatzResearch.WordTrace]
  refine ⟨257425423659176701666250573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171616949106117801110833715 257425423659176701666250573)
  ·
    refine ⟨96534533872191263124843965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 257425423659176701666250573 96534533872191263124843965)
    ·
      refine ⟨36200450202071723671816487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96534533872191263124843965 36200450202071723671816487)
      ·
        refine ⟨54300675303107585507724731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36200450202071723671816487 54300675303107585507724731)
        ·
          refine ⟨81451012954661378261587097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54300675303107585507724731 81451012954661378261587097)
          ·
            refine ⟨61088259715996033696190323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81451012954661378261587097 61088259715996033696190323)
            ·
              refine ⟨91632389573994050544285485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61088259715996033696190323 91632389573994050544285485)
              ·
                refine ⟨34362146090247768954107057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91632389573994050544285485 34362146090247768954107057)
                ·
                  refine ⟨25771609567685826715580293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34362146090247768954107057 25771609567685826715580293)
                  ·
                    refine ⟨4832176793941092509171305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25771609567685826715580293 4832176793941092509171305)
                    ·
                      refine ⟨3624132595455819381878479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4832176793941092509171305 3624132595455819381878479)
                      ·
                        rfl

theorem cell23_7057973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 3, 2, 4, 2].length) (baseStart_7057973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7057973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7057973 prefixEnd_7057973 := by exact prefixLift 7057973
  have htrace : WordTrace (prefixWord ++ tailWord_7057973) baseStart_7057973 baseEnd_7057973 := by
    simpa [prefixWord, tailWord_7057973, baseEnd_7057973] using wordTrace_append hprefix tailTrace_7057973
  have hstable : (prefixWord ++ tailWord_7057973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7057973).length < 2 ^ (prefixWord ++ tailWord_7057973).sum := by decide
  have hdescent : baseEnd_7057973 < baseStart_7057973 := by decide
  rcases family_descends (prefixWord ++ tailWord_7057973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7057976 : List Nat := [2, 1, 2, 1, 4, 1, 1, 1, 3, 4, 3]
def baseStart_7057976 : Nat := 118140960795 + 7057976 * 2 ^ 59
def prefixEnd_7057976 : Nat := 4983230072969 + 3 ^ 40 * 7057976 * 2
def baseEnd_7057976 : Nat := 3624134135897782870140965

theorem tailTrace_7057976 : CollatzResearch.WordTrace tailWord_7057976 prefixEnd_7057976 3624134135897782870140965 := by
  unfold tailWord_7057976
  simp only [CollatzResearch.WordTrace]
  refine ⟨128712766539082916589304891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171617022052110555452406521 128712766539082916589304891)
  ·
    refine ⟨193069149808624374883957337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128712766539082916589304891 193069149808624374883957337)
    ·
      refine ⟨144801862356468281162968003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193069149808624374883957337 144801862356468281162968003)
      ·
        refine ⟨217202793534702421744452005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144801862356468281162968003 217202793534702421744452005)
        ·
          refine ⟨40725523787756704077084751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 217202793534702421744452005 40725523787756704077084751)
          ·
            refine ⟨61088285681635056115627127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40725523787756704077084751 61088285681635056115627127)
            ·
              refine ⟨91632428522452584173440691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61088285681635056115627127 91632428522452584173440691)
              ·
                refine ⟨137448642783678876260161037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91632428522452584173440691 137448642783678876260161037)
                ·
                  refine ⟨51543241043879578597560389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 137448642783678876260161037 51543241043879578597560389)
                  ·
                    refine ⟨9664357695727420987042573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51543241043879578597560389 9664357695727420987042573)
                    ·
                      refine ⟨3624134135897782870140965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9664357695727420987042573 3624134135897782870140965)
                      ·
                        rfl

theorem cell23_7057976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 1, 3, 4, 3].length) (baseStart_7057976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7057976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7057976 prefixEnd_7057976 := by exact prefixLift 7057976
  have htrace : WordTrace (prefixWord ++ tailWord_7057976) baseStart_7057976 baseEnd_7057976 := by
    simpa [prefixWord, tailWord_7057976, baseEnd_7057976] using wordTrace_append hprefix tailTrace_7057976
  have hstable : (prefixWord ++ tailWord_7057976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7057976).length < 2 ^ (prefixWord ++ tailWord_7057976).sum := by decide
  have hdescent : baseEnd_7057976 < baseStart_7057976 := by decide
  rcases family_descends (prefixWord ++ tailWord_7057976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7057990 : List Nat := [6, 1, 1, 1, 2, 1, 2, 1, 1, 3, 4]
def baseStart_7057990 : Nat := 118140960795 + 7057990 * 2 ^ 59
def prefixEnd_7057990 : Nat := 4983230072969 + 3 ^ 40 * 7057990 * 2
def baseEnd_7057990 : Nat := 3624141324626945815365901

theorem tailTrace_7057990 : CollatzResearch.WordTrace tailWord_7057990 prefixEnd_7057990 3624141324626945815365901 := by
  unfold tailWord_7057990
  simp only [CollatzResearch.WordTrace]
  refine ⟨8044563865628597299050607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 171617362466743409046412949 8044563865628597299050607)
  ·
    refine ⟨12066845798442895948575911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8044563865628597299050607 12066845798442895948575911)
    ·
      refine ⟨18100268697664343922863867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12066845798442895948575911 18100268697664343922863867)
      ·
        refine ⟨27150403046496515884295801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18100268697664343922863867 27150403046496515884295801)
        ·
          refine ⟨20362802284872386913221851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27150403046496515884295801 20362802284872386913221851)
          ·
            refine ⟨30544203427308580369832777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20362802284872386913221851 30544203427308580369832777)
            ·
              refine ⟨22908152570481435277374583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30544203427308580369832777 22908152570481435277374583)
              ·
                refine ⟨34362228855722152916061875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22908152570481435277374583 34362228855722152916061875)
                ·
                  refine ⟨51543343283583229374092813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34362228855722152916061875 51543343283583229374092813)
                  ·
                    refine ⟨19328753731343711015284805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51543343283583229374092813 19328753731343711015284805)
                    ·
                      refine ⟨3624141324626945815365901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19328753731343711015284805 3624141324626945815365901)
                      ·
                        rfl

theorem cell23_7057990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 1, 1, 3, 4].length) (baseStart_7057990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7057990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7057990 prefixEnd_7057990 := by exact prefixLift 7057990
  have htrace : WordTrace (prefixWord ++ tailWord_7057990) baseStart_7057990 baseEnd_7057990 := by
    simpa [prefixWord, tailWord_7057990, baseEnd_7057990] using wordTrace_append hprefix tailTrace_7057990
  have hstable : (prefixWord ++ tailWord_7057990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7057990).length < 2 ^ (prefixWord ++ tailWord_7057990).sum := by decide
  have hdescent : baseEnd_7057990 < baseStart_7057990 := by decide
  rcases family_descends (prefixWord ++ tailWord_7057990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7058017 : List Nat := [1, 2, 3, 1, 1, 5, 3, 2, 1, 4]
def baseStart_7058017 : Nat := 118140960795 + 7058017 * 2 ^ 59
def prefixEnd_7058017 : Nat := 4983230072969 + 3 ^ 40 * 7058017 * 2
def baseEnd_7058017 : Nat := 1208051729534872403242759

theorem tailTrace_7058017 : CollatzResearch.WordTrace tailWord_7058017 prefixEnd_7058017 1208051729534872403242759 := by
  unfold tailWord_7058017
  simp only [CollatzResearch.WordTrace]
  refine ⟨257427028471017297180852305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171618018980678198120568203 257427028471017297180852305)
  ·
    refine ⟨193070271353262972885639229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257427028471017297180852305 193070271353262972885639229)
    ·
      refine ⟨72401351757473614832114711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 193070271353262972885639229 72401351757473614832114711)
      ·
        refine ⟨108602027636210422248172067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72401351757473614832114711 108602027636210422248172067)
        ·
          refine ⟨162903041454315633372258101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108602027636210422248172067 162903041454315633372258101)
          ·
            refine ⟨15272160136342090628649197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 162903041454315633372258101 15272160136342090628649197)
            ·
              refine ⟨5727060051128283985743449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15272160136342090628649197 5727060051128283985743449)
              ·
                refine ⟨4295295038346212989307587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5727060051128283985743449 4295295038346212989307587)
                ·
                  refine ⟨6442942557519319483961381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4295295038346212989307587 6442942557519319483961381)
                  ·
                    refine ⟨1208051729534872403242759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6442942557519319483961381 1208051729534872403242759)
                    ·
                      rfl

theorem cell23_7058017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 3, 2, 1, 4].length) (baseStart_7058017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7058017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7058017 prefixEnd_7058017 := by exact prefixLift 7058017
  have htrace : WordTrace (prefixWord ++ tailWord_7058017) baseStart_7058017 baseEnd_7058017 := by
    simpa [prefixWord, tailWord_7058017, baseEnd_7058017] using wordTrace_append hprefix tailTrace_7058017
  have hstable : (prefixWord ++ tailWord_7058017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7058017).length < 2 ^ (prefixWord ++ tailWord_7058017).sum := by decide
  have hdescent : baseEnd_7058017 < baseStart_7058017 := by decide
  rcases family_descends (prefixWord ++ tailWord_7058017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7058030 : List Nat := [4, 1, 2, 2, 2, 1, 4, 1, 6]
def baseStart_7058030 : Nat := 118140960795 + 7058030 * 2 ^ 59
def prefixEnd_7058030 : Nat := 4983230072969 + 3 ^ 40 * 7058030 * 2
def baseEnd_7058030 : Nat := 402684651539236184318413

theorem tailTrace_7058030 : CollatzResearch.WordTrace tailWord_7058030 prefixEnd_7058030 402684651539236184318413 := by
  unfold tailWord_7058030
  simp only [CollatzResearch.WordTrace]
  refine ⟨32178437827496275050134443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 171618335079980133600717029 32178437827496275050134443)
  ·
    refine ⟨48267656741244412575201665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32178437827496275050134443 48267656741244412575201665)
    ·
      refine ⟨36200742555933309431401249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48267656741244412575201665 36200742555933309431401249)
      ·
        refine ⟨27150556916949982073550937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36200742555933309431401249 27150556916949982073550937)
        ·
          refine ⟨20362917687712486555163203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27150556916949982073550937 20362917687712486555163203)
          ·
            refine ⟨30544376531568729832744805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20362917687712486555163203 30544376531568729832744805)
            ·
              refine ⟨5727070599669136843639651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30544376531568729832744805 5727070599669136843639651)
              ·
                refine ⟨8590605899503705265459477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5727070599669136843639651 8590605899503705265459477)
                ·
                  refine ⟨402684651539236184318413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8590605899503705265459477 402684651539236184318413)
                  ·
                    rfl

theorem cell23_7058030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 4, 1, 6].length) (baseStart_7058030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7058030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7058030 prefixEnd_7058030 := by exact prefixLift 7058030
  have htrace : WordTrace (prefixWord ++ tailWord_7058030) baseStart_7058030 baseEnd_7058030 := by
    simpa [prefixWord, tailWord_7058030, baseEnd_7058030] using wordTrace_append hprefix tailTrace_7058030
  have hstable : (prefixWord ++ tailWord_7058030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7058030).length < 2 ^ (prefixWord ++ tailWord_7058030).sum := by decide
  have hdescent : baseEnd_7058030 < baseStart_7058030 := by decide
  rcases family_descends (prefixWord ++ tailWord_7058030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7058147 : List Nat := [1, 1, 1, 7, 1, 3, 1, 1, 1, 3, 3]
def baseStart_7058147 : Nat := 118140960795 + 7058147 * 2 ^ 59
def prefixEnd_7058147 : Nat := 4983230072969 + 3 ^ 40 * 7058147 * 2
def baseEnd_7058147 : Nat := 3624221941089701701102679

theorem tailTrace_7058147 : CollatzResearch.WordTrace tailWord_7058147 prefixEnd_7058147 3624221941089701701102679 := by
  unfold tailWord_7058147
  simp only [CollatzResearch.WordTrace]
  refine ⟨257431769960546329383084695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171621179973697552922056463 257431769960546329383084695)
  ·
    refine ⟨386147654940819494074627043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257431769960546329383084695 386147654940819494074627043)
    ·
      refine ⟨579221482411229241111940565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 386147654940819494074627043 579221482411229241111940565)
      ·
        refine ⟨13575503494013185338561107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 579221482411229241111940565 13575503494013185338561107)
        ·
          refine ⟨20363255241019778007841661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13575503494013185338561107 20363255241019778007841661)
          ·
            refine ⟨7636220715382416752940623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20363255241019778007841661 7636220715382416752940623)
            ·
              refine ⟨11454331073073625129410935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7636220715382416752940623 11454331073073625129410935)
              ·
                refine ⟨17181496609610437694116403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11454331073073625129410935 17181496609610437694116403)
                ·
                  refine ⟨25772244914415656541174605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17181496609610437694116403 25772244914415656541174605)
                  ·
                    refine ⟨9664591842905871202940477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25772244914415656541174605 9664591842905871202940477)
                    ·
                      refine ⟨3624221941089701701102679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9664591842905871202940477 3624221941089701701102679)
                      ·
                        rfl

theorem cell23_7058147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 1, 1, 1, 3, 3].length) (baseStart_7058147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7058147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7058147 prefixEnd_7058147 := by exact prefixLift 7058147
  have htrace : WordTrace (prefixWord ++ tailWord_7058147) baseStart_7058147 baseEnd_7058147 := by
    simpa [prefixWord, tailWord_7058147, baseEnd_7058147] using wordTrace_append hprefix tailTrace_7058147
  have hstable : (prefixWord ++ tailWord_7058147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7058147).length < 2 ^ (prefixWord ++ tailWord_7058147).sum := by decide
  have hdescent : baseEnd_7058147 < baseStart_7058147 := by decide
  rcases family_descends (prefixWord ++ tailWord_7058147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7058170 : List Nat := [3, 1, 1, 1, 1, 3, 2, 4, 1, 4, 2]
def baseStart_7058170 : Nat := 118140960795 + 7058170 * 2 ^ 59
def prefixEnd_7058170 : Nat := 4983230072969 + 3 ^ 40 * 7058170 * 2
def baseEnd_7058170 : Nat := 3624233751144755111115073

theorem tailTrace_7058170 : CollatzResearch.WordTrace tailWord_7058170 prefixEnd_7058170 3624233751144755111115073 := by
  unfold tailWord_7058170
  simp only [CollatzResearch.WordTrace]
  refine ⟨64358152209865751077792991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171621739226308669540781309 64358152209865751077792991)
  ·
    refine ⟨96537228314798626616689487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64358152209865751077792991 96537228314798626616689487)
    ·
      refine ⟨144805842472197939925034231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96537228314798626616689487 144805842472197939925034231)
      ·
        refine ⟨217208763708296909887551347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144805842472197939925034231 217208763708296909887551347)
        ·
          refine ⟨325813145562445364831327021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217208763708296909887551347 325813145562445364831327021)
          ·
            refine ⟨122179929585917011811747633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 325813145562445364831327021 122179929585917011811747633)
            ·
              refine ⟨91634947189437758858810725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122179929585917011811747633 91634947189437758858810725)
              ·
                refine ⟨17181552598019579786027011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 91634947189437758858810725 17181552598019579786027011)
                ·
                  refine ⟨25772328897029369679040517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17181552598019579786027011 25772328897029369679040517)
                  ·
                    refine ⟨4832311668193006814820097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25772328897029369679040517 4832311668193006814820097)
                    ·
                      refine ⟨3624233751144755111115073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4832311668193006814820097 3624233751144755111115073)
                      ·
                        rfl

theorem cell23_7058170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 4, 1, 4, 2].length) (baseStart_7058170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7058170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7058170 prefixEnd_7058170 := by exact prefixLift 7058170
  have htrace : WordTrace (prefixWord ++ tailWord_7058170) baseStart_7058170 baseEnd_7058170 := by
    simpa [prefixWord, tailWord_7058170, baseEnd_7058170] using wordTrace_append hprefix tailTrace_7058170
  have hstable : (prefixWord ++ tailWord_7058170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7058170).length < 2 ^ (prefixWord ++ tailWord_7058170).sum := by decide
  have hdescent : baseEnd_7058170 < baseStart_7058170 := by decide
  rcases family_descends (prefixWord ++ tailWord_7058170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7058173 : List Nat := [1, 4, 1, 1, 1, 1, 5, 1, 2, 1, 5]
def baseStart_7058173 : Nat := 118140960795 + 7058173 * 2 ^ 59
def prefixEnd_7058173 : Nat := 4983230072969 + 3 ^ 40 * 7058173 * 2
def baseEnd_7058173 : Nat := 3624235291586718599377559

theorem tailTrace_7058173 : CollatzResearch.WordTrace tailWord_7058173 prefixEnd_7058173 3624235291586718599377559 := by
  unfold tailWord_7058173
  simp only [CollatzResearch.WordTrace]
  refine ⟨257432718258452135823531173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171621812172301423882354115 257432718258452135823531173)
  ·
    refine ⟨48268634673459775466912095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 257432718258452135823531173 48268634673459775466912095)
    ·
      refine ⟨72402952010189663200368143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48268634673459775466912095 72402952010189663200368143)
      ·
        refine ⟨108604428015284494800552215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72402952010189663200368143 108604428015284494800552215)
        ·
          refine ⟨162906642022926742200828323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108604428015284494800552215 162906642022926742200828323)
          ·
            refine ⟨244359963034390113301242485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162906642022926742200828323 244359963034390113301242485)
            ·
              refine ⟨22908746534474073121991483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 244359963034390113301242485 22908746534474073121991483)
              ·
                refine ⟨34363119801711109682987225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22908746534474073121991483 34363119801711109682987225)
                ·
                  refine ⟨25772339851283332262240419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34363119801711109682987225 25772339851283332262240419)
                  ·
                    refine ⟨38658509776924998393360629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25772339851283332262240419 38658509776924998393360629)
                    ·
                      refine ⟨3624235291586718599377559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38658509776924998393360629 3624235291586718599377559)
                      ·
                        rfl

theorem cell23_7058173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 1, 2, 1, 5].length) (baseStart_7058173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7058173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7058173 prefixEnd_7058173 := by exact prefixLift 7058173
  have htrace : WordTrace (prefixWord ++ tailWord_7058173) baseStart_7058173 baseEnd_7058173 := by
    simpa [prefixWord, tailWord_7058173, baseEnd_7058173] using wordTrace_append hprefix tailTrace_7058173
  have hstable : (prefixWord ++ tailWord_7058173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7058173).length < 2 ^ (prefixWord ++ tailWord_7058173).sum := by decide
  have hdescent : baseEnd_7058173 < baseStart_7058173 := by decide
  rcases family_descends (prefixWord ++ tailWord_7058173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7058174 : List Nat := [4, 2, 2, 1, 2, 1, 2, 3, 1, 3, 2]
def baseStart_7058174 : Nat := 118140960795 + 7058174 * 2 ^ 59
def prefixEnd_7058174 : Nat := 4983230072969 + 3 ^ 40 * 7058174 * 2
def baseEnd_7058174 : Nat := 3624235805067373095465055

theorem tailTrace_7058174 : CollatzResearch.WordTrace tailWord_7058174 prefixEnd_7058174 3624235805067373095465055 := by
  unfold tailWord_7058174
  simp only [CollatzResearch.WordTrace]
  refine ⟨32179094341431064124289697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 171621836487632341996211717 32179094341431064124289697)
  ·
    refine ⟨24134320756073298093217273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32179094341431064124289697 24134320756073298093217273)
    ·
      refine ⟨18100740567054973569912955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24134320756073298093217273 18100740567054973569912955)
      ·
        refine ⟨27151110850582460354869433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18100740567054973569912955 27151110850582460354869433)
        ·
          refine ⟨20363333137936845266152075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27151110850582460354869433 20363333137936845266152075)
          ·
            refine ⟨30544999706905267899228113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20363333137936845266152075 30544999706905267899228113)
            ·
              refine ⟨22908749780178950924421085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30544999706905267899228113 22908749780178950924421085)
              ·
                refine ⟨8590781167567106596657907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22908749780178950924421085 8590781167567106596657907)
                ·
                  refine ⟨12886171751350659894986861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8590781167567106596657907 12886171751350659894986861)
                  ·
                    refine ⟨4832314406756497460620073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12886171751350659894986861 4832314406756497460620073)
                    ·
                      refine ⟨3624235805067373095465055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4832314406756497460620073 3624235805067373095465055)
                      ·
                        rfl

theorem cell23_7058174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 3, 1, 3, 2].length) (baseStart_7058174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7058174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7058174 prefixEnd_7058174 := by exact prefixLift 7058174
  have htrace : WordTrace (prefixWord ++ tailWord_7058174) baseStart_7058174 baseEnd_7058174 := by
    simpa [prefixWord, tailWord_7058174, baseEnd_7058174] using wordTrace_append hprefix tailTrace_7058174
  have hstable : (prefixWord ++ tailWord_7058174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7058174).length < 2 ^ (prefixWord ++ tailWord_7058174).sum := by decide
  have hdescent : baseEnd_7058174 < baseStart_7058174 := by decide
  rcases family_descends (prefixWord ++ tailWord_7058174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7058187 : List Nat := [1, 1, 1, 1, 5, 1, 1, 6, 2, 2, 2]
def baseStart_7058187 : Nat := 118140960795 + 7058187 * 2 ^ 59
def prefixEnd_7058187 : Nat := 4983230072969 + 3 ^ 40 * 7058187 * 2
def baseEnd_7058187 : Nat := 3624242480315881544602495

theorem tailTrace_7058187 : CollatzResearch.WordTrace tailWord_7058187 prefixEnd_7058187 3624242480315881544602495 := by
  unfold tailWord_7058187
  simp only [CollatzResearch.WordTrace]
  refine ⟨257433228880401416214540815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171622152586934277476360543 257433228880401416214540815)
  ·
    refine ⟨386149843320602124321811223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257433228880401416214540815 386149843320602124321811223)
    ·
      refine ⟨579224764980903186482716835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 386149843320602124321811223 579224764980903186482716835)
      ·
        refine ⟨868837147471354779724075253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 579224764980903186482716835 868837147471354779724075253)
        ·
          refine ⟨81453482575439510599132055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 868837147471354779724075253 81453482575439510599132055)
          ·
            refine ⟨122180223863159265898698083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81453482575439510599132055 122180223863159265898698083)
            ·
              refine ⟨183270335794738898848047125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122180223863159265898698083 183270335794738898848047125)
              ·
                refine ⟨8590796990378385883502209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 183270335794738898848047125 8590796990378385883502209)
                ·
                  refine ⟨6443097742783789412626657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8590796990378385883502209 6443097742783789412626657)
                  ·
                    refine ⟨4832323307087842059469993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6443097742783789412626657 4832323307087842059469993)
                    ·
                      refine ⟨3624242480315881544602495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4832323307087842059469993 3624242480315881544602495)
                      ·
                        rfl

theorem cell23_7058187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 6, 2, 2, 2].length) (baseStart_7058187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7058187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7058187 prefixEnd_7058187 := by exact prefixLift 7058187
  have htrace : WordTrace (prefixWord ++ tailWord_7058187) baseStart_7058187 baseEnd_7058187 := by
    simpa [prefixWord, tailWord_7058187, baseEnd_7058187] using wordTrace_append hprefix tailTrace_7058187
  have hstable : (prefixWord ++ tailWord_7058187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7058187).length < 2 ^ (prefixWord ++ tailWord_7058187).sum := by decide
  have hdescent : baseEnd_7058187 < baseStart_7058187 := by decide
  rcases family_descends (prefixWord ++ tailWord_7058187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7058193 : List Nat := [1, 2, 2, 1, 1, 3, 5, 1, 7]
def baseStart_7058193 : Nat := 118140960795 + 7058193 * 2 ^ 59
def prefixEnd_7058193 : Nat := 4983230072969 + 3 ^ 40 * 7058193 * 2
def baseEnd_7058193 : Nat := 402693951244423169014163

theorem tailTrace_7058193 : CollatzResearch.WordTrace tailWord_7058193 prefixEnd_7058193 402693951244423169014163 := by
  unfold tailWord_7058193
  simp only [CollatzResearch.WordTrace]
  refine ⟨257433447718379679239259233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171622298478919786159506155 257433447718379679239259233)
  ·
    refine ⟨193075085788784759429444425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257433447718379679239259233 193075085788784759429444425)
    ·
      refine ⟨144806314341588569572083319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193075085788784759429444425 144806314341588569572083319)
      ·
        refine ⟨217209471512382854358124979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144806314341588569572083319 217209471512382854358124979)
        ·
          refine ⟨325814207268574281537187469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217209471512382854358124979 325814207268574281537187469)
          ·
            refine ⟨122180327725715355576445301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 325814207268574281537187469 122180327725715355576445301)
            ·
              refine ⟨11454405724285814585291747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 122180327725715355576445301 11454405724285814585291747)
              ·
                refine ⟨17181608586428721877937621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11454405724285814585291747 17181608586428721877937621)
                ·
                  refine ⟨402693951244423169014163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17181608586428721877937621 402693951244423169014163)
                  ·
                    rfl

theorem cell23_7058193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 5, 1, 7].length) (baseStart_7058193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7058193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7058193 prefixEnd_7058193 := by exact prefixLift 7058193
  have htrace : WordTrace (prefixWord ++ tailWord_7058193) baseStart_7058193 baseEnd_7058193 := by
    simpa [prefixWord, tailWord_7058193, baseEnd_7058193] using wordTrace_append hprefix tailTrace_7058193
  have hstable : (prefixWord ++ tailWord_7058193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7058193).length < 2 ^ (prefixWord ++ tailWord_7058193).sum := by decide
  have hdescent : baseEnd_7058193 < baseStart_7058193 := by decide
  rcases family_descends (prefixWord ++ tailWord_7058193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7058204 : List Nat := [2, 2, 3, 1, 1, 4, 1, 3, 2, 2, 2]
def baseStart_7058204 : Nat := 118140960795 + 7058204 * 2 ^ 59
def prefixEnd_7058204 : Nat := 4983230072969 + 3 ^ 40 * 7058204 * 2
def baseEnd_7058204 : Nat := 3624251209487007978089917

theorem tailTrace_7058204 : CollatzResearch.WordTrace tailWord_7058204 prefixEnd_7058204 3624251209487007978089917 := by
  unfold tailWord_7058204
  simp only [CollatzResearch.WordTrace]
  refine ⟨128716924460669914058954833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171622565947559885411939777 128716924460669914058954833)
  ·
    refine ⟨96537693345502435544216125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128716924460669914058954833 96537693345502435544216125)
    ·
      refine ⟨36201635004563413329081047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96537693345502435544216125 36201635004563413329081047)
      ·
        refine ⟨54302452506845119993621571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36201635004563413329081047 54302452506845119993621571)
        ·
          refine ⟨81453678760267679990432357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54302452506845119993621571 81453678760267679990432357)
          ·
            refine ⟨15272564767550189998206067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 81453678760267679990432357 15272564767550189998206067)
            ·
              refine ⟨22908847151325284997309101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15272564767550189998206067 22908847151325284997309101)
              ·
                refine ⟨8590817681746981873990913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22908847151325284997309101 8590817681746981873990913)
                ·
                  refine ⟨6443113261310236405493185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8590817681746981873990913 6443113261310236405493185)
                  ·
                    refine ⟨4832334945982677304119889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6443113261310236405493185 4832334945982677304119889)
                    ·
                      refine ⟨3624251209487007978089917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4832334945982677304119889 3624251209487007978089917)
                      ·
                        rfl

theorem cell23_7058204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 3, 2, 2, 2].length) (baseStart_7058204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7058204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7058204 prefixEnd_7058204 := by exact prefixLift 7058204
  have htrace : WordTrace (prefixWord ++ tailWord_7058204) baseStart_7058204 baseEnd_7058204 := by
    simpa [prefixWord, tailWord_7058204, baseEnd_7058204] using wordTrace_append hprefix tailTrace_7058204
  have hstable : (prefixWord ++ tailWord_7058204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7058204).length < 2 ^ (prefixWord ++ tailWord_7058204).sum := by decide
  have hdescent : baseEnd_7058204 < baseStart_7058204 := by decide
  rcases family_descends (prefixWord ++ tailWord_7058204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7058221 : List Nat := [1, 5, 3, 2, 1, 1, 1, 2, 1, 4, 2]
def baseStart_7058221 : Nat := 118140960795 + 7058221 * 2 ^ 59
def prefixEnd_7058221 : Nat := 4983230072969 + 3 ^ 40 * 7058221 * 2
def baseEnd_7058221 : Nat := 3624259938658134411577339

theorem tailTrace_7058221 : CollatzResearch.WordTrace tailWord_7058221 prefixEnd_7058221 3624259938658134411577339 := by
  unfold tailWord_7058221
  simp only [CollatzResearch.WordTrace]
  refine ⟨257434468962278240021278517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171622979308185493347519011 257434468962278240021278517)
  ·
    refine ⟨24134481465213585001994861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 257434468962278240021278517 24134481465213585001994861)
    ·
      refine ⟨9050430549455094375748073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24134481465213585001994861 9050430549455094375748073)
      ·
        refine ⟨6787822912091320781811055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9050430549455094375748073 6787822912091320781811055)
        ·
          refine ⟨10181734368136981172716583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6787822912091320781811055 10181734368136981172716583)
          ·
            refine ⟨15272601552205471759074875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10181734368136981172716583 15272601552205471759074875)
            ·
              refine ⟨22908902328308207638612313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15272601552205471759074875 22908902328308207638612313)
              ·
                refine ⟨17181676746231155728959235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22908902328308207638612313 17181676746231155728959235)
                ·
                  refine ⟨25772515119346733593438853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17181676746231155728959235 25772515119346733593438853)
                  ·
                    refine ⟨4832346584877512548769785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25772515119346733593438853 4832346584877512548769785)
                    ·
                      refine ⟨3624259938658134411577339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4832346584877512548769785 3624259938658134411577339)
                      ·
                        rfl

theorem cell23_7058221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 2, 1, 4, 2].length) (baseStart_7058221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7058221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7058221 prefixEnd_7058221 := by exact prefixLift 7058221
  have htrace : WordTrace (prefixWord ++ tailWord_7058221) baseStart_7058221 baseEnd_7058221 := by
    simpa [prefixWord, tailWord_7058221, baseEnd_7058221] using wordTrace_append hprefix tailTrace_7058221
  have hstable : (prefixWord ++ tailWord_7058221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7058221).length < 2 ^ (prefixWord ++ tailWord_7058221).sum := by decide
  have hdescent : baseEnd_7058221 < baseStart_7058221 := by decide
  rcases family_descends (prefixWord ++ tailWord_7058221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7058273 : List Nat := [1, 2, 3, 1, 1, 1, 2, 1, 1, 6, 4]
def baseStart_7058273 : Nat := 118140960795 + 7058273 * 2 ^ 59
def prefixEnd_7058273 : Nat := 4983230072969 + 3 ^ 40 * 7058273 * 2
def baseEnd_7058273 : Nat := 3624286639652168208127099

theorem tailTrace_7058273 : CollatzResearch.WordTrace tailWord_7058273 prefixEnd_7058273 3624286639652168208127099 := by
  unfold tailWord_7058273
  simp only [CollatzResearch.WordTrace]
  refine ⟨257436365558089852902171473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171624243705393235268114315 257436365558089852902171473)
  ·
    refine ⟨193077274168567389676628605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257436365558089852902171473 193077274168567389676628605)
    ·
      refine ⟨72403977813212771128735727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 193077274168567389676628605 72403977813212771128735727)
      ·
        refine ⟨108605966719819156693103591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72403977813212771128735727 108605966719819156693103591)
        ·
          refine ⟨162908950079728735039655387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108605966719819156693103591 162908950079728735039655387)
          ·
            refine ⟨244363425119593102559483081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162908950079728735039655387 244363425119593102559483081)
            ·
              refine ⟨183272568839694826919612311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 244363425119593102559483081 183272568839694826919612311)
              ·
                refine ⟨274908853259542240379418467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 183272568839694826919612311 274908853259542240379418467)
                ·
                  refine ⟨412363279889313360569127701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 274908853259542240379418467 412363279889313360569127701)
                  ·
                    refine ⟨19329528744811563776677861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 412363279889313360569127701 19329528744811563776677861)
                    ·
                      refine ⟨3624286639652168208127099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19329528744811563776677861 3624286639652168208127099)
                      ·
                        rfl

theorem cell23_7058273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 1, 1, 6, 4].length) (baseStart_7058273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7058273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7058273 prefixEnd_7058273 := by exact prefixLift 7058273
  have htrace : WordTrace (prefixWord ++ tailWord_7058273) baseStart_7058273 baseEnd_7058273 := by
    simpa [prefixWord, tailWord_7058273, baseEnd_7058273] using wordTrace_append hprefix tailTrace_7058273
  have hstable : (prefixWord ++ tailWord_7058273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7058273).length < 2 ^ (prefixWord ++ tailWord_7058273).sum := by decide
  have hdescent : baseEnd_7058273 < baseStart_7058273 := by decide
  rcases family_descends (prefixWord ++ tailWord_7058273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7058274 : List Nat := [3, 3, 2, 1, 3, 2, 1, 1, 2, 5]
def baseStart_7058274 : Nat := 118140960795 + 7058274 * 2 ^ 59
def prefixEnd_7058274 : Nat := 4983230072969 + 3 ^ 40 * 7058274 * 2
def baseEnd_7058274 : Nat := 1208095717710940901404865

theorem tailTrace_7058274 : CollatzResearch.WordTrace tailWord_7058274 prefixEnd_7058274 1208095717710940901404865 := by
  unfold tailWord_7058274
  simp only [CollatzResearch.WordTrace]
  refine ⟨64359100507771557518239469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171624268020724153381971917 64359100507771557518239469)
  ·
    refine ⟨24134662690414334069339801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64359100507771557518239469 24134662690414334069339801)
    ·
      refine ⟨18100997017810750552004851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24134662690414334069339801 18100997017810750552004851)
      ·
        refine ⟨27151495526716125828007277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18100997017810750552004851 27151495526716125828007277)
        ·
          refine ⟨10181810822518547185502729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27151495526716125828007277 10181810822518547185502729)
          ·
            refine ⟨7636358116888910389127047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10181810822518547185502729 7636358116888910389127047)
            ·
              refine ⟨11454537175333365583690571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7636358116888910389127047 11454537175333365583690571)
              ·
                refine ⟨17181805763000048375535857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11454537175333365583690571 17181805763000048375535857)
                ·
                  refine ⟨12886354322250036281651893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17181805763000048375535857 12886354322250036281651893)
                  ·
                    refine ⟨1208095717710940901404865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12886354322250036281651893 1208095717710940901404865)
                    ·
                      rfl

theorem cell23_7058274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 1, 1, 2, 5].length) (baseStart_7058274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7058274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7058274 prefixEnd_7058274 := by exact prefixLift 7058274
  have htrace : WordTrace (prefixWord ++ tailWord_7058274) baseStart_7058274 baseEnd_7058274 := by
    simpa [prefixWord, tailWord_7058274, baseEnd_7058274] using wordTrace_append hprefix tailTrace_7058274
  have hstable : (prefixWord ++ tailWord_7058274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7058274).length < 2 ^ (prefixWord ++ tailWord_7058274).sum := by decide
  have hdescent : baseEnd_7058274 < baseStart_7058274 := by decide
  rcases family_descends (prefixWord ++ tailWord_7058274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7058294 : List Nat := [5, 1, 1, 3, 1, 1, 1, 2, 2, 4, 2]
def baseStart_7058294 : Nat := 118140960795 + 7058294 * 2 ^ 59
def prefixEnd_7058294 : Nat := 4983230072969 + 3 ^ 40 * 7058294 * 2
def baseEnd_7058294 : Nat := 3624297422745912625964503

theorem tailTrace_7058294 : CollatzResearch.WordTrace tailWord_7058294 prefixEnd_7058294 3624297422745912625964503 := by
  unfold tailWord_7058294
  simp only [CollatzResearch.WordTrace]
  refine ⟨16089820718188360843042871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 171624754327342515659123957 16089820718188360843042871)
  ·
    refine ⟨24134731077282541264564307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16089820718188360843042871 24134731077282541264564307)
    ·
      refine ⟨36202096615923811896846461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24134731077282541264564307 36202096615923811896846461)
      ·
        refine ⟨13575786230971429461317423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36202096615923811896846461 13575786230971429461317423)
        ·
          refine ⟨20363679346457144191976135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13575786230971429461317423 20363679346457144191976135)
          ·
            refine ⟨30545519019685716287964203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20363679346457144191976135 30545519019685716287964203)
            ·
              refine ⟨45818278529528574431946305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30545519019685716287964203 45818278529528574431946305)
              ·
                refine ⟨34363708897146430823959729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45818278529528574431946305 34363708897146430823959729)
                ·
                  refine ⟨25772781672859823117969797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34363708897146430823959729 25772781672859823117969797)
                  ·
                    refine ⟨4832396563661216834619337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25772781672859823117969797 4832396563661216834619337)
                    ·
                      refine ⟨3624297422745912625964503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4832396563661216834619337 3624297422745912625964503)
                      ·
                        rfl

theorem cell23_7058294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 2, 2, 4, 2].length) (baseStart_7058294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7058294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7058294 prefixEnd_7058294 := by exact prefixLift 7058294
  have htrace : WordTrace (prefixWord ++ tailWord_7058294) baseStart_7058294 baseEnd_7058294 := by
    simpa [prefixWord, tailWord_7058294, baseEnd_7058294] using wordTrace_append hprefix tailTrace_7058294
  have hstable : (prefixWord ++ tailWord_7058294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7058294).length < 2 ^ (prefixWord ++ tailWord_7058294).sum := by decide
  have hdescent : baseEnd_7058294 < baseStart_7058294 := by decide
  rcases family_descends (prefixWord ++ tailWord_7058294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7058303 : List Nat := [1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 6]
def baseStart_7058303 : Nat := 118140960795 + 7058303 * 2 ^ 59
def prefixEnd_7058303 : Nat := 4983230072969 + 3 ^ 40 * 7058303 * 2
def baseEnd_7058303 : Nat := 3624302044071803090751961

theorem tailTrace_7058303 : CollatzResearch.WordTrace tailWord_7058303 prefixEnd_7058303 3624302044071803090751961 := by
  unfold tailWord_7058303
  simp only [CollatzResearch.WordTrace]
  refine ⟨257437459747981168025763563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171624973165320778683842375 257437459747981168025763563)
  ·
    refine ⟨386156189621971752038645345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257437459747981168025763563 386156189621971752038645345)
    ·
      refine ⟨289617142216478814028984009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 386156189621971752038645345 289617142216478814028984009)
      ·
        refine ⟨217212856662359110521738007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 289617142216478814028984009 217212856662359110521738007)
        ·
          refine ⟨325819284993538665782607011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217212856662359110521738007 325819284993538665782607011)
          ·
            refine ⟨488728927490307998673910517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 325819284993538665782607011 488728927490307998673910517)
            ·
              refine ⟨45818336952216374875679111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 488728927490307998673910517 45818336952216374875679111)
              ·
                refine ⟨68727505428324562313518667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45818336952216374875679111 68727505428324562313518667)
                ·
                  refine ⟨103091258142486843470278001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68727505428324562313518667 103091258142486843470278001)
                  ·
                    refine ⟨77318443606865132602708501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 103091258142486843470278001 77318443606865132602708501)
                    ·
                      refine ⟨3624302044071803090751961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 77318443606865132602708501 3624302044071803090751961)
                      ·
                        rfl

theorem cell23_7058303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 6].length) (baseStart_7058303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7058303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7058303 prefixEnd_7058303 := by exact prefixLift 7058303
  have htrace : WordTrace (prefixWord ++ tailWord_7058303) baseStart_7058303 baseEnd_7058303 := by
    simpa [prefixWord, tailWord_7058303, baseEnd_7058303] using wordTrace_append hprefix tailTrace_7058303
  have hstable : (prefixWord ++ tailWord_7058303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7058303).length < 2 ^ (prefixWord ++ tailWord_7058303).sum := by decide
  have hdescent : baseEnd_7058303 < baseStart_7058303 := by decide
  rcases family_descends (prefixWord ++ tailWord_7058303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7058327 : List Nat := [1, 1, 3, 3, 1, 2, 1, 4, 3, 1, 3]
def baseStart_7058327 : Nat := 118140960795 + 7058327 * 2 ^ 59
def prefixEnd_7058327 : Nat := 4983230072969 + 3 ^ 40 * 7058327 * 2
def baseEnd_7058327 : Nat := 3624314367607510996851851

theorem tailTrace_7058327 : CollatzResearch.WordTrace tailWord_7058327 prefixEnd_7058327 3624314367607510996851851 := by
  unfold tailWord_7058327
  simp only [CollatzResearch.WordTrace]
  refine ⟨257438335099894220124637235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171625556733262813416424823 257438335099894220124637235)
  ·
    refine ⟨386157502649841330186955853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257438335099894220124637235 386157502649841330186955853)
    ·
      refine ⟨144809063493690498820108445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 386157502649841330186955853 144809063493690498820108445)
      ·
        refine ⟨54303398810133937057540667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144809063493690498820108445 54303398810133937057540667)
        ·
          refine ⟨81455098215200905586311001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54303398810133937057540667 81455098215200905586311001)
          ·
            refine ⟨61091323661400679189733251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81455098215200905586311001 61091323661400679189733251)
            ·
              refine ⟨91636985492101018784599877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61091323661400679189733251 91636985492101018784599877)
              ·
                refine ⟨17181934779768941022112477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 91636985492101018784599877 17181934779768941022112477)
                ·
                  refine ⟨6443225542413352883292179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17181934779768941022112477 6443225542413352883292179)
                  ·
                    refine ⟨9664838313620029324938269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6443225542413352883292179 9664838313620029324938269)
                    ·
                      refine ⟨3624314367607510996851851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9664838313620029324938269 3624314367607510996851851)
                      ·
                        rfl

theorem cell23_7058327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 4, 3, 1, 3].length) (baseStart_7058327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7058327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7058327 prefixEnd_7058327 := by exact prefixLift 7058327
  have htrace : WordTrace (prefixWord ++ tailWord_7058327) baseStart_7058327 baseEnd_7058327 := by
    simpa [prefixWord, tailWord_7058327, baseEnd_7058327] using wordTrace_append hprefix tailTrace_7058327
  have hstable : (prefixWord ++ tailWord_7058327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7058327).length < 2 ^ (prefixWord ++ tailWord_7058327).sum := by decide
  have hdescent : baseEnd_7058327 < baseStart_7058327 := by decide
  rcases family_descends (prefixWord ++ tailWord_7058327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7058380 : List Nat := [2, 2, 1, 4, 1, 1, 1, 3, 1, 1, 6]
def baseStart_7058380 : Nat := 118140960795 + 7058380 * 2 ^ 59
def prefixEnd_7058380 : Nat := 4983230072969 + 3 ^ 40 * 7058380 * 2
def baseEnd_7058380 : Nat := 3624341582082199289489107

theorem tailTrace_7058380 : CollatzResearch.WordTrace tailWord_7058380 prefixEnd_7058380 3624341582082199289489107 := by
  unfold tailWord_7058380
  simp only [CollatzResearch.WordTrace]
  refine ⟨128720134084351105088158297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171626845445801473450877729 128720134084351105088158297)
  ·
    refine ⟨96540100563263328816118723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128720134084351105088158297 96540100563263328816118723)
    ·
      refine ⟨144810150844894993224178085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96540100563263328816118723 144810150844894993224178085)
      ·
        refine ⟨27151903283417811229533391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 144810150844894993224178085 27151903283417811229533391)
        ·
          refine ⟨40727854925126716844300087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27151903283417811229533391 40727854925126716844300087)
          ·
            refine ⟨61091782387690075266450131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40727854925126716844300087 61091782387690075266450131)
            ·
              refine ⟨91637673581535112899675197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61091782387690075266450131 91637673581535112899675197)
              ·
                refine ⟨34364127593075667337378199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91637673581535112899675197 34364127593075667337378199)
                ·
                  refine ⟨51546191389613501006067299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34364127593075667337378199 51546191389613501006067299)
                  ·
                    refine ⟨77319287084420251509100949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51546191389613501006067299 77319287084420251509100949)
                    ·
                      refine ⟨3624341582082199289489107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 77319287084420251509100949 3624341582082199289489107)
                      ·
                        rfl

theorem cell23_7058380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 3, 1, 1, 6].length) (baseStart_7058380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7058380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7058380 prefixEnd_7058380 := by exact prefixLift 7058380
  have htrace : WordTrace (prefixWord ++ tailWord_7058380) baseStart_7058380 baseEnd_7058380 := by
    simpa [prefixWord, tailWord_7058380, baseEnd_7058380] using wordTrace_append hprefix tailTrace_7058380
  have hstable : (prefixWord ++ tailWord_7058380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7058380).length < 2 ^ (prefixWord ++ tailWord_7058380).sum := by decide
  have hdescent : baseEnd_7058380 < baseStart_7058380 := by decide
  rcases family_descends (prefixWord ++ tailWord_7058380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7058397 : List Nat := [1, 4, 3, 1, 2, 1, 1, 1, 3, 2, 4]
def baseStart_7058397 : Nat := 118140960795 + 7058397 * 2 ^ 59
def prefixEnd_7058397 : Nat := 4983230072969 + 3 ^ 40 * 7058397 * 2
def baseEnd_7058397 : Nat := 3624350311253325722976529

theorem tailTrace_7058397 : CollatzResearch.WordTrace tailWord_7058397 prefixEnd_7058397 3624350311253325722976529 := by
  unfold tailWord_7058397
  simp only [CollatzResearch.WordTrace]
  refine ⟨257440888209640622079685445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171627258806427081386456963 257440888209640622079685445)
  ·
    refine ⟨48270166539307616639941021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 257440888209640622079685445 48270166539307616639941021)
    ·
      refine ⟨18101312452240356239977883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48270166539307616639941021 18101312452240356239977883)
      ·
        refine ⟨27151968678360534359966825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18101312452240356239977883 27151968678360534359966825)
        ·
          refine ⟨20363976508770400769975119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27151968678360534359966825 20363976508770400769975119)
          ·
            refine ⟨30545964763155601154962679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20363976508770400769975119 30545964763155601154962679)
            ·
              refine ⟨45818947144733401732444019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30545964763155601154962679 45818947144733401732444019)
              ·
                refine ⟨68728420717100102598666029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45818947144733401732444019 68728420717100102598666029)
                ·
                  refine ⟨25773157768912538474499761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68728420717100102598666029 25773157768912538474499761)
                  ·
                    refine ⟨19329868326684403855874821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25773157768912538474499761 19329868326684403855874821)
                    ·
                      refine ⟨3624350311253325722976529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19329868326684403855874821 3624350311253325722976529)
                      ·
                        rfl

theorem cell23_7058397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 1, 3, 2, 4].length) (baseStart_7058397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7058397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7058397 prefixEnd_7058397 := by exact prefixLift 7058397
  have htrace : WordTrace (prefixWord ++ tailWord_7058397) baseStart_7058397 baseEnd_7058397 := by
    simpa [prefixWord, tailWord_7058397, baseEnd_7058397] using wordTrace_append hprefix tailTrace_7058397
  have hstable : (prefixWord ++ tailWord_7058397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7058397).length < 2 ^ (prefixWord ++ tailWord_7058397).sum := by decide
  have hdescent : baseEnd_7058397 < baseStart_7058397 := by decide
  rcases family_descends (prefixWord ++ tailWord_7058397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7058401 : List Nat := [1, 2, 3, 1, 2, 1, 1, 7, 1, 2, 2]
def baseStart_7058401 : Nat := 118140960795 + 7058401 * 2 ^ 59
def prefixEnd_7058401 : Nat := 4983230072969 + 3 ^ 40 * 7058401 * 2
def baseEnd_7058401 : Nat := 3624352365175943707326511

theorem tailTrace_7058401 : CollatzResearch.WordTrace tailWord_7058401 prefixEnd_7058401 3624352365175943707326511 := by
  unfold tailWord_7058401
  simp only [CollatzResearch.WordTrace]
  refine ⟨257441034101626130762831057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171627356067750753841887371 257441034101626130762831057)
  ·
    refine ⟨193080775576219598072123293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257441034101626130762831057 193080775576219598072123293)
    ·
      refine ⟨72405290841082349277046235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 193080775576219598072123293 72405290841082349277046235)
      ·
        refine ⟨108607936261623523915569353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72405290841082349277046235 108607936261623523915569353)
        ·
          refine ⟨81455952196217642936677015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108607936261623523915569353 81455952196217642936677015)
          ·
            refine ⟨122183928294326464405015523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81455952196217642936677015 122183928294326464405015523)
            ·
              refine ⟨183275892441489696607523285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122183928294326464405015523 183275892441489696607523285)
              ·
                refine ⟨4295528729097414764238827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 183275892441489696607523285 4295528729097414764238827)
                ·
                  refine ⟨6443293093646122146358241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4295528729097414764238827 6443293093646122146358241)
                  ·
                    refine ⟨4832469820234591609768681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6443293093646122146358241 4832469820234591609768681)
                    ·
                      refine ⟨3624352365175943707326511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4832469820234591609768681 3624352365175943707326511)
                      ·
                        rfl

theorem cell23_7058401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 7, 1, 2, 2].length) (baseStart_7058401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7058401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7058401 prefixEnd_7058401 := by exact prefixLift 7058401
  have htrace : WordTrace (prefixWord ++ tailWord_7058401) baseStart_7058401 baseEnd_7058401 := by
    simpa [prefixWord, tailWord_7058401, baseEnd_7058401] using wordTrace_append hprefix tailTrace_7058401
  have hstable : (prefixWord ++ tailWord_7058401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7058401).length < 2 ^ (prefixWord ++ tailWord_7058401).sum := by decide
  have hdescent : baseEnd_7058401 < baseStart_7058401 := by decide
  rcases family_descends (prefixWord ++ tailWord_7058401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7058444 : List Nat := [2, 2, 1, 2, 3, 2, 2, 1, 3, 3, 2]
def baseStart_7058444 : Nat := 118140960795 + 7058444 * 2 ^ 59
def prefixEnd_7058444 : Nat := 4983230072969 + 3 ^ 40 * 7058444 * 2
def baseEnd_7058444 : Nat := 3624374444844087039088813

theorem tailTrace_7058444 : CollatzResearch.WordTrace tailWord_7058444 prefixEnd_7058444 3624374444844087039088813 := by
  unfold tailWord_7058444
  simp only [CollatzResearch.WordTrace]
  refine ⟨128721301220235174553323193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171628401626980232737764257 128721301220235174553323193)
  ·
    refine ⟨96540975915176380914992395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128721301220235174553323193 96540975915176380914992395)
    ·
      refine ⟨144811463872764571372488593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96540975915176380914992395 144811463872764571372488593)
      ·
        refine ⟨108608597904573428529366445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144811463872764571372488593 108608597904573428529366445)
        ·
          refine ⟨40728224214215035698512417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108608597904573428529366445 40728224214215035698512417)
          ·
            refine ⟨30546168160661276773884313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40728224214215035698512417 30546168160661276773884313)
            ·
              refine ⟨22909626120495957580413235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30546168160661276773884313 22909626120495957580413235)
              ·
                refine ⟨34364439180743936370619853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22909626120495957580413235 34364439180743936370619853)
                ·
                  refine ⟨12886664692778976138982445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34364439180743936370619853 12886664692778976138982445)
                  ·
                    refine ⟨4832499259792116052118417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12886664692778976138982445 4832499259792116052118417)
                    ·
                      refine ⟨3624374444844087039088813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4832499259792116052118417 3624374444844087039088813)
                      ·
                        rfl

theorem cell23_7058444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 1, 3, 3, 2].length) (baseStart_7058444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7058444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7058444 prefixEnd_7058444 := by exact prefixLift 7058444
  have htrace : WordTrace (prefixWord ++ tailWord_7058444) baseStart_7058444 baseEnd_7058444 := by
    simpa [prefixWord, tailWord_7058444, baseEnd_7058444] using wordTrace_append hprefix tailTrace_7058444
  have hstable : (prefixWord ++ tailWord_7058444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7058444).length < 2 ^ (prefixWord ++ tailWord_7058444).sum := by decide
  have hdescent : baseEnd_7058444 < baseStart_7058444 := by decide
  rcases family_descends (prefixWord ++ tailWord_7058444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7058468 : List Nat := [2, 3, 1, 4, 1, 3, 1, 2, 2, 1, 3]
def baseStart_7058468 : Nat := 118140960795 + 7058468 * 2 ^ 59
def prefixEnd_7058468 : Nat := 4983230072969 + 3 ^ 40 * 7058468 * 2
def baseEnd_7058468 : Nat := 3624386768379794945188703

theorem tailTrace_7058468 : CollatzResearch.WordTrace tailWord_7058468 prefixEnd_7058468 3624386768379794945188703 := by
  unfold tailWord_7058468
  simp only [CollatzResearch.WordTrace]
  refine ⟨128721738896191700602760029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171628985194922267470346705 128721738896191700602760029)
  ·
    refine ⟨48270652086071887726035011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128721738896191700602760029 48270652086071887726035011)
    ·
      refine ⟨72405978129107831589052517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48270652086071887726035011 72405978129107831589052517)
      ·
        refine ⟨13576120899207718422947347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72405978129107831589052517 13576120899207718422947347)
        ·
          refine ⟨20364181348811577634421021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13576120899207718422947347 20364181348811577634421021)
          ·
            refine ⟨7636568005804341612907883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20364181348811577634421021 7636568005804341612907883)
            ·
              refine ⟨11454852008706512419361825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7636568005804341612907883 11454852008706512419361825)
              ·
                refine ⟨8591139006529884314521369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11454852008706512419361825 8591139006529884314521369)
                ·
                  refine ⟨6443354254897413235891027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8591139006529884314521369 6443354254897413235891027)
                  ·
                    refine ⟨9665031382346119853836541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6443354254897413235891027 9665031382346119853836541)
                    ·
                      refine ⟨3624386768379794945188703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9665031382346119853836541 3624386768379794945188703)
                      ·
                        rfl

theorem cell23_7058468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 1, 2, 2, 1, 3].length) (baseStart_7058468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7058468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7058468 prefixEnd_7058468 := by exact prefixLift 7058468
  have htrace : WordTrace (prefixWord ++ tailWord_7058468) baseStart_7058468 baseEnd_7058468 := by
    simpa [prefixWord, tailWord_7058468, baseEnd_7058468] using wordTrace_append hprefix tailTrace_7058468
  have hstable : (prefixWord ++ tailWord_7058468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7058468).length < 2 ^ (prefixWord ++ tailWord_7058468).sum := by decide
  have hdescent : baseEnd_7058468 < baseStart_7058468 := by decide
  rcases family_descends (prefixWord ++ tailWord_7058468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7058484 : List Nat := [2, 5, 1, 2, 1, 1, 2, 1, 2, 6]
def baseStart_7058484 : Nat := 118140960795 + 7058484 * 2 ^ 59
def prefixEnd_7058484 : Nat := 4983230072969 + 3 ^ 40 * 7058484 * 2
def baseEnd_7058484 : Nat := 1208131661356755627529543

theorem tailTrace_7058484 : CollatzResearch.WordTrace tailWord_7058484 prefixEnd_7058484 1208131661356755627529543 := by
  unfold tailWord_7058484
  simp only [CollatzResearch.WordTrace]
  refine ⟨128722030680162717969051253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171629374240216957292068337 128722030680162717969051253)
  ·
    refine ⟨12067690376265254809598555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 128722030680162717969051253 12067690376265254809598555)
    ·
      refine ⟨18101535564397882214397833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12067690376265254809598555 18101535564397882214397833)
      ·
        refine ⟨13576151673298411660798375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18101535564397882214397833 13576151673298411660798375)
        ·
          refine ⟨20364227509947617491197563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13576151673298411660798375 20364227509947617491197563)
          ·
            refine ⟨30546341264921426236796345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20364227509947617491197563 30546341264921426236796345)
            ·
              refine ⟨22909755948691069677597259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30546341264921426236796345 22909755948691069677597259)
              ·
                refine ⟨34364633923036604516395889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22909755948691069677597259 34364633923036604516395889)
                ·
                  refine ⟨25773475442277453387296917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34364633923036604516395889 25773475442277453387296917)
                  ·
                    refine ⟨1208131661356755627529543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25773475442277453387296917 1208131661356755627529543)
                    ·
                      rfl

theorem cell23_7058484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 1, 2, 6].length) (baseStart_7058484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7058484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7058484 prefixEnd_7058484 := by exact prefixLift 7058484
  have htrace : WordTrace (prefixWord ++ tailWord_7058484) baseStart_7058484 baseEnd_7058484 := by
    simpa [prefixWord, tailWord_7058484, baseEnd_7058484] using wordTrace_append hprefix tailTrace_7058484
  have hstable : (prefixWord ++ tailWord_7058484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7058484).length < 2 ^ (prefixWord ++ tailWord_7058484).sum := by decide
  have hdescent : baseEnd_7058484 < baseStart_7058484 := by decide
  rcases family_descends (prefixWord ++ tailWord_7058484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7058527 : List Nat := [1, 1, 2, 3, 1, 1, 5, 2, 2, 5]
def baseStart_7058527 : Nat := 118140960795 + 7058527 * 2 ^ 59
def prefixEnd_7058527 : Nat := 4983230072969 + 3 ^ 40 * 7058527 * 2
def baseEnd_7058527 : Nat := 1208139021246136738116977

theorem tailTrace_7058527 : CollatzResearch.WordTrace tailWord_7058527 prefixEnd_7058527 1208139021246136738116977 := by
  unfold tailWord_7058527
  simp only [CollatzResearch.WordTrace]
  refine ⟨257445629699169654281917835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171630419799446436187945223 257445629699169654281917835)
  ·
    refine ⟨386168444548754481422876753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257445629699169654281917835 386168444548754481422876753)
    ·
      refine ⟨289626333411565861067157565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 386168444548754481422876753 289626333411565861067157565)
      ·
        refine ⟨108609875029337197900184087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 289626333411565861067157565 108609875029337197900184087)
        ·
          refine ⟨162914812544005796850276131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108609875029337197900184087 162914812544005796850276131)
          ·
            refine ⟨244372218816008695275414197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162914812544005796850276131 244372218816008695275414197)
            ·
              refine ⟨22909895514000815182070081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 244372218816008695275414197 22909895514000815182070081)
              ·
                refine ⟨17182421635500611386552561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22909895514000815182070081 17182421635500611386552561)
                ·
                  refine ⟨12886816226625458539914421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17182421635500611386552561 12886816226625458539914421)
                  ·
                    refine ⟨1208139021246136738116977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12886816226625458539914421 1208139021246136738116977)
                    ·
                      rfl

theorem cell23_7058527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 2, 2, 5].length) (baseStart_7058527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7058527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7058527 prefixEnd_7058527 := by exact prefixLift 7058527
  have htrace : WordTrace (prefixWord ++ tailWord_7058527) baseStart_7058527 baseEnd_7058527 := by
    simpa [prefixWord, tailWord_7058527, baseEnd_7058527] using wordTrace_append hprefix tailTrace_7058527
  have hstable : (prefixWord ++ tailWord_7058527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7058527).length < 2 ^ (prefixWord ++ tailWord_7058527).sum := by decide
  have hdescent : baseEnd_7058527 < baseStart_7058527 := by decide
  rcases family_descends (prefixWord ++ tailWord_7058527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7058537 : List Nat := [1, 2, 1, 1, 1, 7, 1, 1, 1, 2, 5]
def baseStart_7058537 : Nat := 118140960795 + 7058537 * 2 ^ 59
def prefixEnd_7058537 : Nat := 4983230072969 + 3 ^ 40 * 7058537 * 2
def baseEnd_7058537 : Nat := 3624422198544955175225885

theorem tailTrace_7058537 : CollatzResearch.WordTrace tailWord_7058537 prefixEnd_7058537 3624422198544955175225885 := by
  unfold tailWord_7058537
  simp only [CollatzResearch.WordTrace]
  refine ⟨257445994429133425989781865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171630662952755617326521243 257445994429133425989781865)
  ·
    refine ⟨193084495821850069492336399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257445994429133425989781865 193084495821850069492336399)
    ·
      refine ⟨289626743732775104238504599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193084495821850069492336399 289626743732775104238504599)
      ·
        refine ⟨434440115599162656357756899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 289626743732775104238504599 434440115599162656357756899)
        ·
          refine ⟨651660173398743984536635349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 434440115599162656357756899 651660173398743984536635349)
          ·
            refine ⟨15273285314033062137577391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 651660173398743984536635349 15273285314033062137577391)
            ·
              refine ⟨22909927971049593206366087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15273285314033062137577391 22909927971049593206366087)
              ·
                refine ⟨34364891956574389809549131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22909927971049593206366087 34364891956574389809549131)
                ·
                  refine ⟨51547337934861584714323697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34364891956574389809549131 51547337934861584714323697)
                  ·
                    refine ⟨38660503451146188535742773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51547337934861584714323697 38660503451146188535742773)
                    ·
                      refine ⟨3624422198544955175225885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38660503451146188535742773 3624422198544955175225885)
                      ·
                        rfl

theorem cell23_7058537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 1, 1, 2, 5].length) (baseStart_7058537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7058537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7058537 prefixEnd_7058537 := by exact prefixLift 7058537
  have htrace : WordTrace (prefixWord ++ tailWord_7058537) baseStart_7058537 baseEnd_7058537 := by
    simpa [prefixWord, tailWord_7058537, baseEnd_7058537] using wordTrace_append hprefix tailTrace_7058537
  have hstable : (prefixWord ++ tailWord_7058537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7058537).length < 2 ^ (prefixWord ++ tailWord_7058537).sum := by decide
  have hdescent : baseEnd_7058537 < baseStart_7058537 := by decide
  rcases family_descends (prefixWord ++ tailWord_7058537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7058564 : List Nat := [2, 3, 2, 1, 2, 2, 1, 3, 2, 1, 4]
def baseStart_7058564 : Nat := 118140960795 + 7058564 * 2 ^ 59
def prefixEnd_7058564 : Nat := 4983230072969 + 3 ^ 40 * 7058564 * 2
def baseEnd_7058564 : Nat := 3624436062522626569588261

theorem tailTrace_7058564 : CollatzResearch.WordTrace tailWord_7058564 prefixEnd_7058564 3624436062522626569588261 := by
  unfold tailWord_7058564
  simp only [CollatzResearch.WordTrace]
  refine ⟨128723489600017804800507373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171631319466690406400676497 128723489600017804800507373)
  ·
    refine ⟨48271308600006676800190265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128723489600017804800507373 48271308600006676800190265)
    ·
      refine ⟨36203481450005007600142699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48271308600006676800190265 36203481450005007600142699)
      ·
        refine ⟨54305222175007511400214049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36203481450005007600142699 54305222175007511400214049)
        ·
          refine ⟨40728916631255633550160537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54305222175007511400214049 40728916631255633550160537)
          ·
            refine ⟨30546687473441725162620403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40728916631255633550160537 30546687473441725162620403)
            ·
              refine ⟨45820031210162587743930605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30546687473441725162620403 45820031210162587743930605)
              ·
                refine ⟨17182511703810970403973977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45820031210162587743930605 17182511703810970403973977)
                ·
                  refine ⟨12886883777858227802980483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17182511703810970403973977 12886883777858227802980483)
                  ·
                    refine ⟨19330325666787341704470725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12886883777858227802980483 19330325666787341704470725)
                    ·
                      refine ⟨3624436062522626569588261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19330325666787341704470725 3624436062522626569588261)
                      ·
                        rfl

theorem cell23_7058564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 3, 2, 1, 4].length) (baseStart_7058564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7058564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7058564 prefixEnd_7058564 := by exact prefixLift 7058564
  have htrace : WordTrace (prefixWord ++ tailWord_7058564) baseStart_7058564 baseEnd_7058564 := by
    simpa [prefixWord, tailWord_7058564, baseEnd_7058564] using wordTrace_append hprefix tailTrace_7058564
  have hstable : (prefixWord ++ tailWord_7058564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7058564).length < 2 ^ (prefixWord ++ tailWord_7058564).sum := by decide
  have hdescent : baseEnd_7058564 < baseStart_7058564 := by decide
  rcases family_descends (prefixWord ++ tailWord_7058564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7058625 : List Nat := [1, 2, 6, 1, 1, 2, 2, 3, 1, 4]
def baseStart_7058625 : Nat := 118140960795 + 7058625 * 2 ^ 59
def prefixEnd_7058625 : Nat := 4983230072969 + 3 ^ 40 * 7058625 * 2
def baseEnd_7058625 : Nat := 1208155794947516943641827

theorem tailTrace_7058625 : CollatzResearch.WordTrace tailWord_7058625 prefixEnd_7058625 1208155794947516943641827 := by
  unfold tailWord_7058625
  simp only [CollatzResearch.WordTrace]
  refine ⟨257449204052814617018985329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171632802701876411345990219 257449204052814617018985329)
  ·
    refine ⟨193086903039610962764238997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257449204052814617018985329 193086903039610962764238997)
    ·
      refine ⟨9050948579981763879573703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 193086903039610962764238997 9050948579981763879573703)
      ·
        refine ⟨13576422869972645819360555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9050948579981763879573703 13576422869972645819360555)
        ·
          refine ⟨20364634304958968729040833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13576422869972645819360555 20364634304958968729040833)
          ·
            refine ⟨15273475728719226546780625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20364634304958968729040833 15273475728719226546780625)
            ·
              refine ⟨11455106796539419910085469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15273475728719226546780625 11455106796539419910085469)
              ·
                refine ⟨4295665048702282466282051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11455106796539419910085469 4295665048702282466282051)
                ·
                  refine ⟨6443497573053423699423077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4295665048702282466282051 6443497573053423699423077)
                  ·
                    refine ⟨1208155794947516943641827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6443497573053423699423077 1208155794947516943641827)
                    ·
                      rfl

theorem cell23_7058625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 2, 3, 1, 4].length) (baseStart_7058625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7058625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7058625 prefixEnd_7058625 := by exact prefixLift 7058625
  have htrace : WordTrace (prefixWord ++ tailWord_7058625) baseStart_7058625 baseEnd_7058625 := by
    simpa [prefixWord, tailWord_7058625, baseEnd_7058625] using wordTrace_append hprefix tailTrace_7058625
  have hstable : (prefixWord ++ tailWord_7058625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7058625).length < 2 ^ (prefixWord ++ tailWord_7058625).sum := by decide
  have hdescent : baseEnd_7058625 < baseStart_7058625 := by decide
  rcases family_descends (prefixWord ++ tailWord_7058625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7058638 : List Nat := [4, 1, 1, 1, 6, 1, 1, 2, 6]
def baseStart_7058638 : Nat := 118140960795 + 7058638 * 2 ^ 59
def prefixEnd_7058638 : Nat := 4983230072969 + 3 ^ 40 * 7058638 * 2
def baseEnd_7058638 : Nat := 402719340010117697784769

theorem tailTrace_7058638 : CollatzResearch.WordTrace tailWord_7058638 prefixEnd_7058638 402719340010117697784769 := by
  unfold tailWord_7058638
  simp only [CollatzResearch.WordTrace]
  refine ⟨32181209775220940029901071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 171633118801178346826139045 32181209775220940029901071)
  ·
    refine ⟨48271814662831410044851607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32181209775220940029901071 48271814662831410044851607)
    ·
      refine ⟨72407721994247115067277411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48271814662831410044851607 72407721994247115067277411)
      ·
        refine ⟨108611582991370672600916117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72407721994247115067277411 108611582991370672600916117)
        ·
          refine ⟨5091167952720500278167943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 108611582991370672600916117 5091167952720500278167943)
          ·
            refine ⟨7636751929080750417251915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5091167952720500278167943 7636751929080750417251915)
            ·
              refine ⟨11455127893621125625877873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7636751929080750417251915 11455127893621125625877873)
              ·
                refine ⟨8591345920215844219408405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11455127893621125625877873 8591345920215844219408405)
                ·
                  refine ⟨402719340010117697784769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8591345920215844219408405 402719340010117697784769)
                  ·
                    rfl

theorem cell23_7058638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 1, 2, 6].length) (baseStart_7058638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7058638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7058638 prefixEnd_7058638 := by exact prefixLift 7058638
  have htrace : WordTrace (prefixWord ++ tailWord_7058638) baseStart_7058638 baseEnd_7058638 := by
    simpa [prefixWord, tailWord_7058638, baseEnd_7058638] using wordTrace_append hprefix tailTrace_7058638
  have hstable : (prefixWord ++ tailWord_7058638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7058638).length < 2 ^ (prefixWord ++ tailWord_7058638).sum := by decide
  have hdescent : baseEnd_7058638 < baseStart_7058638 := by decide
  rcases family_descends (prefixWord ++ tailWord_7058638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7058647 : List Nat := [1, 1, 3, 2, 1, 2, 2, 2, 3, 6]
def baseStart_7058647 : Nat := 118140960795 + 7058647 * 2 ^ 59
def prefixEnd_7058647 : Nat := 4983230072969 + 3 ^ 40 * 7058647 * 2
def baseEnd_7058647 : Nat := 1208159560472316581616793

theorem tailTrace_7058647 : CollatzResearch.WordTrace tailWord_7058647 prefixEnd_7058647 1208159560472316581616793 := by
  unfold tailWord_7058647
  simp only [CollatzResearch.WordTrace]
  refine ⟨257450006458734914776286195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171633337639156609850857463 257450006458734914776286195)
  ·
    refine ⟨386175009688102372164429293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257450006458734914776286195 386175009688102372164429293)
    ·
      refine ⟨144815628633038389561660985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 386175009688102372164429293 144815628633038389561660985)
      ·
        refine ⟨108611721474778792171245739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144815628633038389561660985 108611721474778792171245739)
        ·
          refine ⟨162917582212168188256868609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108611721474778792171245739 162917582212168188256868609)
          ·
            refine ⟨122188186659126141192651457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162917582212168188256868609 122188186659126141192651457)
            ·
              refine ⟨91641139994344605894488593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122188186659126141192651457 91641139994344605894488593)
              ·
                refine ⟨68730854995758454420866445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91641139994344605894488593 68730854995758454420866445)
                ·
                  refine ⟨25774070623409420407824917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68730854995758454420866445 25774070623409420407824917)
                  ·
                    refine ⟨1208159560472316581616793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25774070623409420407824917 1208159560472316581616793)
                    ·
                      rfl

theorem cell23_7058647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 2, 3, 6].length) (baseStart_7058647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7058647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7058647 prefixEnd_7058647 := by exact prefixLift 7058647
  have htrace : WordTrace (prefixWord ++ tailWord_7058647) baseStart_7058647 baseEnd_7058647 := by
    simpa [prefixWord, tailWord_7058647, baseEnd_7058647] using wordTrace_append hprefix tailTrace_7058647
  have hstable : (prefixWord ++ tailWord_7058647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7058647).length < 2 ^ (prefixWord ++ tailWord_7058647).sum := by decide
  have hdescent : baseEnd_7058647 < baseStart_7058647 := by decide
  rcases family_descends (prefixWord ++ tailWord_7058647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7058648 : List Nat := [2, 1, 2, 2, 5, 1, 2, 1, 3, 1, 3]
def baseStart_7058648 : Nat := 118140960795 + 7058648 * 2 ^ 59
def prefixEnd_7058648 : Nat := 4983230072969 + 3 ^ 40 * 7058648 * 2
def baseEnd_7058648 : Nat := 3624479194897604240937875

theorem tailTrace_7058648 : CollatzResearch.WordTrace tailWord_7058648 prefixEnd_7058648 3624479194897604240937875 := by
  unfold tailWord_7058648
  simp only [CollatzResearch.WordTrace]
  refine ⟨128725021465865645973536299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171633361954487527964715065 128725021465865645973536299)
  ·
    refine ⟨193087532198798468960304449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128725021465865645973536299 193087532198798468960304449)
    ·
      refine ⟨144815649149098851720228337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193087532198798468960304449 144815649149098851720228337)
      ·
        refine ⟨108611736861824138790171253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144815649149098851720228337 108611736861824138790171253)
        ·
          refine ⟨10182350330796013011578555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 108611736861824138790171253 10182350330796013011578555)
          ·
            refine ⟨15273525496194019517367833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10182350330796013011578555 15273525496194019517367833)
            ·
              refine ⟨11455144122145514638025875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15273525496194019517367833 11455144122145514638025875)
              ·
                refine ⟨17182716183218271957038813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11455144122145514638025875 17182716183218271957038813)
                ·
                  refine ⟨6443518568706851983889555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17182716183218271957038813 6443518568706851983889555)
                  ·
                    refine ⟨9665277853060277975834333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6443518568706851983889555 9665277853060277975834333)
                    ·
                      refine ⟨3624479194897604240937875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9665277853060277975834333 3624479194897604240937875)
                      ·
                        rfl

theorem cell23_7058648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 2, 1, 3, 1, 3].length) (baseStart_7058648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7058648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7058648 prefixEnd_7058648 := by exact prefixLift 7058648
  have htrace : WordTrace (prefixWord ++ tailWord_7058648) baseStart_7058648 baseEnd_7058648 := by
    simpa [prefixWord, tailWord_7058648, baseEnd_7058648] using wordTrace_append hprefix tailTrace_7058648
  have hstable : (prefixWord ++ tailWord_7058648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7058648).length < 2 ^ (prefixWord ++ tailWord_7058648).sum := by decide
  have hdescent : baseEnd_7058648 < baseStart_7058648 := by decide
  rcases family_descends (prefixWord ++ tailWord_7058648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7058676 : List Nat := [2, 6, 1, 2, 2, 1, 1, 3, 1, 4]
def baseStart_7058676 : Nat := 118140960795 + 7058676 * 2 ^ 59
def prefixEnd_7058676 : Nat := 4983230072969 + 3 ^ 40 * 7058676 * 2
def baseEnd_7058676 : Nat := 1208164524118643377129249

theorem tailTrace_7058676 : CollatzResearch.WordTrace tailWord_7058676 prefixEnd_7058676 1208164524118643377129249 := by
  unfold tailWord_7058676
  simp only [CollatzResearch.WordTrace]
  refine ⟨128725532087814926364545941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171634042783753235152727921 128725532087814926364545941)
  ·
    refine ⟨6034009316616324673338091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 128725532087814926364545941 6034009316616324673338091)
    ·
      refine ⟨9051013974924487010007137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6034009316616324673338091 9051013974924487010007137)
      ·
        refine ⟨6788260481193365257505353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9051013974924487010007137 6788260481193365257505353)
        ·
          refine ⟨5091195360895023943129015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6788260481193365257505353 5091195360895023943129015)
          ·
            refine ⟨7636793041342535914693523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5091195360895023943129015 7636793041342535914693523)
            ·
              refine ⟨11455189562013803872040285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7636793041342535914693523 11455189562013803872040285)
              ·
                refine ⟨4295696085755176452015107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11455189562013803872040285 4295696085755176452015107)
                ·
                  refine ⟨6443544128632764678022661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4295696085755176452015107 6443544128632764678022661)
                  ·
                    refine ⟨1208164524118643377129249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6443544128632764678022661 1208164524118643377129249)
                    ·
                      rfl

theorem cell23_7058676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 1, 3, 1, 4].length) (baseStart_7058676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7058676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7058676 prefixEnd_7058676 := by exact prefixLift 7058676
  have htrace : WordTrace (prefixWord ++ tailWord_7058676) baseStart_7058676 baseEnd_7058676 := by
    simpa [prefixWord, tailWord_7058676, baseEnd_7058676] using wordTrace_append hprefix tailTrace_7058676
  have hstable : (prefixWord ++ tailWord_7058676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7058676).length < 2 ^ (prefixWord ++ tailWord_7058676).sum := by decide
  have hdescent : baseEnd_7058676 < baseStart_7058676 := by decide
  rcases family_descends (prefixWord ++ tailWord_7058676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7058691 : List Nat := [1, 1, 1, 3, 2, 4, 2, 3, 1, 2, 3]
def baseStart_7058691 : Nat := 118140960795 + 7058691 * 2 ^ 59
def prefixEnd_7058691 : Nat := 4983230072969 + 3 ^ 40 * 7058691 * 2
def baseEnd_7058691 : Nat := 3624501274565747572700177

theorem tailTrace_7058691 : CollatzResearch.WordTrace tailWord_7058691 prefixEnd_7058691 3624501274565747572700177 := by
  unfold tailWord_7058691
  simp only [CollatzResearch.WordTrace]
  refine ⟨257451611270575510290887927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171634407513717006860591951 257451611270575510290887927)
  ·
    refine ⟨386177416905863265436331891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257451611270575510290887927 386177416905863265436331891)
    ·
      refine ⟨579266125358794898154497837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 386177416905863265436331891 579266125358794898154497837)
      ·
        refine ⟨217224797009548086807936689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 579266125358794898154497837 217224797009548086807936689)
        ·
          refine ⟨162918597757161065105952517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 217224797009548086807936689 162918597757161065105952517)
          ·
            refine ⟨30547237079467699707366097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 162918597757161065105952517 30547237079467699707366097)
            ·
              refine ⟨22910427809600774780524573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30547237079467699707366097 22910427809600774780524573)
              ·
                refine ⟨8591410428600290542696715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22910427809600774780524573 8591410428600290542696715)
                ·
                  refine ⟨12887115642900435814045073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8591410428600290542696715 12887115642900435814045073)
                  ·
                    refine ⟨9665336732175326860533805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12887115642900435814045073 9665336732175326860533805)
                    ·
                      refine ⟨3624501274565747572700177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9665336732175326860533805 3624501274565747572700177)
                      ·
                        rfl

theorem cell23_7058691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 3, 1, 2, 3].length) (baseStart_7058691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7058691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7058691 prefixEnd_7058691 := by exact prefixLift 7058691
  have htrace : WordTrace (prefixWord ++ tailWord_7058691) baseStart_7058691 baseEnd_7058691 := by
    simpa [prefixWord, tailWord_7058691, baseEnd_7058691] using wordTrace_append hprefix tailTrace_7058691
  have hstable : (prefixWord ++ tailWord_7058691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7058691).length < 2 ^ (prefixWord ++ tailWord_7058691).sum := by decide
  have hdescent : baseEnd_7058691 < baseStart_7058691 := by decide
  rcases family_descends (prefixWord ++ tailWord_7058691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7058742 : List Nat := [5, 1, 2, 3, 2, 1, 1, 1, 1, 1, 5]
def baseStart_7058742 : Nat := 118140960795 + 7058742 * 2 ^ 59
def prefixEnd_7058742 : Nat := 4983230072969 + 3 ^ 40 * 7058742 * 2
def baseEnd_7058742 : Nat := 3624527462079126873162443

theorem tailTrace_7058742 : CollatzResearch.WordTrace tailWord_7058742 prefixEnd_7058742 3624527462079126873162443 := by
  unfold tailWord_7058742
  simp only [CollatzResearch.WordTrace]
  refine ⟨16090841962086921625062155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 171635647595593830667329653 16090841962086921625062155)
  ·
    refine ⟨24136262943130382437593233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16090841962086921625062155 24136262943130382437593233)
    ·
      refine ⟨18102197207347786828194925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24136262943130382437593233 18102197207347786828194925)
      ·
        refine ⟨6788323952755420060573097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18102197207347786828194925 6788323952755420060573097)
        ·
          refine ⟨5091242964566565045429823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6788323952755420060573097 5091242964566565045429823)
          ·
            refine ⟨7636864446849847568144735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5091242964566565045429823 7636864446849847568144735)
            ·
              refine ⟨11455296670274771352217103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7636864446849847568144735 11455296670274771352217103)
              ·
                refine ⟨17182945005412157028325655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11455296670274771352217103 17182945005412157028325655)
                ·
                  refine ⟨25774417508118235542488483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17182945005412157028325655 25774417508118235542488483)
                  ·
                    refine ⟨38661626262177353313732725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25774417508118235542488483 38661626262177353313732725)
                    ·
                      refine ⟨3624527462079126873162443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38661626262177353313732725 3624527462079126873162443)
                      ·
                        rfl

theorem cell23_7058742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 1, 1, 1, 1, 5].length) (baseStart_7058742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7058742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7058742 prefixEnd_7058742 := by exact prefixLift 7058742
  have htrace : WordTrace (prefixWord ++ tailWord_7058742) baseStart_7058742 baseEnd_7058742 := by
    simpa [prefixWord, tailWord_7058742, baseEnd_7058742] using wordTrace_append hprefix tailTrace_7058742
  have hstable : (prefixWord ++ tailWord_7058742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7058742).length < 2 ^ (prefixWord ++ tailWord_7058742).sum := by decide
  have hdescent : baseEnd_7058742 < baseStart_7058742 := by decide
  rcases family_descends (prefixWord ++ tailWord_7058742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7058756 : List Nat := [2, 3, 4, 1, 1, 3, 2, 2, 1, 2, 2]
def baseStart_7058756 : Nat := 118140960795 + 7058756 * 2 ^ 59
def prefixEnd_7058756 : Nat := 4983230072969 + 3 ^ 40 * 7058756 * 2
def baseEnd_7058756 : Nat := 3624534650808289818387379

theorem tailTrace_7058756 : CollatzResearch.WordTrace tailWord_7058756 prefixEnd_7058756 3624534650808289818387379 := by
  unfold tailWord_7058756
  simp only [CollatzResearch.WordTrace]
  refine ⟨128726991007670013196002061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171635988010226684261336081 128726991007670013196002061)
  ·
    refine ⟨48272621627876254948500773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128726991007670013196002061 48272621627876254948500773)
    ·
      refine ⟨9051116555226797802843895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48272621627876254948500773 9051116555226797802843895)
      ·
        refine ⟨13576674832840196704265843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9051116555226797802843895 13576674832840196704265843)
        ·
          refine ⟨20365012249260295056398765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13576674832840196704265843 20365012249260295056398765)
          ·
            refine ⟨7636879593472610646149537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20365012249260295056398765 7636879593472610646149537)
            ·
              refine ⟨5727659695104457984612153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7636879593472610646149537 5727659695104457984612153)
              ·
                refine ⟨4295744771328343488459115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5727659695104457984612153 4295744771328343488459115)
                ·
                  refine ⟨6443617156992515232688673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4295744771328343488459115 6443617156992515232688673)
                  ·
                    refine ⟨4832712867744386424516505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6443617156992515232688673 4832712867744386424516505)
                    ·
                      refine ⟨3624534650808289818387379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4832712867744386424516505 3624534650808289818387379)
                      ·
                        rfl

theorem cell23_7058756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 2, 2, 1, 2, 2].length) (baseStart_7058756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7058756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7058756 prefixEnd_7058756 := by exact prefixLift 7058756
  have htrace : WordTrace (prefixWord ++ tailWord_7058756) baseStart_7058756 baseEnd_7058756 := by
    simpa [prefixWord, tailWord_7058756, baseEnd_7058756] using wordTrace_append hprefix tailTrace_7058756
  have hstable : (prefixWord ++ tailWord_7058756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7058756).length < 2 ^ (prefixWord ++ tailWord_7058756).sum := by decide
  have hdescent : baseEnd_7058756 < baseStart_7058756 := by decide
  rcases family_descends (prefixWord ++ tailWord_7058756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7058784 : List Nat := [2, 1, 1, 3, 4, 1, 1, 1, 9]
def baseStart_7058784 : Nat := 118140960795 + 7058784 * 2 ^ 59
def prefixEnd_7058784 : Nat := 4983230072969 + 3 ^ 40 * 7058784 * 2
def baseEnd_7058784 : Nat := 402727669807401745426361

theorem tailTrace_7058784 : CollatzResearch.WordTrace tailWord_7058784 prefixEnd_7058784 402727669807401745426361 := by
  unfold tailWord_7058784
  simp only [CollatzResearch.WordTrace]
  refine ⟨128727501629619293587011703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171636668839492391449348937 128727501629619293587011703)
  ·
    refine ⟨193091252444428940380517555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128727501629619293587011703 193091252444428940380517555)
    ·
      refine ⟨289636878666643410570776333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193091252444428940380517555 289636878666643410570776333)
      ·
        refine ⟨108613829499991278964041125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 289636878666643410570776333 108613829499991278964041125)
        ·
          refine ⟨20365093031248364805757711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 108613829499991278964041125 20365093031248364805757711)
          ·
            refine ⟨30547639546872547208636567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20365093031248364805757711 30547639546872547208636567)
            ·
              refine ⟨45821459320308820812954851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30547639546872547208636567 45821459320308820812954851)
              ·
                refine ⟨68732188980463231219432277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45821459320308820812954851 68732188980463231219432277)
                ·
                  refine ⟨402727669807401745426361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 68732188980463231219432277 402727669807401745426361)
                  ·
                    rfl

theorem cell23_7058784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 1, 9].length) (baseStart_7058784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7058784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7058784 prefixEnd_7058784 := by exact prefixLift 7058784
  have htrace : WordTrace (prefixWord ++ tailWord_7058784) baseStart_7058784 baseEnd_7058784 := by
    simpa [prefixWord, tailWord_7058784, baseEnd_7058784] using wordTrace_append hprefix tailTrace_7058784
  have hstable : (prefixWord ++ tailWord_7058784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7058784).length < 2 ^ (prefixWord ++ tailWord_7058784).sum := by decide
  have hdescent : baseEnd_7058784 < baseStart_7058784 := by decide
  rcases family_descends (prefixWord ++ tailWord_7058784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7058801 : List Nat := [1, 2, 2, 2, 1, 2, 3, 5, 5]
def baseStart_7058801 : Nat := 118140960795 + 7058801 * 2 ^ 59
def prefixEnd_7058801 : Nat := 4983230072969 + 3 ^ 40 * 7058801 * 2
def baseEnd_7058801 : Nat := 402728639715304682480519

theorem tailTrace_7058801 : CollatzResearch.WordTrace tailWord_7058801 prefixEnd_7058801 402728639715304682480519 := by
  unfold tailWord_7058801
  simp only [CollatzResearch.WordTrace]
  refine ⟨257455623300176999077392257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171637082200117999384928171 257455623300176999077392257)
  ·
    refine ⟨193091717475132749308044193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257455623300176999077392257 193091717475132749308044193)
    ·
      refine ⟨144818788106349561981033145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193091717475132749308044193 144818788106349561981033145)
      ·
        refine ⟨108614091079762171485774859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144818788106349561981033145 108614091079762171485774859)
        ·
          refine ⟨162921136619643257228662289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108614091079762171485774859 162921136619643257228662289)
          ·
            refine ⟨122190852464732442921496717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162921136619643257228662289 122190852464732442921496717)
            ·
              refine ⟨45821569674274666095561269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 122190852464732442921496717 45821569674274666095561269)
              ·
                refine ⟨4295772156963249946458869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45821569674274666095561269 4295772156963249946458869)
                ·
                  refine ⟨402728639715304682480519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4295772156963249946458869 402728639715304682480519)
                  ·
                    rfl

theorem cell23_7058801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 5, 5].length) (baseStart_7058801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7058801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7058801 prefixEnd_7058801 := by exact prefixLift 7058801
  have htrace : WordTrace (prefixWord ++ tailWord_7058801) baseStart_7058801 baseEnd_7058801 := by
    simpa [prefixWord, tailWord_7058801, baseEnd_7058801] using wordTrace_append hprefix tailTrace_7058801
  have hstable : (prefixWord ++ tailWord_7058801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7058801).length < 2 ^ (prefixWord ++ tailWord_7058801).sum := by decide
  have hdescent : baseEnd_7058801 < baseStart_7058801 := by decide
  rcases family_descends (prefixWord ++ tailWord_7058801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7058818 : List Nat := [3, 4, 2, 1, 1, 1, 1, 3, 7]
def baseStart_7058818 : Nat := 118140960795 + 7058818 * 2 ^ 59
def prefixEnd_7058818 : Nat := 4983230072969 + 3 ^ 40 * 7058818 * 2
def baseEnd_7058818 : Nat := 402729609623207619534677

theorem tailTrace_7058818 : CollatzResearch.WordTrace tailWord_7058818 prefixEnd_7058818 402729609623207619534677 := by
  unfold tailWord_7058818
  simp only [CollatzResearch.WordTrace]
  refine ⟨64364060835278852745190277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171637495560743607320507405 64364060835278852745190277)
  ·
    refine ⟨12068261406614784889723177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64364060835278852745190277 12068261406614784889723177)
    ·
      refine ⟨9051196054961088667292383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12068261406614784889723177 9051196054961088667292383)
      ·
        refine ⟨13576794082441633000938575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9051196054961088667292383 13576794082441633000938575)
        ·
          refine ⟨20365191123662449501407863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13576794082441633000938575 20365191123662449501407863)
          ·
            refine ⟨30547786685493674252111795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20365191123662449501407863 30547786685493674252111795)
            ·
              refine ⟨45821680028240511378167693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30547786685493674252111795 45821680028240511378167693)
              ·
                refine ⟨17183130010590191766812885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45821680028240511378167693 17183130010590191766812885)
                ·
                  refine ⟨402729609623207619534677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17183130010590191766812885 402729609623207619534677)
                  ·
                    rfl

theorem cell23_7058818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 3, 7].length) (baseStart_7058818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7058818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7058818 prefixEnd_7058818 := by exact prefixLift 7058818
  have htrace : WordTrace (prefixWord ++ tailWord_7058818) baseStart_7058818 baseEnd_7058818 := by
    simpa [prefixWord, tailWord_7058818, baseEnd_7058818] using wordTrace_append hprefix tailTrace_7058818
  have hstable : (prefixWord ++ tailWord_7058818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7058818).length < 2 ^ (prefixWord ++ tailWord_7058818).sum := by decide
  have hdescent : baseEnd_7058818 < baseStart_7058818 := by decide
  rcases family_descends (prefixWord ++ tailWord_7058818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7058821 : List Nat := [1, 3, 1, 1, 3, 1, 2, 1, 1, 7, 2]
def baseStart_7058821 : Nat := 118140960795 + 7058821 * 2 ^ 59
def prefixEnd_7058821 : Nat := 4983230072969 + 3 ^ 40 * 7058821 * 2
def baseEnd_7058821 : Nat := 3624568027050832064074579

theorem tailTrace_7058821 : CollatzResearch.WordTrace tailWord_7058821 prefixEnd_7058821 3624568027050832064074579 := by
  unfold tailWord_7058821
  simp only [CollatzResearch.WordTrace]
  refine ⟨257456352760104542493120317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171637568506736361662080211 257456352760104542493120317)
  ·
    refine ⟨96546132285039203434920119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 257456352760104542493120317 96546132285039203434920119)
    ·
      refine ⟨144819198427558805152380179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96546132285039203434920119 144819198427558805152380179)
      ·
        refine ⟨217228797641338207728570269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144819198427558805152380179 217228797641338207728570269)
        ·
          refine ⟨81460799115501827898213851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 217228797641338207728570269 81460799115501827898213851)
          ·
            refine ⟨122191198673252741847320777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81460799115501827898213851 122191198673252741847320777)
            ·
              refine ⟨91643399004939556385490583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122191198673252741847320777 91643399004939556385490583)
              ·
                refine ⟨137465098507409334578235875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91643399004939556385490583 137465098507409334578235875)
                ·
                  refine ⟨206197647761114001867353813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 137465098507409334578235875 206197647761114001867353813)
                  ·
                    refine ⟨4832757369401109418766105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 206197647761114001867353813 4832757369401109418766105)
                    ·
                      refine ⟨3624568027050832064074579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4832757369401109418766105 3624568027050832064074579)
                      ·
                        rfl

theorem cell23_7058821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 1, 1, 7, 2].length) (baseStart_7058821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7058821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7058821 prefixEnd_7058821 := by exact prefixLift 7058821
  have htrace : WordTrace (prefixWord ++ tailWord_7058821) baseStart_7058821 baseEnd_7058821 := by
    simpa [prefixWord, tailWord_7058821, baseEnd_7058821] using wordTrace_append hprefix tailTrace_7058821
  have hstable : (prefixWord ++ tailWord_7058821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7058821).length < 2 ^ (prefixWord ++ tailWord_7058821).sum := by decide
  have hdescent : baseEnd_7058821 < baseStart_7058821 := by decide
  rcases family_descends (prefixWord ++ tailWord_7058821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7058851 : List Nat := [1, 1, 1, 4, 1, 3, 2, 3, 2, 1, 4]
def baseStart_7058851 : Nat := 118140960795 + 7058851 * 2 ^ 59
def prefixEnd_7058851 : Nat := 4983230072969 + 3 ^ 40 * 7058851 * 2
def baseEnd_7058851 : Nat := 3624583431470466946699441

theorem tailTrace_7058851 : CollatzResearch.WordTrace tailWord_7058851 prefixEnd_7058851 3624583431470466946699441 := by
  unfold tailWord_7058851
  simp only [CollatzResearch.WordTrace]
  refine ⟨257457446949995857616712407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171638297966663905077808271 257457446949995857616712407)
  ·
    refine ⟨386186170424993786425068611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257457446949995857616712407 386186170424993786425068611)
    ·
      refine ⟨579279255637490679637602917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 386186170424993786425068611 579279255637490679637602917)
      ·
        refine ⟨108614860432029502432050547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 579279255637490679637602917 108614860432029502432050547)
        ·
          refine ⟨162922290648044253648075821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108614860432029502432050547 162922290648044253648075821)
          ·
            refine ⟨61095858993016595118028433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 162922290648044253648075821 61095858993016595118028433)
            ·
              refine ⟨45821894244762446338521325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61095858993016595118028433 45821894244762446338521325)
              ·
                refine ⟨17183210341785917376945497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45821894244762446338521325 17183210341785917376945497)
                ·
                  refine ⟨12887407756339438032709123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17183210341785917376945497 12887407756339438032709123)
                  ·
                    refine ⟨19331111634509157049063685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12887407756339438032709123 19331111634509157049063685)
                    ·
                      refine ⟨3624583431470466946699441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19331111634509157049063685 3624583431470466946699441)
                      ·
                        rfl

theorem cell23_7058851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 3, 2, 1, 4].length) (baseStart_7058851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7058851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7058851 prefixEnd_7058851 := by exact prefixLift 7058851
  have htrace : WordTrace (prefixWord ++ tailWord_7058851) baseStart_7058851 baseEnd_7058851 := by
    simpa [prefixWord, tailWord_7058851, baseEnd_7058851] using wordTrace_append hprefix tailTrace_7058851
  have hstable : (prefixWord ++ tailWord_7058851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7058851).length < 2 ^ (prefixWord ++ tailWord_7058851).sum := by decide
  have hdescent : baseEnd_7058851 < baseStart_7058851 := by decide
  rcases family_descends (prefixWord ++ tailWord_7058851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7058864 : List Nat := [2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 6]
def baseStart_7058864 : Nat := 118140960795 + 7058864 * 2 ^ 59
def prefixEnd_7058864 : Nat := 4983230072969 + 3 ^ 40 * 7058864 * 2
def baseEnd_7058864 : Nat := 3624590106718975395836881

theorem tailTrace_7058864 : CollatzResearch.WordTrace tailWord_7058864 prefixEnd_7058864 3624590106718975395836881 := by
  unfold tailWord_7058864
  simp only [CollatzResearch.WordTrace]
  refine ⟨128728960549474380418467823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171638614065965840557957097 128728960549474380418467823)
  ·
    refine ⟨193093440824211570627701735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128728960549474380418467823 193093440824211570627701735)
    ·
      refine ⟨289640161236317355941552603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193093440824211570627701735 289640161236317355941552603)
      ·
        refine ⟨434460241854476033912328905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 289640161236317355941552603 434460241854476033912328905)
        ·
          refine ⟨325845181390857025434246679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 434460241854476033912328905 325845181390857025434246679)
          ·
            refine ⟨488767772086285538151370019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 325845181390857025434246679 488767772086285538151370019)
            ·
              refine ⟨733151658129428307227055029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 488767772086285538151370019 733151658129428307227055029)
              ·
                refine ⟨68732967949633903802536409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 733151658129428307227055029 68732967949633903802536409)
                ·
                  refine ⟨51549725962225427851902307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68732967949633903802536409 51549725962225427851902307)
                  ·
                    refine ⟨77324588943338141777853461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51549725962225427851902307 77324588943338141777853461)
                    ·
                      refine ⟨3624590106718975395836881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 77324588943338141777853461 3624590106718975395836881)
                      ·
                        rfl

theorem cell23_7058864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 6].length) (baseStart_7058864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7058864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7058864 prefixEnd_7058864 := by exact prefixLift 7058864
  have htrace : WordTrace (prefixWord ++ tailWord_7058864) baseStart_7058864 baseEnd_7058864 := by
    simpa [prefixWord, tailWord_7058864, baseEnd_7058864] using wordTrace_append hprefix tailTrace_7058864
  have hstable : (prefixWord ++ tailWord_7058864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7058864).length < 2 ^ (prefixWord ++ tailWord_7058864).sum := by decide
  have hdescent : baseEnd_7058864 < baseStart_7058864 := by decide
  rcases family_descends (prefixWord ++ tailWord_7058864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7058925 : List Nat := [1, 5, 1, 3, 2, 1, 2, 2, 6]
def baseStart_7058925 : Nat := 118140960795 + 7058925 * 2 ^ 59
def prefixEnd_7058925 : Nat := 4983230072969 + 3 ^ 40 * 7058925 * 2
def baseEnd_7058925 : Nat := 402735714337655517463789

theorem tailTrace_7058925 : CollatzResearch.WordTrace tailWord_7058925 prefixEnd_7058925 402735714337655517463789 := by
  unfold tailWord_7058925
  simp only [CollatzResearch.WordTrace]
  refine ⟨257460145951727768254906229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171640097301151845503270819 257460145951727768254906229)
  ·
    refine ⟨24136888682974478273897459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 257460145951727768254906229 24136888682974478273897459)
    ·
      refine ⟨36205333024461717410846189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24136888682974478273897459 36205333024461717410846189)
      ·
        refine ⟨13576999884173144029067321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36205333024461717410846189 13576999884173144029067321)
        ·
          refine ⟨10182749913129858021800491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13576999884173144029067321 10182749913129858021800491)
          ·
            refine ⟨15274124869694787032700737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10182749913129858021800491 15274124869694787032700737)
            ·
              refine ⟨11455593652271090274525553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15274124869694787032700737 11455593652271090274525553)
              ·
                refine ⟨8591695239203317705894165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11455593652271090274525553 8591695239203317705894165)
                ·
                  refine ⟨402735714337655517463789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8591695239203317705894165 402735714337655517463789)
                  ·
                    rfl

theorem cell23_7058925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 2, 2, 6].length) (baseStart_7058925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7058925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7058925 prefixEnd_7058925 := by exact prefixLift 7058925
  have htrace : WordTrace (prefixWord ++ tailWord_7058925) baseStart_7058925 baseEnd_7058925 := by
    simpa [prefixWord, tailWord_7058925, baseEnd_7058925] using wordTrace_append hprefix tailTrace_7058925
  have hstable : (prefixWord ++ tailWord_7058925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7058925).length < 2 ^ (prefixWord ++ tailWord_7058925).sum := by decide
  have hdescent : baseEnd_7058925 < baseStart_7058925 := by decide
  rcases family_descends (prefixWord ++ tailWord_7058925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7058975 : List Nat := [1, 1, 2, 4, 1, 1, 6, 1, 1, 1, 4]
def baseStart_7058975 : Nat := 118140960795 + 7058975 * 2 ^ 59
def prefixEnd_7058975 : Nat := 4983230072969 + 3 ^ 40 * 7058975 * 2
def baseEnd_7058975 : Nat := 3624647103071624461548871

theorem tailTrace_7058975 : CollatzResearch.WordTrace tailWord_7058975 prefixEnd_7058975 3624647103071624461548871 := by
  unfold tailWord_7058975
  simp only [CollatzResearch.WordTrace]
  refine ⟨257461969601546626794226379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171641313067697751196150919 257461969601546626794226379)
  ·
    refine ⟨386192954402319940191339569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257461969601546626794226379 386192954402319940191339569)
    ·
      refine ⟨289644715801739955143504677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 386192954402319940191339569 289644715801739955143504677)
      ·
        refine ⟨54308384212826241589407127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 289644715801739955143504677 54308384212826241589407127)
        ·
          refine ⟨81462576319239362384110691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54308384212826241589407127 81462576319239362384110691)
          ·
            refine ⟨122193864478859043576166037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81462576319239362384110691 122193864478859043576166037)
            ·
              refine ⟨5727837397446517667632783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 122193864478859043576166037 5727837397446517667632783)
              ·
                refine ⟨8591756096169776501449175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5727837397446517667632783 8591756096169776501449175)
                ·
                  refine ⟨12887634144254664752173763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8591756096169776501449175 12887634144254664752173763)
                  ·
                    refine ⟨19331451216381997128260645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12887634144254664752173763 19331451216381997128260645)
                    ·
                      refine ⟨3624647103071624461548871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19331451216381997128260645 3624647103071624461548871)
                      ·
                        rfl

theorem cell23_7058975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 6, 1, 1, 1, 4].length) (baseStart_7058975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7058975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7058975 prefixEnd_7058975 := by exact prefixLift 7058975
  have htrace : WordTrace (prefixWord ++ tailWord_7058975) baseStart_7058975 baseEnd_7058975 := by
    simpa [prefixWord, tailWord_7058975, baseEnd_7058975] using wordTrace_append hprefix tailTrace_7058975
  have hstable : (prefixWord ++ tailWord_7058975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7058975).length < 2 ^ (prefixWord ++ tailWord_7058975).sum := by decide
  have hdescent : baseEnd_7058975 < baseStart_7058975 := by decide
  rcases family_descends (prefixWord ++ tailWord_7058975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7058991 : List Nat := [1, 1, 2, 1, 2, 1, 1, 1, 1, 9, 3]
def baseStart_7058991 : Nat := 118140960795 + 7058991 * 2 ^ 59
def prefixEnd_7058991 : Nat := 4983230072969 + 3 ^ 40 * 7058991 * 2
def baseEnd_7058991 : Nat := 3624655318762096398948797

theorem tailTrace_7058991 : CollatzResearch.WordTrace tailWord_7058991 prefixEnd_7058991 3624655318762096398948797 := by
  unfold tailWord_7058991
  simp only [CollatzResearch.WordTrace]
  refine ⟨257462553169488661526808827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171641702112992441017872551 257462553169488661526808827)
  ·
    refine ⟨386193829754232992290213241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257462553169488661526808827 386193829754232992290213241)
    ·
      refine ⟨289645372315674744217659931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 386193829754232992290213241 289645372315674744217659931)
      ·
        refine ⟨434468058473512116326489897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 289645372315674744217659931 434468058473512116326489897)
        ·
          refine ⟨325851043855134087244867423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 434468058473512116326489897 325851043855134087244867423)
          ·
            refine ⟨488776565782701130867301135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 325851043855134087244867423 488776565782701130867301135)
            ·
              refine ⟨733164848674051696300951703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 488776565782701130867301135 733164848674051696300951703)
              ·
                refine ⟨1099747273011077544451427555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 733164848674051696300951703 1099747273011077544451427555)
                ·
                  refine ⟨1649620909516616316677141333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1099747273011077544451427555 1649620909516616316677141333)
                  ·
                    refine ⟨9665747516698923730530125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 1649620909516616316677141333 9665747516698923730530125)
                    ·
                      refine ⟨3624655318762096398948797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9665747516698923730530125 3624655318762096398948797)
                      ·
                        rfl

theorem cell23_7058991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 9, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 9, 3].length) (baseStart_7058991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7058991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7058991 prefixEnd_7058991 := by exact prefixLift 7058991
  have htrace : WordTrace (prefixWord ++ tailWord_7058991) baseStart_7058991 baseEnd_7058991 := by
    simpa [prefixWord, tailWord_7058991, baseEnd_7058991] using wordTrace_append hprefix tailTrace_7058991
  have hstable : (prefixWord ++ tailWord_7058991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7058991).length < 2 ^ (prefixWord ++ tailWord_7058991).sum := by decide
  have hdescent : baseEnd_7058991 < baseStart_7058991 := by decide
  rcases family_descends (prefixWord ++ tailWord_7058991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7059015 : List Nat := [1, 1, 4, 1, 5, 2, 2, 7]
def baseStart_7059015 : Nat := 118140960795 + 7059015 * 2 ^ 59
def prefixEnd_7059015 : Nat := 4983230072969 + 3 ^ 40 * 7059015 * 2
def baseEnd_7059015 : Nat := 134246949714733492779581

theorem tailTrace_7059015 : CollatzResearch.WordTrace tailWord_7059015 prefixEnd_7059015 134246949714733492779581 := by
  unfold tailWord_7059015
  simp only [CollatzResearch.WordTrace]
  refine ⟨257463428521401713625682499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171642285680934475750454999 257463428521401713625682499)
  ·
    refine ⟨386195142782102570438523749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257463428521401713625682499 386195142782102570438523749)
    ·
      refine ⟨72411589271644231957223203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 386195142782102570438523749 72411589271644231957223203)
      ·
        refine ⟨108617383907466347935834805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72411589271644231957223203 108617383907466347935834805)
        ·
          refine ⟨10182879741324970118984513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 108617383907466347935834805 10182879741324970118984513)
          ·
            refine ⟨7637159805993727589238385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10182879741324970118984513 7637159805993727589238385)
            ·
              refine ⟨5727869854495295691928789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7637159805993727589238385 5727869854495295691928789)
              ·
                refine ⟨134246949714733492779581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5727869854495295691928789 134246949714733492779581)
                ·
                  rfl

theorem cell23_7059015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 2, 7].length) (baseStart_7059015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7059015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7059015 prefixEnd_7059015 := by exact prefixLift 7059015
  have htrace : WordTrace (prefixWord ++ tailWord_7059015) baseStart_7059015 baseEnd_7059015 := by
    simpa [prefixWord, tailWord_7059015, baseEnd_7059015] using wordTrace_append hprefix tailTrace_7059015
  have hstable : (prefixWord ++ tailWord_7059015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7059015).length < 2 ^ (prefixWord ++ tailWord_7059015).sum := by decide
  have hdescent : baseEnd_7059015 < baseStart_7059015 := by decide
  rcases family_descends (prefixWord ++ tailWord_7059015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7059026 : List Nat := [3, 2, 2, 1, 2, 4, 1, 3, 1, 2, 2]
def baseStart_7059026 : Nat := 118140960795 + 7059026 * 2 ^ 59
def prefixEnd_7059026 : Nat := 4983230072969 + 3 ^ 40 * 7059026 * 2
def baseEnd_7059026 : Nat := 3624673290585003762011137

theorem tailTrace_7059026 : CollatzResearch.WordTrace tailWord_7059026 prefixEnd_7059026 3624673290585003762011137 := by
  unfold tailWord_7059026
  simp only [CollatzResearch.WordTrace]
  refine ⟨64365957431090465626083233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171642553149574575002888621 64365957431090465626083233)
  ·
    refine ⟨48274468073317849219562425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64365957431090465626083233 48274468073317849219562425)
    ·
      refine ⟨36205851054988386914671819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48274468073317849219562425 36205851054988386914671819)
      ·
        refine ⟨54308776582482580372007729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36205851054988386914671819 54308776582482580372007729)
        ·
          refine ⟨40731582436861935279005797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54308776582482580372007729 40731582436861935279005797)
          ·
            refine ⟨7637171706911612864813587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40731582436861935279005797 7637171706911612864813587)
            ·
              refine ⟨11455757560367419297220381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7637171706911612864813587 11455757560367419297220381)
              ·
                refine ⟨4295909085137782236457643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11455757560367419297220381 4295909085137782236457643)
                ·
                  refine ⟨6443863627706673354686465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4295909085137782236457643 6443863627706673354686465)
                  ·
                    refine ⟨4832897720780005016014849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6443863627706673354686465 4832897720780005016014849)
                    ·
                      refine ⟨3624673290585003762011137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4832897720780005016014849 3624673290585003762011137)
                      ·
                        rfl

theorem cell23_7059026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 1, 3, 1, 2, 2].length) (baseStart_7059026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7059026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7059026 prefixEnd_7059026 := by exact prefixLift 7059026
  have htrace : WordTrace (prefixWord ++ tailWord_7059026) baseStart_7059026 baseEnd_7059026 := by
    simpa [prefixWord, tailWord_7059026, baseEnd_7059026] using wordTrace_append hprefix tailTrace_7059026
  have hstable : (prefixWord ++ tailWord_7059026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7059026).length < 2 ^ (prefixWord ++ tailWord_7059026).sum := by decide
  have hdescent : baseEnd_7059026 < baseStart_7059026 := by decide
  rcases family_descends (prefixWord ++ tailWord_7059026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7059065 : List Nat := [1, 2, 1, 3, 3, 1, 2, 3, 1, 4, 2]
def baseStart_7059065 : Nat := 118140960795 + 7059065 * 2 ^ 59
def prefixEnd_7059065 : Nat := 4983230072969 + 3 ^ 40 * 7059065 * 2
def baseEnd_7059065 : Nat := 3624693316330529109423457

theorem tailTrace_7059065 : CollatzResearch.WordTrace tailWord_7059065 prefixEnd_7059065 3624693316330529109423457 := by
  unfold tailWord_7059065
  simp only [CollatzResearch.WordTrace]
  refine ⟨257465252171220572165002649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171643501447480381443335099 257465252171220572165002649)
  ·
    refine ⟨193098939128415429123751987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257465252171220572165002649 193098939128415429123751987)
    ·
      refine ⟨289648408692623143685627981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193098939128415429123751987 289648408692623143685627981)
      ·
        refine ⟨108618153259733678882110493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 289648408692623143685627981 108618153259733678882110493)
        ·
          refine ⟨40731807472400129580791435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108618153259733678882110493 40731807472400129580791435)
          ·
            refine ⟨61097711208600194371187153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40731807472400129580791435 61097711208600194371187153)
            ·
              refine ⟨45823283406450145778390365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61097711208600194371187153 45823283406450145778390365)
              ·
                refine ⟨17183731277418804666896387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45823283406450145778390365 17183731277418804666896387)
                ·
                  refine ⟨25775596916128207000344581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17183731277418804666896387 25775596916128207000344581)
                  ·
                    refine ⟨4832924421774038812564609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25775596916128207000344581 4832924421774038812564609)
                    ·
                      refine ⟨3624693316330529109423457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4832924421774038812564609 3624693316330529109423457)
                      ·
                        rfl

theorem cell23_7059065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 3, 1, 4, 2].length) (baseStart_7059065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7059065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7059065 prefixEnd_7059065 := by exact prefixLift 7059065
  have htrace : WordTrace (prefixWord ++ tailWord_7059065) baseStart_7059065 baseEnd_7059065 := by
    simpa [prefixWord, tailWord_7059065, baseEnd_7059065] using wordTrace_append hprefix tailTrace_7059065
  have hstable : (prefixWord ++ tailWord_7059065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7059065).length < 2 ^ (prefixWord ++ tailWord_7059065).sum := by decide
  have hdescent : baseEnd_7059065 < baseStart_7059065 := by decide
  rcases family_descends (prefixWord ++ tailWord_7059065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7059069 : List Nat := [1, 4, 1, 1, 4, 3, 1, 2, 1, 3, 2]
def baseStart_7059069 : Nat := 118140960795 + 7059069 * 2 ^ 59
def prefixEnd_7059069 : Nat := 4983230072969 + 3 ^ 40 * 7059069 * 2
def baseEnd_7059069 : Nat := 3624695370253147093773439

theorem tailTrace_7059069 : CollatzResearch.WordTrace tailWord_7059069 prefixEnd_7059069 3624695370253147093773439 := by
  unfold tailWord_7059069
  simp only [CollatzResearch.WordTrace]
  refine ⟨257465398063206080848148261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171643598708804053898765507 257465398063206080848148261)
  ·
    refine ⟨48274762136851140159027799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 257465398063206080848148261 48274762136851140159027799)
    ·
      refine ⟨72412143205276710238541699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48274762136851140159027799 72412143205276710238541699)
      ·
        refine ⟨108618214807915065357812549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72412143205276710238541699 108618214807915065357812549)
        ·
          refine ⟨20365915276484074754589853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 108618214807915065357812549 20365915276484074754589853)
          ·
            refine ⟨7637218228681528032971195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20365915276484074754589853 7637218228681528032971195)
            ·
              refine ⟨11455827343022292049456793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7637218228681528032971195 11455827343022292049456793)
              ·
                refine ⟨8591870507266719037092595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11455827343022292049456793 8591870507266719037092595)
                ·
                  refine ⟨12887805760900078555638893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8591870507266719037092595 12887805760900078555638893)
                  ·
                    refine ⟨4832927160337529458364585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12887805760900078555638893 4832927160337529458364585)
                    ·
                      refine ⟨3624695370253147093773439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4832927160337529458364585 3624695370253147093773439)
                      ·
                        rfl

theorem cell23_7059069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 1, 2, 1, 3, 2].length) (baseStart_7059069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7059069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7059069 prefixEnd_7059069 := by exact prefixLift 7059069
  have htrace : WordTrace (prefixWord ++ tailWord_7059069) baseStart_7059069 baseEnd_7059069 := by
    simpa [prefixWord, tailWord_7059069, baseEnd_7059069] using wordTrace_append hprefix tailTrace_7059069
  have hstable : (prefixWord ++ tailWord_7059069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7059069).length < 2 ^ (prefixWord ++ tailWord_7059069).sum := by decide
  have hdescent : baseEnd_7059069 < baseStart_7059069 := by decide
  rcases family_descends (prefixWord ++ tailWord_7059069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7059082 : List Nat := [3, 1, 2, 3, 2, 2, 1, 2, 1, 4, 2]
def baseStart_7059082 : Nat := 118140960795 + 7059082 * 2 ^ 59
def prefixEnd_7059082 : Nat := 4983230072969 + 3 ^ 40 * 7059082 * 2
def baseEnd_7059082 : Nat := 3624702045501655542910879

theorem tailTrace_7059082 : CollatzResearch.WordTrace tailWord_7059082 prefixEnd_7059082 3624702045501655542910879 := by
  unfold tailWord_7059082
  simp only [CollatzResearch.WordTrace]
  refine ⟨64366468053039746017092875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171643914808105989378914333 64366468053039746017092875)
  ·
    refine ⟨96549702079559619025639313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64366468053039746017092875 96549702079559619025639313)
    ·
      refine ⟨72412276559669714269229485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96549702079559619025639313 72412276559669714269229485)
      ·
        refine ⟨27154603709876142850961057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72412276559669714269229485 27154603709876142850961057)
        ·
          refine ⟨20365952782407107138220793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27154603709876142850961057 20365952782407107138220793)
          ·
            refine ⟨15274464586805330353665595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20365952782407107138220793 15274464586805330353665595)
            ·
              refine ⟨22911696880207995530498393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15274464586805330353665595 22911696880207995530498393)
              ·
                refine ⟨17183772660155996647873795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22911696880207995530498393 17183772660155996647873795)
                ·
                  refine ⟨25775658990233994971810693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17183772660155996647873795 25775658990233994971810693)
                  ·
                    refine ⟨4832936060668874057214505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25775658990233994971810693 4832936060668874057214505)
                    ·
                      refine ⟨3624702045501655542910879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4832936060668874057214505 3624702045501655542910879)
                      ·
                        rfl

theorem cell23_7059082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 2, 1, 4, 2].length) (baseStart_7059082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7059082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7059082 prefixEnd_7059082 := by exact prefixLift 7059082
  have htrace : WordTrace (prefixWord ++ tailWord_7059082) baseStart_7059082 baseEnd_7059082 := by
    simpa [prefixWord, tailWord_7059082, baseEnd_7059082] using wordTrace_append hprefix tailTrace_7059082
  have hstable : (prefixWord ++ tailWord_7059082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7059082).length < 2 ^ (prefixWord ++ tailWord_7059082).sum := by decide
  have hdescent : baseEnd_7059082 < baseStart_7059082 := by decide
  rcases family_descends (prefixWord ++ tailWord_7059082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7059091 : List Nat := [1, 1, 1, 2, 1, 2, 2, 1, 2, 4, 6]
def baseStart_7059091 : Nat := 118140960795 + 7059091 * 2 ^ 59
def prefixEnd_7059091 : Nat := 4983230072969 + 3 ^ 40 * 7059091 * 2
def baseEnd_7059091 : Nat := 3624706666827546007698337

theorem tailTrace_7059091 : CollatzResearch.WordTrace tailWord_7059091 prefixEnd_7059091 3624706666827546007698337 := by
  unfold tailWord_7059091
  simp only [CollatzResearch.WordTrace]
  refine ⟨257466200469126378605449127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171644133646084252403632751 257466200469126378605449127)
  ·
    refine ⟨386199300703689567908173691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257466200469126378605449127 386199300703689567908173691)
    ·
      refine ⟨579298951055534351862260537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 386199300703689567908173691 579298951055534351862260537)
      ·
        refine ⟨434474213291650763896695403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 579298951055534351862260537 434474213291650763896695403)
        ·
          refine ⟨651711319937476145845043105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 434474213291650763896695403 651711319937476145845043105)
          ·
            refine ⟨488783489953107109383782329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 651711319937476145845043105 488783489953107109383782329)
            ·
              refine ⟨366587617464830332037836747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 488783489953107109383782329 366587617464830332037836747)
              ·
                refine ⟨549881426197245498056755121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 366587617464830332037836747 549881426197245498056755121)
                ·
                  refine ⟨412411069647934123542566341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 549881426197245498056755121 412411069647934123542566341)
                  ·
                    refine ⟨77327075558987648164231189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 412411069647934123542566341 77327075558987648164231189)
                    ·
                      refine ⟨3624706666827546007698337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 77327075558987648164231189 3624706666827546007698337)
                      ·
                        rfl

theorem cell23_7059091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 2, 4, 6].length) (baseStart_7059091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7059091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7059091 prefixEnd_7059091 := by exact prefixLift 7059091
  have htrace : WordTrace (prefixWord ++ tailWord_7059091) baseStart_7059091 baseEnd_7059091 := by
    simpa [prefixWord, tailWord_7059091, baseEnd_7059091] using wordTrace_append hprefix tailTrace_7059091
  have hstable : (prefixWord ++ tailWord_7059091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7059091).length < 2 ^ (prefixWord ++ tailWord_7059091).sum := by decide
  have hdescent : baseEnd_7059091 < baseStart_7059091 := by decide
  rcases family_descends (prefixWord ++ tailWord_7059091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7059215 : List Nat := [1, 1, 2, 1, 1, 1, 4, 2, 3, 5, 2]
def baseStart_7059215 : Nat := 118140960795 + 7059215 * 2 ^ 59
def prefixEnd_7059215 : Nat := 4983230072969 + 3 ^ 40 * 7059215 * 2
def baseEnd_7059215 : Nat := 3624770338428703522547767

theorem tailTrace_7059215 : CollatzResearch.WordTrace tailWord_7059215 prefixEnd_7059215 3624770338428703522547767 := by
  unfold tailWord_7059215
  simp only [CollatzResearch.WordTrace]
  refine ⟨257470723120677147782963099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171647148747118098521975399 257470723120677147782963099)
  ·
    refine ⟨386206084681015721674444649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257470723120677147782963099 386206084681015721674444649)
    ·
      refine ⟨289654563510761791255833487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 386206084681015721674444649 289654563510761791255833487)
      ·
        refine ⟨434481845266142686883750231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 289654563510761791255833487 434481845266142686883750231)
        ·
          refine ⟨651722767899214030325625347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 434481845266142686883750231 651722767899214030325625347)
          ·
            refine ⟨977584151848821045488438021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 651722767899214030325625347 977584151848821045488438021)
            ·
              refine ⟨183297028471653946029082129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 977584151848821045488438021 183297028471653946029082129)
              ·
                refine ⟨137472771353740459521811597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 183297028471653946029082129 137472771353740459521811597)
                ·
                  refine ⟨51552289257652672320679349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 137472771353740459521811597 51552289257652672320679349)
                  ·
                    refine ⟨4833027117904938030063689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51552289257652672320679349 4833027117904938030063689)
                    ·
                      refine ⟨3624770338428703522547767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4833027117904938030063689 3624770338428703522547767)
                      ·
                        rfl

theorem cell23_7059215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 2, 3, 5, 2].length) (baseStart_7059215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7059215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7059215 prefixEnd_7059215 := by exact prefixLift 7059215
  have htrace : WordTrace (prefixWord ++ tailWord_7059215) baseStart_7059215 baseEnd_7059215 := by
    simpa [prefixWord, tailWord_7059215, baseEnd_7059215] using wordTrace_append hprefix tailTrace_7059215
  have hstable : (prefixWord ++ tailWord_7059215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7059215).length < 2 ^ (prefixWord ++ tailWord_7059215).sum := by decide
  have hdescent : baseEnd_7059215 < baseStart_7059215 := by decide
  rcases family_descends (prefixWord ++ tailWord_7059215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7059232 : List Nat := [2, 1, 1, 5, 1, 1, 1, 2, 4, 3, 2]
def baseStart_7059232 : Nat := 118140960795 + 7059232 * 2 ^ 59
def prefixEnd_7059232 : Nat := 4983230072969 + 3 ^ 40 * 7059232 * 2
def baseEnd_7059232 : Nat := 3624779067599829956035189

theorem tailTrace_7059232 : CollatzResearch.WordTrace tailWord_7059232 prefixEnd_7059232 3624779067599829956035189 := by
  unfold tailWord_7059232
  simp only [CollatzResearch.WordTrace]
  refine ⟨128735671580807779843165975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171647562107743706457554633 128735671580807779843165975)
  ·
    refine ⟨193103507371211669764748963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128735671580807779843165975 193103507371211669764748963)
    ·
      refine ⟨289655261056817504647123445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193103507371211669764748963 289655261056817504647123445)
      ·
        refine ⟨27155180724076641060667823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 289655261056817504647123445 27155180724076641060667823)
        ·
          refine ⟨40732771086114961591001735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27155180724076641060667823 40732771086114961591001735)
          ·
            refine ⟨61099156629172442386502603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40732771086114961591001735 61099156629172442386502603)
            ·
              refine ⟨91648734943758663579753905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61099156629172442386502603 91648734943758663579753905)
              ·
                refine ⟨68736551207818997684815429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91648734943758663579753905 68736551207818997684815429)
                ·
                  refine ⟨12888103351466062065902893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 68736551207818997684815429 12888103351466062065902893)
                  ·
                    refine ⟨4833038756799773274713585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12888103351466062065902893 4833038756799773274713585)
                    ·
                      refine ⟨3624779067599829956035189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4833038756799773274713585 3624779067599829956035189)
                      ·
                        rfl

theorem cell23_7059232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 2, 4, 3, 2].length) (baseStart_7059232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7059232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7059232 prefixEnd_7059232 := by exact prefixLift 7059232
  have htrace : WordTrace (prefixWord ++ tailWord_7059232) baseStart_7059232 baseEnd_7059232 := by
    simpa [prefixWord, tailWord_7059232, baseEnd_7059232] using wordTrace_append hprefix tailTrace_7059232
  have hstable : (prefixWord ++ tailWord_7059232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7059232).length < 2 ^ (prefixWord ++ tailWord_7059232).sum := by decide
  have hdescent : baseEnd_7059232 < baseStart_7059232 := by decide
  rcases family_descends (prefixWord ++ tailWord_7059232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7059248 : List Nat := [2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 5]
def baseStart_7059248 : Nat := 118140960795 + 7059248 * 2 ^ 59
def prefixEnd_7059248 : Nat := 4983230072969 + 3 ^ 40 * 7059248 * 2
def baseEnd_7059248 : Nat := 3624787283290301893435115

theorem tailTrace_7059248 : CollatzResearch.WordTrace tailWord_7059248 prefixEnd_7059248 3624787283290301893435115 := by
  unfold tailWord_7059248
  simp only [CollatzResearch.WordTrace]
  refine ⟨128735963364778797209457199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171647951153038396279276265 128735963364778797209457199)
  ·
    refine ⟨193103945047168195814185799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128735963364778797209457199 193103945047168195814185799)
    ·
      refine ⟨289655917570752293721278699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193103945047168195814185799 289655917570752293721278699)
      ·
        refine ⟨434483876356128440581918049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 289655917570752293721278699 434483876356128440581918049)
        ·
          refine ⟨325862907267096330436438537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 434483876356128440581918049 325862907267096330436438537)
          ·
            refine ⟨244397180450322247827328903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 325862907267096330436438537 244397180450322247827328903)
            ·
              refine ⟨366595770675483371740993355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 244397180450322247827328903 366595770675483371740993355)
              ·
                refine ⟨549893656013225057611490033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 366595770675483371740993355 549893656013225057611490033)
                ·
                  refine ⟨412420242009918793208617525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 549893656013225057611490033 412420242009918793208617525)
                  ·
                    refine ⟨38664397688429886863307893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 412420242009918793208617525 38664397688429886863307893)
                    ·
                      refine ⟨3624787283290301893435115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38664397688429886863307893 3624787283290301893435115)
                      ·
                        rfl

theorem cell23_7059248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 5].length) (baseStart_7059248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7059248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7059248 prefixEnd_7059248 := by exact prefixLift 7059248
  have htrace : WordTrace (prefixWord ++ tailWord_7059248) baseStart_7059248 baseEnd_7059248 := by
    simpa [prefixWord, tailWord_7059248, baseEnd_7059248] using wordTrace_append hprefix tailTrace_7059248
  have hstable : (prefixWord ++ tailWord_7059248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7059248).length < 2 ^ (prefixWord ++ tailWord_7059248).sum := by decide
  have hdescent : baseEnd_7059248 < baseStart_7059248 := by decide
  rcases family_descends (prefixWord ++ tailWord_7059248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7059249 : List Nat := [1, 2, 2, 3, 2, 3, 2, 1, 2, 3, 2]
def baseStart_7059249 : Nat := 118140960795 + 7059249 * 2 ^ 59
def prefixEnd_7059249 : Nat := 4983230072969 + 3 ^ 40 * 7059249 * 2
def baseEnd_7059249 : Nat := 3624787796770956389522611

theorem tailTrace_7059249 : CollatzResearch.WordTrace tailWord_7059249 prefixEnd_7059249 3624787796770956389522611 := by
  unfold tailWord_7059249
  simp only [CollatzResearch.WordTrace]
  refine ⟨257471963202553971589700801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171647975468369314393133867 257471963202553971589700801)
  ·
    refine ⟨193103972401915478692275601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257471963202553971589700801 193103972401915478692275601)
    ·
      refine ⟨144827979301436609019206701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193103972401915478692275601 144827979301436609019206701)
      ·
        refine ⟨54310492238038728382202513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144827979301436609019206701 54310492238038728382202513)
        ·
          refine ⟨40732869178529046286651885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54310492238038728382202513 40732869178529046286651885)
          ·
            refine ⟨15274825941948392357494457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40732869178529046286651885 15274825941948392357494457)
            ·
              refine ⟨11456119456461294268120843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15274825941948392357494457 11456119456461294268120843)
              ·
                refine ⟨17184179184691941402181265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11456119456461294268120843 17184179184691941402181265)
                ·
                  refine ⟨12888134388518956051635949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17184179184691941402181265 12888134388518956051635949)
                  ·
                    refine ⟨4833050395694608519363481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12888134388518956051635949 4833050395694608519363481)
                    ·
                      refine ⟨3624787796770956389522611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4833050395694608519363481 3624787796770956389522611)
                      ·
                        rfl

theorem cell23_7059249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 2, 1, 2, 3, 2].length) (baseStart_7059249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7059249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7059249 prefixEnd_7059249 := by exact prefixLift 7059249
  have htrace : WordTrace (prefixWord ++ tailWord_7059249) baseStart_7059249 baseEnd_7059249 := by
    simpa [prefixWord, tailWord_7059249, baseEnd_7059249] using wordTrace_append hprefix tailTrace_7059249
  have hstable : (prefixWord ++ tailWord_7059249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7059249).length < 2 ^ (prefixWord ++ tailWord_7059249).sum := by decide
  have hdescent : baseEnd_7059249 < baseStart_7059249 := by decide
  rcases family_descends (prefixWord ++ tailWord_7059249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7059255 : List Nat := [1, 1, 3, 1, 2, 1, 2, 4, 4, 4]
def baseStart_7059255 : Nat := 118140960795 + 7059255 * 2 ^ 59
def prefixEnd_7059255 : Nat := 4983230072969 + 3 ^ 40 * 7059255 * 2
def baseEnd_7059255 : Nat := 1208263625884961122015861

theorem tailTrace_7059255 : CollatzResearch.WordTrace tailWord_7059255 prefixEnd_7059255 1208263625884961122015861 := by
  unfold tailWord_7059255
  simp only [CollatzResearch.WordTrace]
  refine ⟨257472182040532234614419219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171648121360354823076279479 257472182040532234614419219)
  ·
    refine ⟨386208273060798351921628829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257472182040532234614419219 386208273060798351921628829)
    ·
      refine ⟨144828102397799381970610811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 386208273060798351921628829 144828102397799381970610811)
      ·
        refine ⟨217242153596699072955916217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144828102397799381970610811 217242153596699072955916217)
        ·
          refine ⟨162931615197524304716937163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 217242153596699072955916217 162931615197524304716937163)
          ·
            refine ⟨244397422796286457075405745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162931615197524304716937163 244397422796286457075405745)
            ·
              refine ⟨183298067097214842806554309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 244397422796286457075405745 183298067097214842806554309)
              ·
                refine ⟨34368387580727783026228933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 183298067097214842806554309 34368387580727783026228933)
                ·
                  refine ⟨6444072671386459317417925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34368387580727783026228933 6444072671386459317417925)
                  ·
                    refine ⟨1208263625884961122015861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6444072671386459317417925 1208263625884961122015861)
                    ·
                      rfl

theorem cell23_7059255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 4, 4, 4].length) (baseStart_7059255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7059255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7059255 prefixEnd_7059255 := by exact prefixLift 7059255
  have htrace : WordTrace (prefixWord ++ tailWord_7059255) baseStart_7059255 baseEnd_7059255 := by
    simpa [prefixWord, tailWord_7059255, baseEnd_7059255] using wordTrace_append hprefix tailTrace_7059255
  have hstable : (prefixWord ++ tailWord_7059255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7059255).length < 2 ^ (prefixWord ++ tailWord_7059255).sum := by decide
  have hdescent : baseEnd_7059255 < baseStart_7059255 := by decide
  rcases family_descends (prefixWord ++ tailWord_7059255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7059272 : List Nat := [2, 1, 3, 1, 1, 4, 1, 4, 2, 4]
def baseStart_7059272 : Nat := 118140960795 + 7059272 * 2 ^ 59
def prefixEnd_7059272 : Nat := 4983230072969 + 3 ^ 40 * 7059272 * 2
def baseEnd_7059272 : Nat := 1208266535608669933178335

theorem tailTrace_7059272 : CollatzResearch.WordTrace tailWord_7059272 prefixEnd_7059272 1208266535608669933178335 := by
  unfold tailWord_7059272
  simp only [CollatzResearch.WordTrace]
  refine ⟨128736401040735323258894035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171648534720980431011858713 128736401040735323258894035)
  ·
    refine ⟨193104601561102984888341053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128736401040735323258894035 193104601561102984888341053)
    ·
      refine ⟨72414225585413619333127895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 193104601561102984888341053 72414225585413619333127895)
      ·
        refine ⟨108621338378120428999691843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72414225585413619333127895 108621338378120428999691843)
        ·
          refine ⟨162932007567180643499537765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108621338378120428999691843 162932007567180643499537765)
          ·
            refine ⟨30549751418846370656163331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 162932007567180643499537765 30549751418846370656163331)
            ·
              refine ⟨45824627128269555984244997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30549751418846370656163331 45824627128269555984244997)
              ·
                refine ⟨8592117586550541747045937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45824627128269555984244997 8592117586550541747045937)
                ·
                  refine ⟨6444088189912906310284453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8592117586550541747045937 6444088189912906310284453)
                  ·
                    refine ⟨1208266535608669933178335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6444088189912906310284453 1208266535608669933178335)
                    ·
                      rfl

theorem cell23_7059272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 4, 2, 4].length) (baseStart_7059272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7059272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7059272 prefixEnd_7059272 := by exact prefixLift 7059272
  have htrace : WordTrace (prefixWord ++ tailWord_7059272) baseStart_7059272 baseEnd_7059272 := by
    simpa [prefixWord, tailWord_7059272, baseEnd_7059272] using wordTrace_append hprefix tailTrace_7059272
  have hstable : (prefixWord ++ tailWord_7059272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7059272).length < 2 ^ (prefixWord ++ tailWord_7059272).sum := by decide
  have hdescent : baseEnd_7059272 < baseStart_7059272 := by decide
  rcases family_descends (prefixWord ++ tailWord_7059272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7059282 : List Nat := [3, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3]
def baseStart_7059282 : Nat := 118140960795 + 7059282 * 2 ^ 59
def prefixEnd_7059282 : Nat := 4983230072969 + 3 ^ 40 * 7059282 * 2
def baseEnd_7059282 : Nat := 3624804741632554760409959

theorem tailTrace_7059282 : CollatzResearch.WordTrace tailWord_7059282 prefixEnd_7059282 3624804741632554760409959 := by
  unfold tailWord_7059282
  simp only [CollatzResearch.WordTrace]
  refine ⟨64368291702858604556413025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171648777874289612150434733 64368291702858604556413025)
  ·
    refine ⟨48276218777143953417309769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64368291702858604556413025 48276218777143953417309769)
    ·
      refine ⟨36207164082857965062982327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48276218777143953417309769 36207164082857965062982327)
      ·
        refine ⟨54310746124286947594473491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36207164082857965062982327 54310746124286947594473491)
        ·
          refine ⟨81466119186430421391710237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54310746124286947594473491 81466119186430421391710237)
          ·
            refine ⟨30549794694911408021891339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81466119186430421391710237 30549794694911408021891339)
            ·
              refine ⟨45824692042367112032837009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30549794694911408021891339 45824692042367112032837009)
              ·
                refine ⟨34368519031775334024627757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45824692042367112032837009 34368519031775334024627757)
                ·
                  refine ⟨12888194636915750259235409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34368519031775334024627757 12888194636915750259235409)
                  ·
                    refine ⟨9666145977686812694426557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12888194636915750259235409 9666145977686812694426557)
                    ·
                      refine ⟨3624804741632554760409959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9666145977686812694426557 3624804741632554760409959)
                      ·
                        rfl

theorem cell23_7059282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3].length) (baseStart_7059282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7059282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7059282 prefixEnd_7059282 := by exact prefixLift 7059282
  have htrace : WordTrace (prefixWord ++ tailWord_7059282) baseStart_7059282 baseEnd_7059282 := by
    simpa [prefixWord, tailWord_7059282, baseEnd_7059282] using wordTrace_append hprefix tailTrace_7059282
  have hstable : (prefixWord ++ tailWord_7059282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7059282).length < 2 ^ (prefixWord ++ tailWord_7059282).sum := by decide
  have hdescent : baseEnd_7059282 < baseStart_7059282 := by decide
  rcases family_descends (prefixWord ++ tailWord_7059282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7059285 : List Nat := [1, 3, 2, 2, 2, 2, 3, 8]
def baseStart_7059285 : Nat := 118140960795 + 7059285 * 2 ^ 59
def prefixEnd_7059285 : Nat := 4983230072969 + 3 ^ 40 * 7059285 * 2
def baseEnd_7059285 : Nat := 134252084521278453654535

theorem tailTrace_7059285 : CollatzResearch.WordTrace tailWord_7059285 prefixEnd_7059285 134252084521278453654535 := by
  unfold tailWord_7059285
  simp only [CollatzResearch.WordTrace]
  refine ⟨257473276230423549738011309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171648850820282366492007539 257473276230423549738011309)
  ·
    refine ⟨96552478586408831151754241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 257473276230423549738011309 96552478586408831151754241)
    ·
      refine ⟨72414358939806623363815681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96552478586408831151754241 72414358939806623363815681)
      ·
        refine ⟨54310769204854967522861761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72414358939806623363815681 54310769204854967522861761)
        ·
          refine ⟨40733076903641225642146321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54310769204854967522861761 40733076903641225642146321)
          ·
            refine ⟨30549807677730919231609741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40733076903641225642146321 30549807677730919231609741)
            ·
              refine ⟨11456177879149094711853653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30549807677730919231609741 11456177879149094711853653)
              ·
                refine ⟨134252084521278453654535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11456177879149094711853653 134252084521278453654535)
                ·
                  rfl

theorem cell23_7059285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 3, 8].length) (baseStart_7059285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7059285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7059285 prefixEnd_7059285 := by exact prefixLift 7059285
  have htrace : WordTrace (prefixWord ++ tailWord_7059285) baseStart_7059285 baseEnd_7059285 := by
    simpa [prefixWord, tailWord_7059285, baseEnd_7059285] using wordTrace_append hprefix tailTrace_7059285
  have hstable : (prefixWord ++ tailWord_7059285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7059285).length < 2 ^ (prefixWord ++ tailWord_7059285).sum := by decide
  have hdescent : baseEnd_7059285 < baseStart_7059285 := by decide
  rcases family_descends (prefixWord ++ tailWord_7059285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7059312 : List Nat := [2, 1, 1, 1, 4, 1, 1, 4, 4, 1, 3]
def baseStart_7059312 : Nat := 118140960795 + 7059312 * 2 ^ 59
def prefixEnd_7059312 : Nat := 4983230072969 + 3 ^ 40 * 7059312 * 2
def baseEnd_7059312 : Nat := 3624820146052189643034821

theorem tailTrace_7059312 : CollatzResearch.WordTrace tailWord_7059312 prefixEnd_7059312 3624820146052189643034821 := by
  unfold tailWord_7059312
  simp only [CollatzResearch.WordTrace]
  refine ⟨128737130500662866674622095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171649507334217155566162793 128737130500662866674622095)
  ·
    refine ⟨193105695750994300011933143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128737130500662866674622095 193105695750994300011933143)
    ·
      refine ⟨289658543626491450017899715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193105695750994300011933143 289658543626491450017899715)
      ·
        refine ⟨434487815439737175026849573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 289658543626491450017899715 434487815439737175026849573)
        ·
          refine ⟨81466465394950720317534295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 434487815439737175026849573 81466465394950720317534295)
          ·
            refine ⟨122199698092426080476301443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81466465394950720317534295 122199698092426080476301443)
            ·
              refine ⟨183299547138639120714452165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122199698092426080476301443 183299547138639120714452165)
              ·
                refine ⟨34368665088494835133959781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 183299547138639120714452165 34368665088494835133959781)
                ·
                  refine ⟨6444124704092781587617459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34368665088494835133959781 6444124704092781587617459)
                  ·
                    refine ⟨9666187056139172381426189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6444124704092781587617459 9666187056139172381426189)
                    ·
                      refine ⟨3624820146052189643034821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9666187056139172381426189 3624820146052189643034821)
                      ·
                        rfl

theorem cell23_7059312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 4, 4, 1, 3].length) (baseStart_7059312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7059312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7059312 prefixEnd_7059312 := by exact prefixLift 7059312
  have htrace : WordTrace (prefixWord ++ tailWord_7059312) baseStart_7059312 baseEnd_7059312 := by
    simpa [prefixWord, tailWord_7059312, baseEnd_7059312] using wordTrace_append hprefix tailTrace_7059312
  have hstable : (prefixWord ++ tailWord_7059312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7059312).length < 2 ^ (prefixWord ++ tailWord_7059312).sum := by decide
  have hdescent : baseEnd_7059312 < baseStart_7059312 := by decide
  rcases family_descends (prefixWord ++ tailWord_7059312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7059345 : List Nat := [1, 2, 2, 1, 1, 1, 6, 1, 2, 6]
def baseStart_7059345 : Nat := 118140960795 + 7059345 * 2 ^ 59
def prefixEnd_7059345 : Nat := 4983230072969 + 3 ^ 40 * 7059345 * 2
def baseEnd_7059345 : Nat := 1208279030304596004640723

theorem tailTrace_7059345 : CollatzResearch.WordTrace tailWord_7059345 prefixEnd_7059345 1208279030304596004640723 := by
  unfold tailWord_7059345
  simp only [CollatzResearch.WordTrace]
  refine ⟨257475464610206179985195489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171650309740137453323463659 257475464610206179985195489)
  ·
    refine ⟨193106598457654634988896617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257475464610206179985195489 193106598457654634988896617)
    ·
      refine ⟨144829948843240976241672463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193106598457654634988896617 144829948843240976241672463)
      ·
        refine ⟨217244923264861464362508695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144829948843240976241672463 217244923264861464362508695)
        ·
          refine ⟨325867384897292196543763043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217244923264861464362508695 325867384897292196543763043)
          ·
            refine ⟨488801077345938294815644565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 325867384897292196543763043 488801077345938294815644565)
            ·
              refine ⟨22912550500590857569483339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 488801077345938294815644565 22912550500590857569483339)
              ·
                refine ⟨34368825750886286354225009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22912550500590857569483339 34368825750886286354225009)
                ·
                  refine ⟨25776619313164714765668757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34368825750886286354225009 25776619313164714765668757)
                  ·
                    refine ⟨1208279030304596004640723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25776619313164714765668757 1208279030304596004640723)
                    ·
                      rfl

theorem cell23_7059345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 6].length) (baseStart_7059345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7059345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7059345 prefixEnd_7059345 := by exact prefixLift 7059345
  have htrace : WordTrace (prefixWord ++ tailWord_7059345) baseStart_7059345 baseEnd_7059345 := by
    simpa [prefixWord, tailWord_7059345, baseEnd_7059345] using wordTrace_append hprefix tailTrace_7059345
  have hstable : (prefixWord ++ tailWord_7059345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7059345).length < 2 ^ (prefixWord ++ tailWord_7059345).sum := by decide
  have hdescent : baseEnd_7059345 < baseStart_7059345 := by decide
  rcases family_descends (prefixWord ++ tailWord_7059345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7059346 : List Nat := [3, 2, 3, 2, 1, 3, 1, 1, 1, 3, 3]
def baseStart_7059346 : Nat := 118140960795 + 7059346 * 2 ^ 59
def prefixEnd_7059346 : Nat := 4983230072969 + 3 ^ 40 * 7059346 * 2
def baseEnd_7059346 : Nat := 3624837604394442510009665

theorem tailTrace_7059346 : CollatzResearch.WordTrace tailWord_7059346 prefixEnd_7059346 3624837604394442510009665 := by
  unfold tailWord_7059346
  simp only [CollatzResearch.WordTrace]
  refine ⟨64368875270800639288995473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171650334055468371437321261 64368875270800639288995473)
  ·
    refine ⟨48276656453100479466746605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64368875270800639288995473 48276656453100479466746605)
    ·
      refine ⟨18103746169912679800029977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48276656453100479466746605 18103746169912679800029977)
      ·
        refine ⟨13577809627434509850022483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18103746169912679800029977 13577809627434509850022483)
        ·
          refine ⟨20366714441151764775033725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13577809627434509850022483 20366714441151764775033725)
          ·
            refine ⟨7637517915431911790637647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20366714441151764775033725 7637517915431911790637647)
            ·
              refine ⟨11456276873147867685956471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7637517915431911790637647 11456276873147867685956471)
              ·
                refine ⟨17184415309721801528934707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11456276873147867685956471 17184415309721801528934707)
                ·
                  refine ⟨25776622964582702293402061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17184415309721801528934707 25776622964582702293402061)
                  ·
                    refine ⟨9666233611718513360025773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25776622964582702293402061 9666233611718513360025773)
                    ·
                      refine ⟨3624837604394442510009665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9666233611718513360025773 3624837604394442510009665)
                      ·
                        rfl

theorem cell23_7059346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 1, 1, 1, 3, 3].length) (baseStart_7059346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7059346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7059346 prefixEnd_7059346 := by exact prefixLift 7059346
  have htrace : WordTrace (prefixWord ++ tailWord_7059346) baseStart_7059346 baseEnd_7059346 := by
    simpa [prefixWord, tailWord_7059346, baseEnd_7059346] using wordTrace_append hprefix tailTrace_7059346
  have hstable : (prefixWord ++ tailWord_7059346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7059346).length < 2 ^ (prefixWord ++ tailWord_7059346).sum := by decide
  have hdescent : baseEnd_7059346 < baseStart_7059346 := by decide
  rcases family_descends (prefixWord ++ tailWord_7059346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7059350 : List Nat := [5, 3, 1, 1, 2, 1, 2, 2, 1, 2, 3]
def baseStart_7059350 : Nat := 118140960795 + 7059350 * 2 ^ 59
def prefixEnd_7059350 : Nat := 4983230072969 + 3 ^ 40 * 7059350 * 2
def baseEnd_7059350 : Nat := 3624839658317060494359647

theorem tailTrace_7059350 : CollatzResearch.WordTrace tailWord_7059350 prefixEnd_7059350 3624839658317060494359647 := by
  unfold tailWord_7059350
  simp only [CollatzResearch.WordTrace]
  refine ⟨16092227935949254114945469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 171650431316792043892751669 16092227935949254114945469)
  ·
    refine ⟨6034585475980970293104551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16092227935949254114945469 6034585475980970293104551)
    ·
      refine ⟨9051878213971455439656827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6034585475980970293104551 9051878213971455439656827)
      ·
        refine ⟨13577817320957183159485241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9051878213971455439656827 13577817320957183159485241)
        ·
          refine ⟨10183362990717887369613931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13577817320957183159485241 10183362990717887369613931)
          ·
            refine ⟨15275044486076831054420897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10183362990717887369613931 15275044486076831054420897)
            ·
              refine ⟨11456283364557623290815673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15275044486076831054420897 11456283364557623290815673)
              ·
                refine ⟨8592212523418217468111755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11456283364557623290815673 8592212523418217468111755)
                ·
                  refine ⟨12888318785127326202167633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8592212523418217468111755 12888318785127326202167633)
                  ·
                    refine ⟨9666239088845494651625725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12888318785127326202167633 9666239088845494651625725)
                    ·
                      refine ⟨3624839658317060494359647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9666239088845494651625725 3624839658317060494359647)
                      ·
                        rfl

theorem cell23_7059350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 2, 2, 1, 2, 3].length) (baseStart_7059350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7059350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7059350 prefixEnd_7059350 := by exact prefixLift 7059350
  have htrace : WordTrace (prefixWord ++ tailWord_7059350) baseStart_7059350 baseEnd_7059350 := by
    simpa [prefixWord, tailWord_7059350, baseEnd_7059350] using wordTrace_append hprefix tailTrace_7059350
  have hstable : (prefixWord ++ tailWord_7059350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7059350).length < 2 ^ (prefixWord ++ tailWord_7059350).sum := by decide
  have hdescent : baseEnd_7059350 < baseStart_7059350 := by decide
  rcases family_descends (prefixWord ++ tailWord_7059350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7059356 : List Nat := [2, 2, 3, 3, 1, 1, 1, 4, 1, 3, 2]
def baseStart_7059356 : Nat := 118140960795 + 7059356 * 2 ^ 59
def prefixEnd_7059356 : Nat := 4983230072969 + 3 ^ 40 * 7059356 * 2
def baseEnd_7059356 : Nat := 3624842739200987470884619

theorem tailTrace_7059356 : CollatzResearch.WordTrace tailWord_7059356 prefixEnd_7059356 3624842739200987470884619 := by
  unfold tailWord_7059356
  simp only [CollatzResearch.WordTrace]
  refine ⟨128737932906583164431922961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171650577208777552575897281 128737932906583164431922961)
  ·
    refine ⟨96553449679937373323942221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128737932906583164431922961 96553449679937373323942221)
    ·
      refine ⟨36207543629976514996478333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96553449679937373323942221 36207543629976514996478333)
      ·
        refine ⟨13577828861241193123679375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36207543629976514996478333 13577828861241193123679375)
        ·
          refine ⟨20366743291861789685519063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13577828861241193123679375 20366743291861789685519063)
          ·
            refine ⟨30550114937792684528278595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20366743291861789685519063 30550114937792684528278595)
            ·
              refine ⟨45825172406689026792417893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30550114937792684528278595 45825172406689026792417893)
              ·
                refine ⟨8592219826254192523578355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45825172406689026792417893 8592219826254192523578355)
                ·
                  refine ⟨12888329739381288785367533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8592219826254192523578355 12888329739381288785367533)
                  ·
                    refine ⟨4833123652267983294512825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12888329739381288785367533 4833123652267983294512825)
                    ·
                      refine ⟨3624842739200987470884619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4833123652267983294512825 3624842739200987470884619)
                      ·
                        rfl

theorem cell23_7059356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 4, 1, 3, 2].length) (baseStart_7059356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7059356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7059356 prefixEnd_7059356 := by exact prefixLift 7059356
  have htrace : WordTrace (prefixWord ++ tailWord_7059356) baseStart_7059356 baseEnd_7059356 := by
    simpa [prefixWord, tailWord_7059356, baseEnd_7059356] using wordTrace_append hprefix tailTrace_7059356
  have hstable : (prefixWord ++ tailWord_7059356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7059356).length < 2 ^ (prefixWord ++ tailWord_7059356).sum := by decide
  have hdescent : baseEnd_7059356 < baseStart_7059356 := by decide
  rcases family_descends (prefixWord ++ tailWord_7059356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7059365 : List Nat := [1, 3, 1, 2, 1, 1, 1, 4, 1, 4, 4]
def baseStart_7059365 : Nat := 118140960795 + 7059365 * 2 ^ 59
def prefixEnd_7059365 : Nat := 4983230072969 + 3 ^ 40 * 7059365 * 2
def baseEnd_7059365 : Nat := 3624847360526877935672077

theorem tailTrace_7059365 : CollatzResearch.WordTrace tailWord_7059365 prefixEnd_7059365 3624847360526877935672077 := by
  unfold tailWord_7059365
  simp only [CollatzResearch.WordTrace]
  refine ⟨257476194070133723400923549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171650796046755815600615699 257476194070133723400923549)
  ·
    refine ⟨96553572776300146275346331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 257476194070133723400923549 96553572776300146275346331)
    ·
      refine ⟨144830359164450219413019497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96553572776300146275346331 144830359164450219413019497)
      ·
        refine ⟨108622769373337664559764623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144830359164450219413019497 108622769373337664559764623)
        ·
          refine ⟨162934154060006496839646935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108622769373337664559764623 162934154060006496839646935)
          ·
            refine ⟨244401231090009745259470403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162934154060006496839646935 244401231090009745259470403)
            ·
              refine ⟨366601846635014617889205605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 244401231090009745259470403 366601846635014617889205605)
              ·
                refine ⟨68737846244065240854226051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 366601846635014617889205605 68737846244065240854226051)
                ·
                  refine ⟨103106769366097861281339077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68737846244065240854226051 103106769366097861281339077)
                  ·
                    refine ⟨19332519256143348990251077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 103106769366097861281339077 19332519256143348990251077)
                    ·
                      refine ⟨3624847360526877935672077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19332519256143348990251077 3624847360526877935672077)
                      ·
                        rfl

theorem cell23_7059365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 4, 1, 4, 4].length) (baseStart_7059365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7059365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7059365 prefixEnd_7059365 := by exact prefixLift 7059365
  have htrace : WordTrace (prefixWord ++ tailWord_7059365) baseStart_7059365 baseEnd_7059365 := by
    simpa [prefixWord, tailWord_7059365, baseEnd_7059365] using wordTrace_append hprefix tailTrace_7059365
  have hstable : (prefixWord ++ tailWord_7059365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7059365).length < 2 ^ (prefixWord ++ tailWord_7059365).sum := by decide
  have hdescent : baseEnd_7059365 < baseStart_7059365 := by decide
  rcases family_descends (prefixWord ++ tailWord_7059365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7059385 : List Nat := [1, 2, 1, 4, 2, 1, 1, 1, 1, 2, 7]
def baseStart_7059385 : Nat := 118140960795 + 7059385 * 2 ^ 59
def prefixEnd_7059385 : Nat := 4983230072969 + 3 ^ 40 * 7059385 * 2
def baseEnd_7059385 : Nat := 3624857630139967857421985

theorem tailTrace_7059385 : CollatzResearch.WordTrace tailWord_7059385 prefixEnd_7059385 3624857630139967857421985 := by
  unfold tailWord_7059385
  simp only [CollatzResearch.WordTrace]
  refine ⟨257476923530061266816651609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171651282353374177877767739 257476923530061266816651609)
  ·
    refine ⟨193107692647545950112488707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257476923530061266816651609 193107692647545950112488707)
    ·
      refine ⟨289661538971318925168733061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193107692647545950112488707 289661538971318925168733061)
      ·
        refine ⟨54311538557122298469137449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 289661538971318925168733061 54311538557122298469137449)
        ·
          refine ⟨40733653917841723851853087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54311538557122298469137449 40733653917841723851853087)
          ·
            refine ⟨61100480876762585777779631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40733653917841723851853087 61100480876762585777779631)
            ·
              refine ⟨91650721315143878666669447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61100480876762585777779631 91650721315143878666669447)
              ·
                refine ⟨137476081972715818000004171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91650721315143878666669447 137476081972715818000004171)
                ·
                  refine ⟨206214122959073727000006257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 137476081972715818000004171 206214122959073727000006257)
                  ·
                    refine ⟨154660592219305295250004693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 206214122959073727000006257 154660592219305295250004693)
                    ·
                      refine ⟨3624857630139967857421985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 154660592219305295250004693 3624857630139967857421985)
                      ·
                        rfl

theorem cell23_7059385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 1, 1, 2, 7].length) (baseStart_7059385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7059385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7059385 prefixEnd_7059385 := by exact prefixLift 7059385
  have htrace : WordTrace (prefixWord ++ tailWord_7059385) baseStart_7059385 baseEnd_7059385 := by
    simpa [prefixWord, tailWord_7059385, baseEnd_7059385] using wordTrace_append hprefix tailTrace_7059385
  have hstable : (prefixWord ++ tailWord_7059385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7059385).length < 2 ^ (prefixWord ++ tailWord_7059385).sum := by decide
  have hdescent : baseEnd_7059385 < baseStart_7059385 := by decide
  rcases family_descends (prefixWord ++ tailWord_7059385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7059402 : List Nat := [3, 1, 2, 1, 2, 1, 2, 3, 2, 3, 3]
def baseStart_7059402 : Nat := 118140960795 + 7059402 * 2 ^ 59
def prefixEnd_7059402 : Nat := 4983230072969 + 3 ^ 40 * 7059402 * 2
def baseEnd_7059402 : Nat := 3624866359311094290909407

theorem tailTrace_7059402 : CollatzResearch.WordTrace tailWord_7059402 prefixEnd_7059402 3624866359311094290909407 := by
  unfold tailWord_7059402
  simp only [CollatzResearch.WordTrace]
  refine ⟨64369385892749919680005115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171651695713999785813346973 64369385892749919680005115)
  ·
    refine ⟨96554078839124879520007673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64369385892749919680005115 96554078839124879520007673)
    ·
      refine ⟨72415559129343659640005755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96554078839124879520007673 72415559129343659640005755)
      ·
        refine ⟨108623338694015489460008633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72415559129343659640005755 108623338694015489460008633)
        ·
          refine ⟨81467504020511617095006475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108623338694015489460008633 81467504020511617095006475)
          ·
            refine ⟨122201256030767425642509713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81467504020511617095006475 122201256030767425642509713)
            ·
              refine ⟨91650942023075569231882285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122201256030767425642509713 91650942023075569231882285)
              ·
                refine ⟨34369103258653338461955857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91650942023075569231882285 34369103258653338461955857)
                ·
                  refine ⟨25776827443990003846466893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34369103258653338461955857 25776827443990003846466893)
                  ·
                    refine ⟨9666310291496251442425085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25776827443990003846466893 9666310291496251442425085)
                    ·
                      refine ⟨3624866359311094290909407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9666310291496251442425085 3624866359311094290909407)
                      ·
                        rfl

theorem cell23_7059402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 3, 2, 3, 3].length) (baseStart_7059402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7059402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7059402 prefixEnd_7059402 := by exact prefixLift 7059402
  have htrace : WordTrace (prefixWord ++ tailWord_7059402) baseStart_7059402 baseEnd_7059402 := by
    simpa [prefixWord, tailWord_7059402, baseEnd_7059402] using wordTrace_append hprefix tailTrace_7059402
  have hstable : (prefixWord ++ tailWord_7059402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7059402).length < 2 ^ (prefixWord ++ tailWord_7059402).sum := by decide
  have hdescent : baseEnd_7059402 < baseStart_7059402 := by decide
  rcases family_descends (prefixWord ++ tailWord_7059402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7059415 : List Nat := [1, 1, 3, 2, 1, 1, 3, 2, 1, 1, 7]
def baseStart_7059415 : Nat := 118140960795 + 7059415 * 2 ^ 59
def prefixEnd_7059415 : Nat := 4983230072969 + 3 ^ 40 * 7059415 * 2
def baseEnd_7059415 : Nat := 3624873034559602740046847

theorem tailTrace_7059415 : CollatzResearch.WordTrace tailWord_7059415 prefixEnd_7059415 3624873034559602740046847 := by
  unfold tailWord_7059415
  simp only [CollatzResearch.WordTrace]
  refine ⟨257478017719952581940243699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171652011813301721293495799 257478017719952581940243699)
  ·
    refine ⟨386217026579928872910365549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257478017719952581940243699 386217026579928872910365549)
    ·
      refine ⟨144831384967473327341387081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 386217026579928872910365549 144831384967473327341387081)
      ·
        refine ⟨108623538725604995506040311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144831384967473327341387081 108623538725604995506040311)
        ·
          refine ⟨162935308088407493259060467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108623538725604995506040311 162935308088407493259060467)
          ·
            refine ⟨244402962132611239888590701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162935308088407493259060467 244402962132611239888590701)
            ·
              refine ⟨91651110799729214958221513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 244402962132611239888590701 91651110799729214958221513)
              ·
                refine ⟨68738333099796911218666135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91651110799729214958221513 68738333099796911218666135)
                ·
                  refine ⟨103107499649695366827999203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68738333099796911218666135 103107499649695366827999203)
                  ·
                    refine ⟨154661249474543050241998805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 103107499649695366827999203 154661249474543050241998805)
                    ·
                      refine ⟨3624873034559602740046847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 154661249474543050241998805 3624873034559602740046847)
                      ·
                        rfl

theorem cell23_7059415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 2, 1, 1, 7].length) (baseStart_7059415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7059415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7059415 prefixEnd_7059415 := by exact prefixLift 7059415
  have htrace : WordTrace (prefixWord ++ tailWord_7059415) baseStart_7059415 baseEnd_7059415 := by
    simpa [prefixWord, tailWord_7059415, baseEnd_7059415] using wordTrace_append hprefix tailTrace_7059415
  have hstable : (prefixWord ++ tailWord_7059415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7059415).length < 2 ^ (prefixWord ++ tailWord_7059415).sum := by decide
  have hdescent : baseEnd_7059415 < baseStart_7059415 := by decide
  rcases family_descends (prefixWord ++ tailWord_7059415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7059420 : List Nat := [2, 2, 6, 1, 1, 1, 1, 2, 1, 4, 2]
def baseStart_7059420 : Nat := 118140960795 + 7059420 * 2 ^ 59
def prefixEnd_7059420 : Nat := 4983230072969 + 3 ^ 40 * 7059420 * 2
def baseEnd_7059420 : Nat := 3624875601962875220484325

theorem tailTrace_7059420 : CollatzResearch.WordTrace tailWord_7059420 prefixEnd_7059420 3624875601962875220484325 := by
  unfold tailWord_7059420
  simp only [CollatzResearch.WordTrace]
  refine ⟨128739100042467233897087857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171652133389956311862783809 128739100042467233897087857)
  ·
    refine ⟨96554325031850425422815893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128739100042467233897087857 96554325031850425422815893)
    ·
      refine ⟨4525983985867988691694495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 96554325031850425422815893 4525983985867988691694495)
      ·
        refine ⟨6788975978801983037541743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4525983985867988691694495 6788975978801983037541743)
        ·
          refine ⟨10183463968202974556312615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6788975978801983037541743 10183463968202974556312615)
          ·
            refine ⟨15275195952304461834468923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10183463968202974556312615 15275195952304461834468923)
            ·
              refine ⟨22912793928456692751703385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15275195952304461834468923 22912793928456692751703385)
              ·
                refine ⟨17184595446342519563777539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22912793928456692751703385 17184595446342519563777539)
                ·
                  refine ⟨25776893169513779345666309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17184595446342519563777539 25776893169513779345666309)
                  ·
                    refine ⟨4833167469283833627312433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25776893169513779345666309 4833167469283833627312433)
                    ·
                      refine ⟨3624875601962875220484325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4833167469283833627312433 3624875601962875220484325)
                      ·
                        rfl

theorem cell23_7059420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 2, 1, 4, 2].length) (baseStart_7059420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7059420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7059420 prefixEnd_7059420 := by exact prefixLift 7059420
  have htrace : WordTrace (prefixWord ++ tailWord_7059420) baseStart_7059420 baseEnd_7059420 := by
    simpa [prefixWord, tailWord_7059420, baseEnd_7059420] using wordTrace_append hprefix tailTrace_7059420
  have hstable : (prefixWord ++ tailWord_7059420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7059420).length < 2 ^ (prefixWord ++ tailWord_7059420).sum := by decide
  have hdescent : baseEnd_7059420 < baseStart_7059420 := by decide
  rcases family_descends (prefixWord ++ tailWord_7059420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7059465 : List Nat := [1, 2, 1, 1, 3, 1, 1, 1, 12]
def baseStart_7059465 : Nat := 118140960795 + 7059465 * 2 ^ 59
def prefixEnd_7059465 : Nat := 4983230072969 + 3 ^ 40 * 7059465 * 2
def baseEnd_7059465 : Nat := 402766523176925282713513

theorem tailTrace_7059465 : CollatzResearch.WordTrace tailWord_7059465 prefixEnd_7059465 402766523176925282713513 := by
  unfold tailWord_7059465
  simp only [CollatzResearch.WordTrace]
  refine ⟨257479841369771440479563849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171653227579847626986375899 257479841369771440479563849)
  ·
    refine ⟨193109881027328580359672887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257479841369771440479563849 193109881027328580359672887)
    ·
      refine ⟨289664821540992870539509331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193109881027328580359672887 289664821540992870539509331)
      ·
        refine ⟨434497232311489305809263997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 289664821540992870539509331 434497232311489305809263997)
        ·
          refine ⟨162936462116808489678473999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 434497232311489305809263997 162936462116808489678473999)
          ·
            refine ⟨244404693175212734517710999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162936462116808489678473999 244404693175212734517710999)
            ·
              refine ⟨366607039762819101776566499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 244404693175212734517710999 366607039762819101776566499)
              ·
                refine ⟨549910559644228652664849749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 366607039762819101776566499 549910559644228652664849749)
                ·
                  refine ⟨402766523176925282713513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 549910559644228652664849749 402766523176925282713513)
                  ·
                    rfl

theorem cell23_7059465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 12].length) (baseStart_7059465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7059465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7059465 prefixEnd_7059465 := by exact prefixLift 7059465
  have htrace : WordTrace (prefixWord ++ tailWord_7059465) baseStart_7059465 baseEnd_7059465 := by
    simpa [prefixWord, tailWord_7059465, baseEnd_7059465] using wordTrace_append hprefix tailTrace_7059465
  have hstable : (prefixWord ++ tailWord_7059465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7059465).length < 2 ^ (prefixWord ++ tailWord_7059465).sum := by decide
  have hdescent : baseEnd_7059465 < baseStart_7059465 := by decide
  rcases family_descends (prefixWord ++ tailWord_7059465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7059519 : List Nat := [1, 1, 2, 2, 3, 1, 3, 2, 1, 5, 2]
def baseStart_7059519 : Nat := 118140960795 + 7059519 * 2 ^ 59
def prefixEnd_7059519 : Nat := 4983230072969 + 3 ^ 40 * 7059519 * 2
def baseEnd_7059519 : Nat := 3624926436547670333146369

theorem tailTrace_7059519 : CollatzResearch.WordTrace tailWord_7059519 prefixEnd_7059519 3624926436547670333146369 := by
  unfold tailWord_7059519
  simp only [CollatzResearch.WordTrace]
  refine ⟨257481810911575807702029611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171654540607717205134686407 257481810911575807702029611)
  ·
    refine ⟨386222716367363711553044417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257481810911575807702029611 386222716367363711553044417)
    ·
      refine ⟨289667037275522783664783313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 386222716367363711553044417 289667037275522783664783313)
      ·
        refine ⟨217250277956642087748587485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 289667037275522783664783313 217250277956642087748587485)
        ·
          refine ⟨81468854233740782905720307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 217250277956642087748587485 81468854233740782905720307)
          ·
            refine ⟨122203281350611174358580461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81468854233740782905720307 122203281350611174358580461)
            ·
              refine ⟨45826230506479190384467673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 122203281350611174358580461 45826230506479190384467673)
              ·
                refine ⟨34369672879859392788350755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45826230506479190384467673 34369672879859392788350755)
                ·
                  refine ⟨51554509319789089182526133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34369672879859392788350755 51554509319789089182526133)
                  ·
                    refine ⟨4833235248730227110861825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51554509319789089182526133 4833235248730227110861825)
                    ·
                      refine ⟨3624926436547670333146369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4833235248730227110861825 3624926436547670333146369)
                      ·
                        rfl

theorem cell23_7059519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 2, 1, 5, 2].length) (baseStart_7059519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7059519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7059519 prefixEnd_7059519 := by exact prefixLift 7059519
  have htrace : WordTrace (prefixWord ++ tailWord_7059519) baseStart_7059519 baseEnd_7059519 := by
    simpa [prefixWord, tailWord_7059519, baseEnd_7059519] using wordTrace_append hprefix tailTrace_7059519
  have hstable : (prefixWord ++ tailWord_7059519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7059519).length < 2 ^ (prefixWord ++ tailWord_7059519).sum := by decide
  have hdescent : baseEnd_7059519 < baseStart_7059519 := by decide
  rcases family_descends (prefixWord ++ tailWord_7059519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7059526 : List Nat := [6, 1, 1, 1, 1, 1, 1, 1, 2, 5, 3]
def baseStart_7059526 : Nat := 118140960795 + 7059526 * 2 ^ 59
def prefixEnd_7059526 : Nat := 4983230072969 + 3 ^ 40 * 7059526 * 2
def baseEnd_7059526 : Nat := 3624930030912251805758837

theorem tailTrace_7059526 : CollatzResearch.WordTrace tailWord_7059526 prefixEnd_7059526 3624930030912251805758837 := by
  unfold tailWord_7059526
  simp only [CollatzResearch.WordTrace]
  refine ⟨8046314569454701496797951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 171654710815033631931689621 8046314569454701496797951)
  ·
    refine ⟨12069471854182052245196927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8046314569454701496797951 12069471854182052245196927)
    ·
      refine ⟨18104207781273078367795391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12069471854182052245196927 18104207781273078367795391)
      ·
        refine ⟨27156311671909617551693087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18104207781273078367795391 27156311671909617551693087)
        ·
          refine ⟨40734467507864426327539631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27156311671909617551693087 40734467507864426327539631)
          ·
            refine ⟨61101701261796639491309447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40734467507864426327539631 61101701261796639491309447)
            ·
              refine ⟨91652551892694959236964171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61101701261796639491309447 91652551892694959236964171)
              ·
                refine ⟨137478827839042438855446257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91652551892694959236964171 137478827839042438855446257)
                ·
                  refine ⟨103109120879281829141584693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 137478827839042438855446257 103109120879281829141584693)
                  ·
                    refine ⟨9666480082432671482023565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 103109120879281829141584693 9666480082432671482023565)
                    ·
                      refine ⟨3624930030912251805758837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9666480082432671482023565 3624930030912251805758837)
                      ·
                        rfl

theorem cell23_7059526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 1, 2, 5, 3].length) (baseStart_7059526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7059526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7059526 prefixEnd_7059526 := by exact prefixLift 7059526
  have htrace : WordTrace (prefixWord ++ tailWord_7059526) baseStart_7059526 baseEnd_7059526 := by
    simpa [prefixWord, tailWord_7059526, baseEnd_7059526] using wordTrace_append hprefix tailTrace_7059526
  have hstable : (prefixWord ++ tailWord_7059526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7059526).length < 2 ^ (prefixWord ++ tailWord_7059526).sum := by decide
  have hdescent : baseEnd_7059526 < baseStart_7059526 := by decide
  rcases family_descends (prefixWord ++ tailWord_7059526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7059529 : List Nat := [1, 2, 1, 1, 2, 2, 6, 2, 1, 5]
def baseStart_7059529 : Nat := 118140960795 + 7059529 * 2 ^ 59
def prefixEnd_7059529 : Nat := 4983230072969 + 3 ^ 40 * 7059529 * 2
def baseEnd_7059529 : Nat := 1208310523784738431340441

theorem tailTrace_7059529 : CollatzResearch.WordTrace tailWord_7059529 prefixEnd_7059529 1208310523784738431340441 := by
  unfold tailWord_7059529
  simp only [CollatzResearch.WordTrace]
  refine ⟨257482175641539579409893641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171654783761026386273262427 257482175641539579409893641)
  ·
    refine ⟨193111631731154684557420231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257482175641539579409893641 193111631731154684557420231)
    ·
      refine ⟨289667447596732026836130347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193111631731154684557420231 289667447596732026836130347)
      ·
        refine ⟨434501171395098040254195521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 289667447596732026836130347 434501171395098040254195521)
        ·
          refine ⟨325875878546323530190646641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 434501171395098040254195521 325875878546323530190646641)
          ·
            refine ⟨244406908909742647642984981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 325875878546323530190646641 244406908909742647642984981)
            ·
              refine ⟨11456573855144186608264921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 244406908909742647642984981 11456573855144186608264921)
              ·
                refine ⟨8592430391358139956198691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11456573855144186608264921 8592430391358139956198691)
                ·
                  refine ⟨12888645587037209934298037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8592430391358139956198691 12888645587037209934298037)
                  ·
                    refine ⟨1208310523784738431340441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12888645587037209934298037 1208310523784738431340441)
                    ·
                      rfl

theorem cell23_7059529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 6, 2, 1, 5].length) (baseStart_7059529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7059529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7059529 prefixEnd_7059529 := by exact prefixLift 7059529
  have htrace : WordTrace (prefixWord ++ tailWord_7059529) baseStart_7059529 baseEnd_7059529 := by
    simpa [prefixWord, tailWord_7059529, baseEnd_7059529] using wordTrace_append hprefix tailTrace_7059529
  have hstable : (prefixWord ++ tailWord_7059529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7059529).length < 2 ^ (prefixWord ++ tailWord_7059529).sum := by decide
  have hdescent : baseEnd_7059529 < baseStart_7059529 := by decide
  rcases family_descends (prefixWord ++ tailWord_7059529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7059543 : List Nat := [1, 1, 3, 2, 2, 1, 5, 3, 1, 1, 3]
def baseStart_7059543 : Nat := 118140960795 + 7059543 * 2 ^ 59
def prefixEnd_7059543 : Nat := 4983230072969 + 3 ^ 40 * 7059543 * 2
def baseEnd_7059543 : Nat := 3624938760083378239246259

theorem tailTrace_7059543 : CollatzResearch.WordTrace tailWord_7059543 prefixEnd_7059543 3624938760083378239246259 := by
  unfold tailWord_7059543
  simp only [CollatzResearch.WordTrace]
  refine ⟨257482686263488859800903283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171655124175659239867268855 257482686263488859800903283)
  ·
    refine ⟨386224029395233289701354925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257482686263488859800903283 386224029395233289701354925)
    ·
      refine ⟨144834011023212483638008097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 386224029395233289701354925 144834011023212483638008097)
      ·
        refine ⟨108625508267409362728506073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144834011023212483638008097 108625508267409362728506073)
        ·
          refine ⟨81469131200557022046379555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108625508267409362728506073 81469131200557022046379555)
          ·
            refine ⟨122203696800835533069569333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81469131200557022046379555 122203696800835533069569333)
            ·
              refine ⟨11456596575078331225272125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 122203696800835533069569333 11456596575078331225272125)
              ·
                refine ⟨4296223715654374209477047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11456596575078331225272125 4296223715654374209477047)
                ·
                  refine ⟨6444335573481561314215571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4296223715654374209477047 6444335573481561314215571)
                  ·
                    refine ⟨9666503360222341971323357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6444335573481561314215571 9666503360222341971323357)
                    ·
                      refine ⟨3624938760083378239246259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9666503360222341971323357 3624938760083378239246259)
                      ·
                        rfl

theorem cell23_7059543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 5, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 5, 3, 1, 1, 3].length) (baseStart_7059543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7059543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7059543 prefixEnd_7059543 := by exact prefixLift 7059543
  have htrace : WordTrace (prefixWord ++ tailWord_7059543) baseStart_7059543 baseEnd_7059543 := by
    simpa [prefixWord, tailWord_7059543, baseEnd_7059543] using wordTrace_append hprefix tailTrace_7059543
  have hstable : (prefixWord ++ tailWord_7059543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7059543).length < 2 ^ (prefixWord ++ tailWord_7059543).sum := by decide
  have hdescent : baseEnd_7059543 < baseStart_7059543 := by decide
  rcases family_descends (prefixWord ++ tailWord_7059543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7059559 : List Nat := [1, 1, 5, 1, 1, 2, 1, 3, 4, 4]
def baseStart_7059559 : Nat := 118140960795 + 7059559 * 2 ^ 59
def prefixEnd_7059559 : Nat := 4983230072969 + 3 ^ 40 * 7059559 * 2
def baseEnd_7059559 : Nat := 1208315658591283392215395

theorem tailTrace_7059559 : CollatzResearch.WordTrace tailWord_7059559 prefixEnd_7059559 1208315658591283392215395 := by
  unfold tailWord_7059559
  simp only [CollatzResearch.WordTrace]
  refine ⟨257483269831430894533485731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171655513220953929688990487 257483269831430894533485731)
  ·
    refine ⟨386224904747146341800228597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257483269831430894533485731 386224904747146341800228597)
    ·
      refine ⟨36208584820044969543771431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 386224904747146341800228597 36208584820044969543771431)
      ·
        refine ⟨54312877230067454315657147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36208584820044969543771431 54312877230067454315657147)
        ·
          refine ⟨81469315845101181473485721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54312877230067454315657147 81469315845101181473485721)
          ·
            refine ⟨61101986883825886105114291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81469315845101181473485721 61101986883825886105114291)
            ·
              refine ⟨91652980325738829157671437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61101986883825886105114291 91652980325738829157671437)
              ·
                refine ⟨34369867622152060934126789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91652980325738829157671437 34369867622152060934126789)
                ·
                  refine ⟨6444350179153511425148773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34369867622152060934126789 6444350179153511425148773)
                  ·
                    refine ⟨1208315658591283392215395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6444350179153511425148773 1208315658591283392215395)
                    ·
                      rfl

theorem cell23_7059559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 3, 4, 4].length) (baseStart_7059559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7059559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7059559 prefixEnd_7059559 := by exact prefixLift 7059559
  have htrace : WordTrace (prefixWord ++ tailWord_7059559) baseStart_7059559 baseEnd_7059559 := by
    simpa [prefixWord, tailWord_7059559, baseEnd_7059559] using wordTrace_append hprefix tailTrace_7059559
  have hstable : (prefixWord ++ tailWord_7059559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7059559).length < 2 ^ (prefixWord ++ tailWord_7059559).sum := by decide
  have hdescent : baseEnd_7059559 < baseStart_7059559 := by decide
  rcases family_descends (prefixWord ++ tailWord_7059559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7059569 : List Nat := [1, 2, 2, 2, 1, 1, 4, 2, 3, 2, 3]
def baseStart_7059569 : Nat := 118140960795 + 7059569 * 2 ^ 59
def prefixEnd_7059569 : Nat := 4983230072969 + 3 ^ 40 * 7059569 * 2
def baseEnd_7059569 : Nat := 3624952110580395137521139

theorem tailTrace_7059569 : CollatzResearch.WordTrace tailWord_7059569 prefixEnd_7059569 3624952110580395137521139 := by
  unfold tailWord_7059569
  simp only [CollatzResearch.WordTrace]
  refine ⟨257483634561394666241349761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171655756374263110827566507 257483634561394666241349761)
  ·
    refine ⟨193112725921045999681012321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257483634561394666241349761 193112725921045999681012321)
    ·
      refine ⟨144834544440784499760759241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193112725921045999681012321 144834544440784499760759241)
      ·
        refine ⟨108625908330588374820569431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144834544440784499760759241 108625908330588374820569431)
        ·
          refine ⟨162938862495882562230854147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108625908330588374820569431 162938862495882562230854147)
          ·
            refine ⟨244408293743823843346281221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162938862495882562230854147 244408293743823843346281221)
            ·
              refine ⟨45826555076966970627427729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 244408293743823843346281221 45826555076966970627427729)
              ·
                refine ⟨34369916307725227970570797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45826555076966970627427729 34369916307725227970570797)
                ·
                  refine ⟨12888718615396960488964049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34369916307725227970570797 12888718615396960488964049)
                  ·
                    refine ⟨9666538961547720366723037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12888718615396960488964049 9666538961547720366723037)
                    ·
                      refine ⟨3624952110580395137521139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9666538961547720366723037 3624952110580395137521139)
                      ·
                        rfl

theorem cell23_7059569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 2, 3, 2, 3].length) (baseStart_7059569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7059569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7059569 prefixEnd_7059569 := by exact prefixLift 7059569
  have htrace : WordTrace (prefixWord ++ tailWord_7059569) baseStart_7059569 baseEnd_7059569 := by
    simpa [prefixWord, tailWord_7059569, baseEnd_7059569] using wordTrace_append hprefix tailTrace_7059569
  have hstable : (prefixWord ++ tailWord_7059569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7059569).length < 2 ^ (prefixWord ++ tailWord_7059569).sum := by decide
  have hdescent : baseEnd_7059569 < baseStart_7059569 := by decide
  rcases family_descends (prefixWord ++ tailWord_7059569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7059617 : List Nat := [1, 2, 3, 3, 1, 2, 4, 2, 1, 2, 2]
def baseStart_7059617 : Nat := 118140960795 + 7059617 * 2 ^ 59
def prefixEnd_7059617 : Nat := 4983230072969 + 3 ^ 40 * 7059617 * 2
def baseEnd_7059617 : Nat := 3624976757651810949720919

theorem tailTrace_7059617 : CollatzResearch.WordTrace tailWord_7059617 prefixEnd_7059617 3624976757651810949720919 := by
  unfold tailWord_7059617
  simp only [CollatzResearch.WordTrace]
  refine ⟨257485385265220770439097105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171656923510147180292731403 257485385265220770439097105)
  ·
    refine ⟨193114038948915577829322829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257485385265220770439097105 193114038948915577829322829)
    ·
      refine ⟨72417764605843341685996061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 193114038948915577829322829 72417764605843341685996061)
      ·
        refine ⟨27156661727191253132248523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72417764605843341685996061 27156661727191253132248523)
        ·
          refine ⟨40734992590786879698372785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27156661727191253132248523 40734992590786879698372785)
          ·
            refine ⟨30551244443090159773779589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40734992590786879698372785 30551244443090159773779589)
            ·
              refine ⟨5728358333079404957583673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30551244443090159773779589 5728358333079404957583673)
              ·
                refine ⟨4296268749809553718187755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5728358333079404957583673 4296268749809553718187755)
                ·
                  refine ⟨6444403124714330577281633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4296268749809553718187755 6444403124714330577281633)
                  ·
                    refine ⟨4833302343535747932961225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6444403124714330577281633 4833302343535747932961225)
                    ·
                      refine ⟨3624976757651810949720919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4833302343535747932961225 3624976757651810949720919)
                      ·
                        rfl

theorem cell23_7059617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 4, 2, 1, 2, 2].length) (baseStart_7059617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7059617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7059617 prefixEnd_7059617 := by exact prefixLift 7059617
  have htrace : WordTrace (prefixWord ++ tailWord_7059617) baseStart_7059617 baseEnd_7059617 := by
    simpa [prefixWord, tailWord_7059617, baseEnd_7059617] using wordTrace_append hprefix tailTrace_7059617
  have hstable : (prefixWord ++ tailWord_7059617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7059617).length < 2 ^ (prefixWord ++ tailWord_7059617).sum := by decide
  have hdescent : baseEnd_7059617 < baseStart_7059617 := by decide
  rcases family_descends (prefixWord ++ tailWord_7059617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7059623 : List Nat := [1, 1, 6, 2, 3, 1, 1, 8]
def baseStart_7059623 : Nat := 118140960795 + 7059623 * 2 ^ 59
def prefixEnd_7059623 : Nat := 4983230072969 + 3 ^ 40 * 7059623 * 2
def baseEnd_7059623 : Nat := 134258512538360663935033

theorem tailTrace_7059623 : CollatzResearch.WordTrace tailWord_7059623 prefixEnd_7059623 134258512538360663935033 := by
  unfold tailWord_7059623
  simp only [CollatzResearch.WordTrace]
  refine ⟨257485604103199033463815523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171657069402132688975877015 257485604103199033463815523)
  ·
    refine ⟨386228406154798550195723285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257485604103199033463815523 386228406154798550195723285)
    ·
      refine ⟨18104456538506182040424529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 386228406154798550195723285 18104456538506182040424529)
      ·
        refine ⟨13578342403879636530318397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18104456538506182040424529 13578342403879636530318397)
        ·
          refine ⟨5091878401454863698869399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13578342403879636530318397 5091878401454863698869399)
          ·
            refine ⟨7637817602182295548304099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5091878401454863698869399 7637817602182295548304099)
            ·
              refine ⟨11456726403273443322456149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7637817602182295548304099 11456726403273443322456149)
              ·
                refine ⟨134258512538360663935033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11456726403273443322456149 134258512538360663935033)
                ·
                  rfl

theorem cell23_7059623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 1, 8].length) (baseStart_7059623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7059623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7059623 prefixEnd_7059623 := by exact prefixLift 7059623
  have htrace : WordTrace (prefixWord ++ tailWord_7059623) baseStart_7059623 baseEnd_7059623 := by
    simpa [prefixWord, tailWord_7059623, baseEnd_7059623] using wordTrace_append hprefix tailTrace_7059623
  have hstable : (prefixWord ++ tailWord_7059623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7059623).length < 2 ^ (prefixWord ++ tailWord_7059623).sum := by decide
  have hdescent : baseEnd_7059623 < baseStart_7059623 := by decide
  rcases family_descends (prefixWord ++ tailWord_7059623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7059630 : List Nat := [4, 1, 4, 2, 1, 1, 2, 1, 1, 2, 4]
def baseStart_7059630 : Nat := 118140960795 + 7059630 * 2 ^ 59
def prefixEnd_7059630 : Nat := 4983230072969 + 3 ^ 40 * 7059630 * 2
def baseEnd_7059630 : Nat := 3624983432900319398858359

theorem tailTrace_7059630 : CollatzResearch.WordTrace tailWord_7059630 prefixEnd_7059630 3624983432900319398858359 := by
  unfold tailWord_7059630
  simp only [CollatzResearch.WordTrace]
  refine ⟨32185732426771709207415043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 171657239609449115772880229 32185732426771709207415043)
  ·
    refine ⟨48278598640157563811122565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32185732426771709207415043 48278598640157563811122565)
    ·
      refine ⟨9052237245029543214585481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48278598640157563811122565 9052237245029543214585481)
      ·
        refine ⟨6789177933772157410939111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9052237245029543214585481 6789177933772157410939111)
        ·
          refine ⟨10183766900658236116408667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6789177933772157410939111 10183766900658236116408667)
          ·
            refine ⟨15275650350987354174613001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10183766900658236116408667 15275650350987354174613001)
            ·
              refine ⟨11456737763240515630959751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15275650350987354174613001 11456737763240515630959751)
              ·
                refine ⟨17185106644860773446439627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11456737763240515630959751 17185106644860773446439627)
                ·
                  refine ⟨25777659967291160169659441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17185106644860773446439627 25777659967291160169659441)
                  ·
                    refine ⟨19333244975468370127244581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25777659967291160169659441 19333244975468370127244581)
                    ·
                      refine ⟨3624983432900319398858359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19333244975468370127244581 3624983432900319398858359)
                      ·
                        rfl

theorem cell23_7059630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_7059630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7059630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7059630 prefixEnd_7059630 := by exact prefixLift 7059630
  have htrace : WordTrace (prefixWord ++ tailWord_7059630) baseStart_7059630 baseEnd_7059630 := by
    simpa [prefixWord, tailWord_7059630, baseEnd_7059630] using wordTrace_append hprefix tailTrace_7059630
  have hstable : (prefixWord ++ tailWord_7059630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7059630).length < 2 ^ (prefixWord ++ tailWord_7059630).sum := by decide
  have hdescent : baseEnd_7059630 < baseStart_7059630 := by decide
  rcases family_descends (prefixWord ++ tailWord_7059630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7059633 : List Nat := [1, 2, 2, 5, 2, 1, 2, 1, 1, 3, 3]
def baseStart_7059633 : Nat := 118140960795 + 7059633 * 2 ^ 59
def prefixEnd_7059633 : Nat := 4983230072969 + 3 ^ 40 * 7059633 * 2
def baseEnd_7059633 : Nat := 3624984973342282887120845

theorem tailTrace_7059633 : CollatzResearch.WordTrace tailWord_7059633 prefixEnd_7059633 3624984973342282887120845 := by
  unfold tailWord_7059633
  simp only [CollatzResearch.WordTrace]
  refine ⟨257485968833162805171679553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171657312555441870114453035 257485968833162805171679553)
  ·
    refine ⟨193114476624872103878759665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257485968833162805171679553 193114476624872103878759665)
    ·
      refine ⟨144835857468654077909069749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193114476624872103878759665 144835857468654077909069749)
      ·
        refine ⟨13578361637686319803975289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 144835857468654077909069749 13578361637686319803975289)
        ·
          refine ⟨10183771228264739852981467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13578361637686319803975289 10183771228264739852981467)
          ·
            refine ⟨15275656842397109779472201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10183771228264739852981467 15275656842397109779472201)
            ·
              refine ⟨11456742631797832334604151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15275656842397109779472201 11456742631797832334604151)
              ·
                refine ⟨17185113947696748501906227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11456742631797832334604151 17185113947696748501906227)
                ·
                  refine ⟨25777670921545122752859341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17185113947696748501906227 25777670921545122752859341)
                  ·
                    refine ⟨9666626595579421032322253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25777670921545122752859341 9666626595579421032322253)
                    ·
                      refine ⟨3624984973342282887120845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9666626595579421032322253 3624984973342282887120845)
                      ·
                        rfl

theorem cell23_7059633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 2, 1, 1, 3, 3].length) (baseStart_7059633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7059633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7059633 prefixEnd_7059633 := by exact prefixLift 7059633
  have htrace : WordTrace (prefixWord ++ tailWord_7059633) baseStart_7059633 baseEnd_7059633 := by
    simpa [prefixWord, tailWord_7059633, baseEnd_7059633] using wordTrace_append hprefix tailTrace_7059633
  have hstable : (prefixWord ++ tailWord_7059633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7059633).length < 2 ^ (prefixWord ++ tailWord_7059633).sum := by decide
  have hdescent : baseEnd_7059633 < baseStart_7059633 := by decide
  rcases family_descends (prefixWord ++ tailWord_7059633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7059650 : List Nat := [3, 5, 1, 1, 1, 1, 2, 2, 1, 3, 3]
def baseStart_7059650 : Nat := 118140960795 + 7059650 * 2 ^ 59
def prefixEnd_7059650 : Nat := 4983230072969 + 3 ^ 40 * 7059650 * 2
def baseEnd_7059650 : Nat := 3624993702513409320608267

theorem tailTrace_7059650 : CollatzResearch.WordTrace tailWord_7059650 prefixEnd_7059650 3624993702513409320608267 := by
  unfold tailWord_7059650
  simp only [CollatzResearch.WordTrace]
  refine ⟨64371647218525304268762101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171657725916067478050032269 64371647218525304268762101)
  ·
    refine ⟨6034841926736747275196447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 64371647218525304268762101 6034841926736747275196447)
    ·
      refine ⟨9052262890105120912794671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6034841926736747275196447 9052262890105120912794671)
      ·
        refine ⟨13578394335157681369192007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9052262890105120912794671 13578394335157681369192007)
        ·
          refine ⟨20367591502736522053788011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13578394335157681369192007 20367591502736522053788011)
          ·
            refine ⟨30551387254104783080682017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20367591502736522053788011 30551387254104783080682017)
            ·
              refine ⟨22913540440578587310511513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30551387254104783080682017 22913540440578587310511513)
              ·
                refine ⟨17185155330433940482883635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22913540440578587310511513 17185155330433940482883635)
                ·
                  refine ⟨25777732995650910724325453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17185155330433940482883635 25777732995650910724325453)
                  ·
                    refine ⟨9666649873369091521622045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25777732995650910724325453 9666649873369091521622045)
                    ·
                      refine ⟨3624993702513409320608267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9666649873369091521622045 3624993702513409320608267)
                      ·
                        rfl

theorem cell23_7059650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 2, 1, 3, 3].length) (baseStart_7059650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7059650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7059650 prefixEnd_7059650 := by exact prefixLift 7059650
  have htrace : WordTrace (prefixWord ++ tailWord_7059650) baseStart_7059650 baseEnd_7059650 := by
    simpa [prefixWord, tailWord_7059650, baseEnd_7059650] using wordTrace_append hprefix tailTrace_7059650
  have hstable : (prefixWord ++ tailWord_7059650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7059650).length < 2 ^ (prefixWord ++ tailWord_7059650).sum := by decide
  have hdescent : baseEnd_7059650 < baseStart_7059650 := by decide
  rcases family_descends (prefixWord ++ tailWord_7059650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7059709 : List Nat := [1, 4, 1, 1, 1, 1, 1, 2, 6, 5]
def baseStart_7059709 : Nat := 118140960795 + 7059709 * 2 ^ 59
def prefixEnd_7059709 : Nat := 4983230072969 + 3 ^ 40 * 7059709 * 2
def baseEnd_7059709 : Nat := 1208341332624008196590165

theorem tailTrace_7059709 : CollatzResearch.WordTrace tailWord_7059709 prefixEnd_7059709 1208341332624008196590165 := by
  unfold tailWord_7059709
  simp only [CollatzResearch.WordTrace]
  refine ⟨257488740780887470151446181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171659160520591646767630787 257488740780887470151446181)
  ·
    refine ⟨48279138896416400653396159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 257488740780887470151446181 48279138896416400653396159)
    ·
      refine ⟨72418708344624600980094239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48279138896416400653396159 72418708344624600980094239)
      ·
        refine ⟨108628062516936901470141359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72418708344624600980094239 108628062516936901470141359)
        ·
          refine ⟨162942093775405352205212039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108628062516936901470141359 162942093775405352205212039)
          ·
            refine ⟨244413140663108028307818059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162942093775405352205212039 244413140663108028307818059)
            ·
              refine ⟨366619710994662042461727089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 244413140663108028307818059 366619710994662042461727089)
              ·
                refine ⟨274964783245996531846295317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 366619710994662042461727089 274964783245996531846295317)
                ·
                  refine ⟨12888974214656087430295093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 274964783245996531846295317 12888974214656087430295093)
                  ·
                    refine ⟨1208341332624008196590165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12888974214656087430295093 1208341332624008196590165)
                    ·
                      rfl

theorem cell23_7059709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 2, 6, 5].length) (baseStart_7059709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7059709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7059709 prefixEnd_7059709 := by exact prefixLift 7059709
  have htrace : WordTrace (prefixWord ++ tailWord_7059709) baseStart_7059709 baseEnd_7059709 := by
    simpa [prefixWord, tailWord_7059709, baseEnd_7059709] using wordTrace_append hprefix tailTrace_7059709
  have hstable : (prefixWord ++ tailWord_7059709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7059709).length < 2 ^ (prefixWord ++ tailWord_7059709).sum := by decide
  have hdescent : baseEnd_7059709 < baseStart_7059709 := by decide
  rcases family_descends (prefixWord ++ tailWord_7059709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7059726 : List Nat := [4, 1, 1, 2, 1, 2, 3, 2, 2, 5]
def baseStart_7059726 : Nat := 118140960795 + 7059726 * 2 ^ 59
def prefixEnd_7059726 : Nat := 4983230072969 + 3 ^ 40 * 7059726 * 2
def baseEnd_7059726 : Nat := 1208344242347717007752639

theorem tailTrace_7059726 : CollatzResearch.WordTrace tailWord_7059726 prefixEnd_7059726 1208344242347717007752639 := by
  unfold tailWord_7059726
  simp only [CollatzResearch.WordTrace]
  refine ⟨32186170102728235256851879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 171659573881217254703210021 32186170102728235256851879)
  ·
    refine ⟨48279255154092352885277819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32186170102728235256851879 48279255154092352885277819)
    ·
      refine ⟨72418882731138529327916729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48279255154092352885277819 72418882731138529327916729)
      ·
        refine ⟨54314162048353896995937547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72418882731138529327916729 54314162048353896995937547)
        ·
          refine ⟨81471243072530845493906321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54314162048353896995937547 81471243072530845493906321)
          ·
            refine ⟨61103432304398134120429741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81471243072530845493906321 61103432304398134120429741)
            ·
              refine ⟨22913787114149300295161153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61103432304398134120429741 22913787114149300295161153)
              ·
                refine ⟨17185340335611975221370865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22913787114149300295161153 17185340335611975221370865)
                ·
                  refine ⟨12889005251708981416028149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17185340335611975221370865 12889005251708981416028149)
                  ·
                    refine ⟨1208344242347717007752639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12889005251708981416028149 1208344242347717007752639)
                    ·
                      rfl

theorem cell23_7059726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 2, 2, 5].length) (baseStart_7059726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7059726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7059726 prefixEnd_7059726 := by exact prefixLift 7059726
  have htrace : WordTrace (prefixWord ++ tailWord_7059726) baseStart_7059726 baseEnd_7059726 := by
    simpa [prefixWord, tailWord_7059726, baseEnd_7059726] using wordTrace_append hprefix tailTrace_7059726
  have hstable : (prefixWord ++ tailWord_7059726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7059726).length < 2 ^ (prefixWord ++ tailWord_7059726).sum := by decide
  have hdescent : baseEnd_7059726 < baseStart_7059726 := by decide
  rcases family_descends (prefixWord ++ tailWord_7059726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7059741 : List Nat := [1, 4, 2, 3, 3, 1, 2, 1, 2, 2, 2]
def baseStart_7059741 : Nat := 118140960795 + 7059741 * 2 ^ 59
def prefixEnd_7059741 : Nat := 4983230072969 + 3 ^ 40 * 7059741 * 2
def baseEnd_7059741 : Nat := 3625040429252968464570349

theorem tailTrace_7059741 : CollatzResearch.WordTrace tailWord_7059741 prefixEnd_7059741 3625040429252968464570349 := by
  unfold tailWord_7059741
  simp only [CollatzResearch.WordTrace]
  refine ⟨257489907916771539616611077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171659938611181026411074051 257489907916771539616611077)
  ·
    refine ⟨48279357734394663678114577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 257489907916771539616611077 48279357734394663678114577)
    ·
      refine ⟨36209518300795997758585933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48279357734394663678114577 36209518300795997758585933)
      ·
        refine ⟨13578569362798499159469725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36209518300795997758585933 13578569362798499159469725)
        ·
          refine ⟨5091963511049437184801147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13578569362798499159469725 5091963511049437184801147)
          ·
            refine ⟨7637945266574155777201721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5091963511049437184801147 7637945266574155777201721)
            ·
              refine ⟨5728458949930616832901291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7637945266574155777201721 5728458949930616832901291)
              ·
                refine ⟨8592688424895925249351937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5728458949930616832901291 8592688424895925249351937)
                ·
                  refine ⟨6444516318671943937013953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8592688424895925249351937 6444516318671943937013953)
                  ·
                    refine ⟨4833387239003957952760465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6444516318671943937013953 4833387239003957952760465)
                    ·
                      refine ⟨3625040429252968464570349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4833387239003957952760465 3625040429252968464570349)
                      ·
                        rfl

theorem cell23_7059741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 2, 1, 2, 2, 2].length) (baseStart_7059741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7059741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7059741 prefixEnd_7059741 := by exact prefixLift 7059741
  have htrace : WordTrace (prefixWord ++ tailWord_7059741) baseStart_7059741 baseEnd_7059741 := by
    simpa [prefixWord, tailWord_7059741, baseEnd_7059741] using wordTrace_append hprefix tailTrace_7059741
  have hstable : (prefixWord ++ tailWord_7059741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7059741).length < 2 ^ (prefixWord ++ tailWord_7059741).sum := by decide
  have hdescent : baseEnd_7059741 < baseStart_7059741 := by decide
  rcases family_descends (prefixWord ++ tailWord_7059741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7059756 : List Nat := [2, 2, 1, 1, 1, 3, 2, 4, 3, 4]
def baseStart_7059756 : Nat := 118140960795 + 7059756 * 2 ^ 59
def prefixEnd_7059756 : Nat := 4983230072969 + 3 ^ 40 * 7059756 * 2
def baseEnd_7059756 : Nat := 1208349377154261968627593

theorem tailTrace_7059756 : CollatzResearch.WordTrace tailWord_7059756 prefixEnd_7059756 1208349377154261968627593 := by
  unfold tailWord_7059756
  simp only [CollatzResearch.WordTrace]
  refine ⟨128745227505858598589203561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171660303341144798118938081 128745227505858598589203561)
  ·
    refine ⟨96558920629393948941902671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128745227505858598589203561 96558920629393948941902671)
    ·
      refine ⟨144838380944090923412854007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96558920629393948941902671 144838380944090923412854007)
      ·
        refine ⟨217257571416136385119281011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144838380944090923412854007 217257571416136385119281011)
        ·
          refine ⟨325886357124204577678921517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217257571416136385119281011 325886357124204577678921517)
          ·
            refine ⟨122207383921576716629595569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 325886357124204577678921517 122207383921576716629595569)
            ·
              refine ⟨91655537941182537472196677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122207383921576716629595569 91655537941182537472196677)
              ·
                refine ⟨17185413363971725776036877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 91655537941182537472196677 17185413363971725776036877)
                ·
                  refine ⟨6444530011489397166013829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17185413363971725776036877 6444530011489397166013829)
                  ·
                    refine ⟨1208349377154261968627593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6444530011489397166013829 1208349377154261968627593)
                    ·
                      rfl

theorem cell23_7059756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 4].length) (baseStart_7059756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7059756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7059756 prefixEnd_7059756 := by exact prefixLift 7059756
  have htrace : WordTrace (prefixWord ++ tailWord_7059756) baseStart_7059756 baseEnd_7059756 := by
    simpa [prefixWord, tailWord_7059756, baseEnd_7059756] using wordTrace_append hprefix tailTrace_7059756
  have hstable : (prefixWord ++ tailWord_7059756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7059756).length < 2 ^ (prefixWord ++ tailWord_7059756).sum := by decide
  have hdescent : baseEnd_7059756 < baseStart_7059756 := by decide
  rcases family_descends (prefixWord ++ tailWord_7059756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7059759 : List Nat := [1, 1, 2, 1, 2, 1, 4, 1, 2, 4, 4]
def baseStart_7059759 : Nat := 118140960795 + 7059759 * 2 ^ 59
def prefixEnd_7059759 : Nat := 4983230072969 + 3 ^ 40 * 7059759 * 2
def baseEnd_7059759 : Nat := 3625049671904749394145265

theorem tailTrace_7059759 : CollatzResearch.WordTrace tailWord_7059759 prefixEnd_7059759 3625049671904749394145265 := by
  unfold tailWord_7059759
  simp only [CollatzResearch.WordTrace]
  refine ⟨257490564430706328690766331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171660376287137552460510887 257490564430706328690766331)
  ·
    refine ⟨386235846646059493036149497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257490564430706328690766331 386235846646059493036149497)
    ·
      refine ⟨289676884984544619777112123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 386235846646059493036149497 289676884984544619777112123)
      ·
        refine ⟨434515327476816929665668185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 289676884984544619777112123 434515327476816929665668185)
        ·
          refine ⟨325886495607612697249251139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 434515327476816929665668185 325886495607612697249251139)
          ·
            refine ⟨488829743411419045873876709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 325886495607612697249251139 488829743411419045873876709)
            ·
              refine ⟨91655576889641071101351883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 488829743411419045873876709 91655576889641071101351883)
              ·
                refine ⟨137483365334461606652027825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91655576889641071101351883 137483365334461606652027825)
                ·
                  refine ⟨103112524000846204989020869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 137483365334461606652027825 103112524000846204989020869)
                  ·
                    refine ⟨19333598250158663435441413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 103112524000846204989020869 19333598250158663435441413)
                    ·
                      refine ⟨3625049671904749394145265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19333598250158663435441413 3625049671904749394145265)
                      ·
                        rfl

theorem cell23_7059759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 1, 2, 4, 4].length) (baseStart_7059759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7059759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7059759 prefixEnd_7059759 := by exact prefixLift 7059759
  have htrace : WordTrace (prefixWord ++ tailWord_7059759) baseStart_7059759 baseEnd_7059759 := by
    simpa [prefixWord, tailWord_7059759, baseEnd_7059759] using wordTrace_append hprefix tailTrace_7059759
  have hstable : (prefixWord ++ tailWord_7059759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7059759).length < 2 ^ (prefixWord ++ tailWord_7059759).sum := by decide
  have hdescent : baseEnd_7059759 < baseStart_7059759 := by decide
  rcases family_descends (prefixWord ++ tailWord_7059759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7059813 : List Nat := [1, 3, 1, 3, 1, 3, 1, 1, 5, 1, 3]
def baseStart_7059813 : Nat := 118140960795 + 7059813 * 2 ^ 59
def prefixEnd_7059813 : Nat := 4983230072969 + 3 ^ 40 * 7059813 * 2
def baseEnd_7059813 : Nat := 3625077399860092182870017

theorem tailTrace_7059813 : CollatzResearch.WordTrace tailWord_7059813 prefixEnd_7059813 3625077399860092182870017 := by
  unfold tailWord_7059813
  simp only [CollatzResearch.WordTrace]
  refine ⟨257492533972510695913232093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171661689315007130608821395 257492533972510695913232093)
  ·
    refine ⟨96559700239691510967462035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 257492533972510695913232093 96559700239691510967462035)
    ·
      refine ⟨144839550359537266451193053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96559700239691510967462035 144839550359537266451193053)
      ·
        refine ⟨54314831384826474919197395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144839550359537266451193053 54314831384826474919197395)
        ·
          refine ⟨81472247077239712378796093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54314831384826474919197395 81472247077239712378796093)
          ·
            refine ⟨30552092653964892142048535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81472247077239712378796093 30552092653964892142048535)
            ·
              refine ⟨45828138980947338213072803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30552092653964892142048535 45828138980947338213072803)
              ·
                refine ⟨68742208471421007319609205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45828138980947338213072803 68742208471421007319609205)
                ·
                  refine ⟨6444582044195719436213363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 68742208471421007319609205 6444582044195719436213363)
                  ·
                    refine ⟨9666873066293579154320045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6444582044195719436213363 9666873066293579154320045)
                    ·
                      refine ⟨3625077399860092182870017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9666873066293579154320045 3625077399860092182870017)
                      ·
                        rfl

theorem cell23_7059813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 1, 5, 1, 3].length) (baseStart_7059813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7059813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7059813 prefixEnd_7059813 := by exact prefixLift 7059813
  have htrace : WordTrace (prefixWord ++ tailWord_7059813) baseStart_7059813 baseEnd_7059813 := by
    simpa [prefixWord, tailWord_7059813, baseEnd_7059813] using wordTrace_append hprefix tailTrace_7059813
  have hstable : (prefixWord ++ tailWord_7059813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7059813).length < 2 ^ (prefixWord ++ tailWord_7059813).sum := by decide
  have hdescent : baseEnd_7059813 < baseStart_7059813 := by decide
  rcases family_descends (prefixWord ++ tailWord_7059813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7059823 : List Nat := [1, 1, 2, 1, 3, 1, 2, 5, 2, 3, 2]
def baseStart_7059823 : Nat := 118140960795 + 7059823 * 2 ^ 59
def prefixEnd_7059823 : Nat := 4983230072969 + 3 ^ 40 * 7059823 * 2
def baseEnd_7059823 : Nat := 3625082534666637143744971

theorem tailTrace_7059823 : CollatzResearch.WordTrace tailWord_7059823 prefixEnd_7059823 3625082534666637143744971 := by
  unfold tailWord_7059823
  simp only [CollatzResearch.WordTrace]
  refine ⟨257492898702474467621096123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171661932468316311747397415 257492898702474467621096123)
  ·
    refine ⟨386239348053711701431644185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257492898702474467621096123 386239348053711701431644185)
    ·
      refine ⟨289679511040283776073733139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 386239348053711701431644185 289679511040283776073733139)
      ·
        refine ⟨434519266560425664110599709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 289679511040283776073733139 434519266560425664110599709)
        ·
          refine ⟨162944724960159624041474891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 434519266560425664110599709 162944724960159624041474891)
          ·
            refine ⟨244417087440239436062212337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162944724960159624041474891 244417087440239436062212337)
            ·
              refine ⟨183312815580179577046659253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 244417087440239436062212337 183312815580179577046659253)
              ·
                refine ⟨17185576460641835348124305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 183312815580179577046659253 17185576460641835348124305)
                ·
                  refine ⟨12889182345481376511093229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17185576460641835348124305 12889182345481376511093229)
                  ·
                    refine ⟨4833443379555516191659961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12889182345481376511093229 4833443379555516191659961)
                    ·
                      refine ⟨3625082534666637143744971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4833443379555516191659961 3625082534666637143744971)
                      ·
                        rfl

theorem cell23_7059823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 5, 2, 3, 2].length) (baseStart_7059823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7059823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7059823 prefixEnd_7059823 := by exact prefixLift 7059823
  have htrace : WordTrace (prefixWord ++ tailWord_7059823) baseStart_7059823 baseEnd_7059823 := by
    simpa [prefixWord, tailWord_7059823, baseEnd_7059823] using wordTrace_append hprefix tailTrace_7059823
  have hstable : (prefixWord ++ tailWord_7059823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7059823).length < 2 ^ (prefixWord ++ tailWord_7059823).sum := by decide
  have hdescent : baseEnd_7059823 < baseStart_7059823 := by decide
  rcases family_descends (prefixWord ++ tailWord_7059823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7059836 : List Nat := [2, 2, 2, 1, 1, 1, 2, 2, 5, 1, 4]
def baseStart_7059836 : Nat := 118140960795 + 7059836 * 2 ^ 59
def prefixEnd_7059836 : Nat := 4983230072969 + 3 ^ 40 * 7059836 * 2
def baseEnd_7059836 : Nat := 3625089209915145592882411

theorem tailTrace_7059836 : CollatzResearch.WordTrace tailWord_7059836 prefixEnd_7059836 3625089209915145592882411 := by
  unfold tailWord_7059836
  simp only [CollatzResearch.WordTrace]
  refine ⟨128746686425713685420659681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171662248567618247227546241 128746686425713685420659681)
  ·
    refine ⟨96560014819285264065494761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128746686425713685420659681 96560014819285264065494761)
    ·
      refine ⟨72420011114463948049121071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96560014819285264065494761 72420011114463948049121071)
      ·
        refine ⟨108630016671695922073681607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72420011114463948049121071 108630016671695922073681607)
        ·
          refine ⟨162945025007543883110522411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108630016671695922073681607 162945025007543883110522411)
          ·
            refine ⟨244417537511315824665783617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162945025007543883110522411 244417537511315824665783617)
            ·
              refine ⟨183313153133486868499337713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 244417537511315824665783617 183313153133486868499337713)
              ·
                refine ⟨137484864850115151374503285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 183313153133486868499337713 137484864850115151374503285)
                ·
                  refine ⟨12889206079698295441359683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 137484864850115151374503285 12889206079698295441359683)
                  ·
                    refine ⟨19333809119547443162039525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12889206079698295441359683 19333809119547443162039525)
                    ·
                      refine ⟨3625089209915145592882411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19333809119547443162039525 3625089209915145592882411)
                      ·
                        rfl

theorem cell23_7059836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 2, 5, 1, 4].length) (baseStart_7059836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7059836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7059836 prefixEnd_7059836 := by exact prefixLift 7059836
  have htrace : WordTrace (prefixWord ++ tailWord_7059836) baseStart_7059836 baseEnd_7059836 := by
    simpa [prefixWord, tailWord_7059836, baseEnd_7059836] using wordTrace_append hprefix tailTrace_7059836
  have hstable : (prefixWord ++ tailWord_7059836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7059836).length < 2 ^ (prefixWord ++ tailWord_7059836).sum := by decide
  have hdescent : baseEnd_7059836 < baseStart_7059836 := by decide
  rcases family_descends (prefixWord ++ tailWord_7059836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7059863 : List Nat := [1, 1, 3, 3, 1, 1, 2, 5, 2, 4]
def baseStart_7059863 : Nat := 118140960795 + 7059863 * 2 ^ 59
def prefixEnd_7059863 : Nat := 4983230072969 + 3 ^ 40 * 7059863 * 2
def baseEnd_7059863 : Nat := 1208367691297605662414929

theorem tailTrace_7059863 : CollatzResearch.WordTrace tailWord_7059863 prefixEnd_7059863 1208367691297605662414929 := by
  unfold tailWord_7059863
  simp only [CollatzResearch.WordTrace]
  refine ⟨257494357622329554452552243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171662905081553036301701495 257494357622329554452552243)
  ·
    refine ⟨386241536433494331678828365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257494357622329554452552243 386241536433494331678828365)
    ·
      refine ⟨144840576162560374379560637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 386241536433494331678828365 144840576162560374379560637)
      ·
        refine ⟨54315216060960140392335239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144840576162560374379560637 54315216060960140392335239)
        ·
          refine ⟨81472824091440210588502859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54315216060960140392335239 81472824091440210588502859)
          ·
            refine ⟨122209236137160315882754289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81472824091440210588502859 122209236137160315882754289)
            ·
              refine ⟨91656927102870236912065717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122209236137160315882754289 91656927102870236912065717)
              ·
                refine ⟨8592836915894084710506161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 91656927102870236912065717 8592836915894084710506161)
                ·
                  refine ⟨6444627686920563532879621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8592836915894084710506161 6444627686920563532879621)
                  ·
                    refine ⟨1208367691297605662414929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6444627686920563532879621 1208367691297605662414929)
                    ·
                      rfl

theorem cell23_7059863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 5, 2, 4].length) (baseStart_7059863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7059863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7059863 prefixEnd_7059863 := by exact prefixLift 7059863
  have htrace : WordTrace (prefixWord ++ tailWord_7059863) baseStart_7059863 baseEnd_7059863 := by
    simpa [prefixWord, tailWord_7059863, baseEnd_7059863] using wordTrace_append hprefix tailTrace_7059863
  have hstable : (prefixWord ++ tailWord_7059863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7059863).length < 2 ^ (prefixWord ++ tailWord_7059863).sum := by decide
  have hdescent : baseEnd_7059863 < baseStart_7059863 := by decide
  rcases family_descends (prefixWord ++ tailWord_7059863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7059880 : List Nat := [2, 1, 6, 1, 1, 1, 1, 2, 4, 4]
def baseStart_7059880 : Nat := 118140960795 + 7059880 * 2 ^ 59
def prefixEnd_7059880 : Nat := 4983230072969 + 3 ^ 40 * 7059880 * 2
def baseEnd_7059880 : Nat := 1208370601021314473577403

theorem tailTrace_7059880 : CollatzResearch.WordTrace tailWord_7059880 prefixEnd_7059880 1208370601021314473577403 := by
  unfold tailWord_7059880
  simp only [CollatzResearch.WordTrace]
  refine ⟨128747488831633983177960547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171663318442178644237280729 128747488831633983177960547)
  ·
    refine ⟨193121233247450974766940821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128747488831633983177960547 193121233247450974766940821)
    ·
      refine ⟨9052557808474264442200351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 193121233247450974766940821 9052557808474264442200351)
      ·
        refine ⟨13578836712711396663300527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9052557808474264442200351 13578836712711396663300527)
        ·
          refine ⟨20368255069067094994950791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13578836712711396663300527 20368255069067094994950791)
          ·
            refine ⟨30552382603600642492426187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20368255069067094994950791 30552382603600642492426187)
            ·
              refine ⟨45828573905400963738639281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30552382603600642492426187 45828573905400963738639281)
              ·
                refine ⟨34371430429050722803979461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45828573905400963738639281 34371430429050722803979461)
                ·
                  refine ⟨6444643205447010525746149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34371430429050722803979461 6444643205447010525746149)
                  ·
                    refine ⟨1208370601021314473577403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6444643205447010525746149 1208370601021314473577403)
                    ·
                      rfl

theorem cell23_7059880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 2, 4, 4].length) (baseStart_7059880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7059880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7059880 prefixEnd_7059880 := by exact prefixLift 7059880
  have htrace : WordTrace (prefixWord ++ tailWord_7059880) baseStart_7059880 baseEnd_7059880 := by
    simpa [prefixWord, tailWord_7059880, baseEnd_7059880] using wordTrace_append hprefix tailTrace_7059880
  have hstable : (prefixWord ++ tailWord_7059880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7059880).length < 2 ^ (prefixWord ++ tailWord_7059880).sum := by decide
  have hdescent : baseEnd_7059880 < baseStart_7059880 := by decide
  rcases family_descends (prefixWord ++ tailWord_7059880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7059893 : List Nat := [1, 3, 3, 2, 3, 2, 9]
def baseStart_7059893 : Nat := 118140960795 + 7059893 * 2 ^ 59
def prefixEnd_7059893 : Nat := 4983230072969 + 3 ^ 40 * 7059893 * 2
def baseEnd_7059893 : Nat := 44754549114968541603329

theorem tailTrace_7059893 : CollatzResearch.WordTrace tailWord_7059893 prefixEnd_7059893 44754549114968541603329 := by
  unfold tailWord_7059893
  simp only [CollatzResearch.WordTrace]
  refine ⟨257495451812220869576144333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171663634541480579717429555 257495451812220869576144333)
  ·
    refine ⟨96560794429582826091054125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 257495451812220869576144333 96560794429582826091054125)
    ·
      refine ⟨36210297911093559784145297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96560794429582826091054125 36210297911093559784145297)
      ·
        refine ⟨27157723433320169838108973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36210297911093559784145297 27157723433320169838108973)
        ·
          refine ⟨10184146287495063689290865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27157723433320169838108973 10184146287495063689290865)
          ·
            refine ⟨7638109715621297766968149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10184146287495063689290865 7638109715621297766968149)
            ·
              refine ⟨44754549114968541603329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7638109715621297766968149 44754549114968541603329)
              ·
                rfl

theorem cell23_7059893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 9].length) (baseStart_7059893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7059893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7059893 prefixEnd_7059893 := by exact prefixLift 7059893
  have htrace : WordTrace (prefixWord ++ tailWord_7059893) baseStart_7059893 baseEnd_7059893 := by
    simpa [prefixWord, tailWord_7059893, baseEnd_7059893] using wordTrace_append hprefix tailTrace_7059893
  have hstable : (prefixWord ++ tailWord_7059893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7059893).length < 2 ^ (prefixWord ++ tailWord_7059893).sum := by decide
  have hdescent : baseEnd_7059893 < baseStart_7059893 := by decide
  rcases family_descends (prefixWord ++ tailWord_7059893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7059930 : List Nat := [3, 1, 1, 2, 3, 1, 3, 1, 3, 3, 2]
def baseStart_7059930 : Nat := 118140960795 + 7059930 * 2 ^ 59
def prefixEnd_7059930 : Nat := 4983230072969 + 3 ^ 40 * 7059930 * 2
def baseEnd_7059930 : Nat := 3625137477096668225106979

theorem tailTrace_7059930 : CollatzResearch.WordTrace tailWord_7059930 prefixEnd_7059930 3625137477096668225106979 := by
  unfold tailWord_7059930
  simp only [CollatzResearch.WordTrace]
  refine ⟨64374200328271706223810311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171664534208724549930160829 64374200328271706223810311)
  ·
    refine ⟨96561300492407559335715467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64374200328271706223810311 96561300492407559335715467)
    ·
      refine ⟨144841950738611339003573201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96561300492407559335715467 144841950738611339003573201)
      ·
        refine ⟨108631463053958504252679901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144841950738611339003573201 108631463053958504252679901)
        ·
          refine ⟨40736798645234439094754963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108631463053958504252679901 40736798645234439094754963)
          ·
            refine ⟨61105197967851658642132445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40736798645234439094754963 61105197967851658642132445)
            ·
              refine ⟨22914449237944371990799667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61105197967851658642132445 22914449237944371990799667)
              ·
                refine ⟨34371673856916557986199501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22914449237944371990799667 34371673856916557986199501)
                ·
                  refine ⟨12889377696343709244824813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34371673856916557986199501 12889377696343709244824813)
                  ·
                    refine ⟨4833516636128890966809305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12889377696343709244824813 4833516636128890966809305)
                    ·
                      refine ⟨3625137477096668225106979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4833516636128890966809305 3625137477096668225106979)
                      ·
                        rfl

theorem cell23_7059930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 1, 3, 3, 2].length) (baseStart_7059930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7059930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7059930 prefixEnd_7059930 := by exact prefixLift 7059930
  have htrace : WordTrace (prefixWord ++ tailWord_7059930) baseStart_7059930 baseEnd_7059930 := by
    simpa [prefixWord, tailWord_7059930, baseEnd_7059930] using wordTrace_append hprefix tailTrace_7059930
  have hstable : (prefixWord ++ tailWord_7059930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7059930).length < 2 ^ (prefixWord ++ tailWord_7059930).sum := by decide
  have hdescent : baseEnd_7059930 < baseStart_7059930 := by decide
  rcases family_descends (prefixWord ++ tailWord_7059930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7059947 : List Nat := [1, 1, 1, 1, 2, 3, 7, 1, 1, 3, 2]
def baseStart_7059947 : Nat := 118140960795 + 7059947 * 2 ^ 59
def prefixEnd_7059947 : Nat := 4983230072969 + 3 ^ 40 * 7059947 * 2
def baseEnd_7059947 : Nat := 3625146206267794658594401

theorem tailTrace_7059947 : CollatzResearch.WordTrace tailWord_7059947 prefixEnd_7059947 3625146206267794658594401 := by
  unfold tailWord_7059947
  simp only [CollatzResearch.WordTrace]
  refine ⟨257497421354025236798610095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171664947569350157865740063 257497421354025236798610095)
  ·
    refine ⟨386246132031037855197915143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257497421354025236798610095 386246132031037855197915143)
    ·
      refine ⟨579369198046556782796872715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 386246132031037855197915143 579369198046556782796872715)
      ·
        refine ⟨869053797069835174195309073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 579369198046556782796872715 869053797069835174195309073)
        ·
          refine ⟨651790347802376380646481805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 869053797069835174195309073 651790347802376380646481805)
          ·
            refine ⟨244421380425891142742430677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 651790347802376380646481805 244421380425891142742430677)
            ·
              refine ⟨5728626103731823658025719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 244421380425891142742430677 5728626103731823658025719)
              ·
                refine ⟨8592939155597735487038579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5728626103731823658025719 8592939155597735487038579)
                ·
                  refine ⟨12889408733396603230557869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8592939155597735487038579 12889408733396603230557869)
                  ·
                    refine ⟨4833528275023726211459201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12889408733396603230557869 4833528275023726211459201)
                    ·
                      refine ⟨3625146206267794658594401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4833528275023726211459201 3625146206267794658594401)
                      ·
                        rfl

theorem cell23_7059947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 7, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 7, 1, 1, 3, 2].length) (baseStart_7059947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7059947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7059947 prefixEnd_7059947 := by exact prefixLift 7059947
  have htrace : WordTrace (prefixWord ++ tailWord_7059947) baseStart_7059947 baseEnd_7059947 := by
    simpa [prefixWord, tailWord_7059947, baseEnd_7059947] using wordTrace_append hprefix tailTrace_7059947
  have hstable : (prefixWord ++ tailWord_7059947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7059947).length < 2 ^ (prefixWord ++ tailWord_7059947).sum := by decide
  have hdescent : baseEnd_7059947 < baseStart_7059947 := by decide
  rcases family_descends (prefixWord ++ tailWord_7059947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7059954 : List Nat := [3, 2, 1, 4, 2, 1, 2, 2, 2, 1, 3]
def baseStart_7059954 : Nat := 118140960795 + 7059954 * 2 ^ 59
def prefixEnd_7059954 : Nat := 4983230072969 + 3 ^ 40 * 7059954 * 2
def baseEnd_7059954 : Nat := 3625149800632376131206869

theorem tailTrace_7059954 : CollatzResearch.WordTrace tailWord_7059954 prefixEnd_7059954 3625149800632376131206869 := by
  unfold tailWord_7059954
  simp only [CollatzResearch.WordTrace]
  refine ⟨64374419166249969248528729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171665117776666584662743277 64374419166249969248528729)
  ·
    refine ⟨48280814374687476936396547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64374419166249969248528729 48280814374687476936396547)
    ·
      refine ⟨72421221562031215404594821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48280814374687476936396547 72421221562031215404594821)
      ·
        refine ⟨13578979042880852888361529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72421221562031215404594821 13578979042880852888361529)
        ·
          refine ⟨10184234282160639666271147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13578979042880852888361529 10184234282160639666271147)
          ·
            refine ⟨15276351423240959499406721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10184234282160639666271147 15276351423240959499406721)
            ·
              refine ⟨11457263567430719624555041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15276351423240959499406721 11457263567430719624555041)
              ·
                refine ⟨8592947675573039718416281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11457263567430719624555041 8592947675573039718416281)
                ·
                  refine ⟨6444710756679779788812211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8592947675573039718416281 6444710756679779788812211)
                  ·
                    refine ⟨9667066135019669683218317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6444710756679779788812211 9667066135019669683218317)
                    ·
                      refine ⟨3625149800632376131206869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9667066135019669683218317 3625149800632376131206869)
                      ·
                        rfl

theorem cell23_7059954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 2, 2, 2, 1, 3].length) (baseStart_7059954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7059954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7059954 prefixEnd_7059954 := by exact prefixLift 7059954
  have htrace : WordTrace (prefixWord ++ tailWord_7059954) baseStart_7059954 baseEnd_7059954 := by
    simpa [prefixWord, tailWord_7059954, baseEnd_7059954] using wordTrace_append hprefix tailTrace_7059954
  have hstable : (prefixWord ++ tailWord_7059954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7059954).length < 2 ^ (prefixWord ++ tailWord_7059954).sum := by decide
  have hdescent : baseEnd_7059954 < baseStart_7059954 := by decide
  rcases family_descends (prefixWord ++ tailWord_7059954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7060010 : List Nat := [3, 1, 4, 1, 1, 2, 1, 2, 2, 3, 3]
def baseStart_7060010 : Nat := 118140960795 + 7060010 * 2 ^ 59
def prefixEnd_7060010 : Nat := 4983230072969 + 3 ^ 40 * 7060010 * 2
def baseEnd_7060010 : Nat := 3625178555549027912106611

theorem tailTrace_7060010 : CollatzResearch.WordTrace tailWord_7060010 prefixEnd_7060010 3625178555549027912106611 := by
  unfold tailWord_7060010
  simp only [CollatzResearch.WordTrace]
  refine ⟨64374929788199249639538371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171666479435197999038768989 64374929788199249639538371)
  ·
    refine ⟨96562394682298874459307557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64374929788199249639538371 96562394682298874459307557)
    ·
      refine ⟨18105449002931038961120167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 96562394682298874459307557 18105449002931038961120167)
      ·
        refine ⟨27158173504396558441680251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18105449002931038961120167 27158173504396558441680251)
        ·
          refine ⟨40737260256594837662520377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27158173504396558441680251 40737260256594837662520377)
          ·
            refine ⟨30552945192446128246890283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40737260256594837662520377 30552945192446128246890283)
            ·
              refine ⟨45829417788669192370335425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30552945192446128246890283 45829417788669192370335425)
              ·
                refine ⟨34372063341501894277751569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45829417788669192370335425 34372063341501894277751569)
                ·
                  refine ⟨25779047506126420708313677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34372063341501894277751569 25779047506126420708313677)
                  ·
                    refine ⟨9667142814797407765617629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25779047506126420708313677 9667142814797407765617629)
                    ·
                      refine ⟨3625178555549027912106611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9667142814797407765617629 3625178555549027912106611)
                      ·
                        rfl

theorem cell23_7060010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 2, 2, 3, 3].length) (baseStart_7060010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7060010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7060010 prefixEnd_7060010 := by exact prefixLift 7060010
  have htrace : WordTrace (prefixWord ++ tailWord_7060010) baseStart_7060010 baseEnd_7060010 := by
    simpa [prefixWord, tailWord_7060010, baseEnd_7060010] using wordTrace_append hprefix tailTrace_7060010
  have hstable : (prefixWord ++ tailWord_7060010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7060010).length < 2 ^ (prefixWord ++ tailWord_7060010).sum := by decide
  have hdescent : baseEnd_7060010 < baseStart_7060010 := by decide
  rcases family_descends (prefixWord ++ tailWord_7060010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7060050 : List Nat := [3, 2, 2, 1, 2, 1, 2, 3, 2, 1, 4]
def baseStart_7060050 : Nat := 118140960795 + 7060050 * 2 ^ 59
def prefixEnd_7060050 : Nat := 4983230072969 + 3 ^ 40 * 7060050 * 2
def baseEnd_7060050 : Nat := 3625199094775207755606427

theorem tailTrace_7060050 : CollatzResearch.WordTrace tailWord_7060050 prefixEnd_7060050 3625199094775207755606427 := by
  unfold tailWord_7060050
  simp only [CollatzResearch.WordTrace]
  refine ⟨64375294518163021347402401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171667452048434723593073069 64375294518163021347402401)
  ·
    refine ⟨48281470888622266010551801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64375294518163021347402401 48281470888622266010551801)
    ·
      refine ⟨36211103166466699507913851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48281470888622266010551801 36211103166466699507913851)
      ·
        refine ⟨54316654749700049261870777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36211103166466699507913851 54316654749700049261870777)
        ·
          refine ⟨40737491062275036946403083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54316654749700049261870777 40737491062275036946403083)
          ·
            refine ⟨61106236593412555419604625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40737491062275036946403083 61106236593412555419604625)
            ·
              refine ⟨45829677445059416564703469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61106236593412555419604625 45829677445059416564703469)
              ·
                refine ⟨17186129041897281211763801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45829677445059416564703469 17186129041897281211763801)
                ·
                  refine ⟨12889596781422960908822851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17186129041897281211763801 12889596781422960908822851)
                  ·
                    refine ⟨19334395172134441363234277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12889596781422960908822851 19334395172134441363234277)
                    ·
                      refine ⟨3625199094775207755606427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19334395172134441363234277 3625199094775207755606427)
                      ·
                        rfl

theorem cell23_7060050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 3, 2, 1, 4].length) (baseStart_7060050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7060050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7060050 prefixEnd_7060050 := by exact prefixLift 7060050
  have htrace : WordTrace (prefixWord ++ tailWord_7060050) baseStart_7060050 baseEnd_7060050 := by
    simpa [prefixWord, tailWord_7060050, baseEnd_7060050] using wordTrace_append hprefix tailTrace_7060050
  have hstable : (prefixWord ++ tailWord_7060050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7060050).length < 2 ^ (prefixWord ++ tailWord_7060050).sum := by decide
  have hdescent : baseEnd_7060050 < baseStart_7060050 := by decide
  rcases family_descends (prefixWord ++ tailWord_7060050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7060073 : List Nat := [1, 2, 1, 1, 1, 4, 1, 6, 6]
def baseStart_7060073 : Nat := 118140960795 + 7060073 * 2 ^ 59
def prefixEnd_7060073 : Nat := 4983230072969 + 3 ^ 40 * 7060073 * 2
def baseEnd_7060073 : Nat := 402801211647806796179869

theorem tailTrace_7060073 : CollatzResearch.WordTrace tailWord_7060073 prefixEnd_7060073 402801211647806796179869 := by
  unfold tailWord_7060073
  simp only [CollatzResearch.WordTrace]
  refine ⟨257502016951568760317696873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171668011301045840211797915 257502016951568760317696873)
  ·
    refine ⟨193126512713676570238272655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257502016951568760317696873 193126512713676570238272655)
    ·
      refine ⟨289689769070514855357408983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193126512713676570238272655 289689769070514855357408983)
      ·
        refine ⟨434534653605772283036113475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 289689769070514855357408983 434534653605772283036113475)
        ·
          refine ⟨651801980408658424554170213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 434534653605772283036113475 651801980408658424554170213)
          ·
            refine ⟨122212871326623454603906915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 651801980408658424554170213 122212871326623454603906915)
            ·
              refine ⟨183319306989935181905860373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122212871326623454603906915 183319306989935181905860373)
              ·
                refine ⟨8593092515153211651837205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 183319306989935181905860373 8593092515153211651837205)
                ·
                  refine ⟨402801211647806796179869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8593092515153211651837205 402801211647806796179869)
                  ·
                    rfl

theorem cell23_7060073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 6, 6].length) (baseStart_7060073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7060073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7060073 prefixEnd_7060073 := by exact prefixLift 7060073
  have htrace : WordTrace (prefixWord ++ tailWord_7060073) baseStart_7060073 baseEnd_7060073 := by
    simpa [prefixWord, tailWord_7060073, baseEnd_7060073] using wordTrace_append hprefix tailTrace_7060073
  have hstable : (prefixWord ++ tailWord_7060073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7060073).length < 2 ^ (prefixWord ++ tailWord_7060073).sum := by decide
  have hdescent : baseEnd_7060073 < baseStart_7060073 := by decide
  rcases family_descends (prefixWord ++ tailWord_7060073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7060077 : List Nat := [1, 5, 1, 1, 3, 1, 3, 1, 3, 4]
def baseStart_7060077 : Nat := 118140960795 + 7060077 * 2 ^ 59
def prefixEnd_7060077 : Nat := 4983230072969 + 3 ^ 40 * 7060077 * 2
def baseEnd_7060077 : Nat := 1208404319584293049989601

theorem tailTrace_7060077 : CollatzResearch.WordTrace tailWord_7060077 prefixEnd_7060077 1208404319584293049989601 := by
  unfold tailWord_7060077
  simp only [CollatzResearch.WordTrace]
  refine ⟨257502162843554269000842485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171668108562369512667228323 257502162843554269000842485)
  ·
    refine ⟨24140827766583212718828983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 257502162843554269000842485 24140827766583212718828983)
    ·
      refine ⟨36211241649874819078243475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24140827766583212718828983 36211241649874819078243475)
      ·
        refine ⟨54316862474812228617365213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36211241649874819078243475 54316862474812228617365213)
        ·
          refine ⟨20368823428054585731511955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54316862474812228617365213 20368823428054585731511955)
          ·
            refine ⟨30553235142081878597267933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20368823428054585731511955 30553235142081878597267933)
            ·
              refine ⟨11457463178280704473975475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30553235142081878597267933 11457463178280704473975475)
              ·
                refine ⟨17186194767421056710963213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11457463178280704473975475 17186194767421056710963213)
                ·
                  refine ⟨6444823037782896266611205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17186194767421056710963213 6444823037782896266611205)
                  ·
                    refine ⟨1208404319584293049989601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6444823037782896266611205 1208404319584293049989601)
                    ·
                      rfl

theorem cell23_7060077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 3, 1, 3, 4].length) (baseStart_7060077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7060077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7060077 prefixEnd_7060077 := by exact prefixLift 7060077
  have htrace : WordTrace (prefixWord ++ tailWord_7060077) baseStart_7060077 baseEnd_7060077 := by
    simpa [prefixWord, tailWord_7060077, baseEnd_7060077] using wordTrace_append hprefix tailTrace_7060077
  have hstable : (prefixWord ++ tailWord_7060077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7060077).length < 2 ^ (prefixWord ++ tailWord_7060077).sum := by decide
  have hdescent : baseEnd_7060077 < baseStart_7060077 := by decide
  rcases family_descends (prefixWord ++ tailWord_7060077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7060083 : List Nat := [1, 1, 1, 2, 2, 1, 1, 4, 2, 5, 3]
def baseStart_7060083 : Nat := 118140960795 + 7060083 * 2 ^ 59
def prefixEnd_7060083 : Nat := 4983230072969 + 3 ^ 40 * 7060083 * 2
def baseEnd_7060083 : Nat := 3625216039636806126493775

theorem tailTrace_7060083 : CollatzResearch.WordTrace tailWord_7060083 prefixEnd_7060083 3625216039636806126493775 := by
  unfold tailWord_7060083
  simp only [CollatzResearch.WordTrace]
  refine ⟨257502381681532532025560903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171668254454355021350373935 257502381681532532025560903)
  ·
    refine ⟨386253572522298798038341355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257502381681532532025560903 386253572522298798038341355)
    ·
      refine ⟨579380358783448197057512033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 386253572522298798038341355 579380358783448197057512033)
      ·
        refine ⟨434535269087586147793134025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 579380358783448197057512033 434535269087586147793134025)
        ·
          refine ⟨325901451815689610844850519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 434535269087586147793134025 325901451815689610844850519)
          ·
            refine ⟨488852177723534416267275779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 325901451815689610844850519 488852177723534416267275779)
            ·
              refine ⟨733278266585301624400913669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 488852177723534416267275779 733278266585301624400913669)
              ·
                refine ⟨137489674984744054575171313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 733278266585301624400913669 137489674984744054575171313)
                ·
                  refine ⟨103117256238558040931378485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 137489674984744054575171313 103117256238558040931378485)
                  ·
                    refine ⟨9667242772364816337316733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 103117256238558040931378485 9667242772364816337316733)
                    ·
                      refine ⟨3625216039636806126493775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9667242772364816337316733 3625216039636806126493775)
                      ·
                        rfl

theorem cell23_7060083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 4, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 4, 2, 5, 3].length) (baseStart_7060083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7060083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7060083 prefixEnd_7060083 := by exact prefixLift 7060083
  have htrace : WordTrace (prefixWord ++ tailWord_7060083) baseStart_7060083 baseEnd_7060083 := by
    simpa [prefixWord, tailWord_7060083, baseEnd_7060083] using wordTrace_append hprefix tailTrace_7060083
  have hstable : (prefixWord ++ tailWord_7060083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7060083).length < 2 ^ (prefixWord ++ tailWord_7060083).sum := by decide
  have hdescent : baseEnd_7060083 < baseStart_7060083 := by decide
  rcases family_descends (prefixWord ++ tailWord_7060083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7060128 : List Nat := [2, 1, 1, 4, 5, 1, 2, 2, 1, 4]
def baseStart_7060128 : Nat := 118140960795 + 7060128 * 2 ^ 59
def prefixEnd_7060128 : Nat := 4983230072969 + 3 ^ 40 * 7060128 * 2
def baseEnd_7060128 : Nat := 1208413048755419483477023

theorem tailTrace_7060128 : CollatzResearch.WordTrace tailWord_7060128 prefixEnd_7060128 1208413048755419483477023 := by
  unfold tailWord_7060128
  simp only [CollatzResearch.WordTrace]
  refine ⟨128752011483184752355474519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171669348644246336473966025 128752011483184752355474519)
  ·
    refine ⟨193128017224777128533211779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128752011483184752355474519 193128017224777128533211779)
    ·
      refine ⟨289692025837165692799817669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193128017224777128533211779 289692025837165692799817669)
      ·
        refine ⟨54317254844468567399965813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 289692025837165692799817669 54317254844468567399965813)
        ·
          refine ⟨5092242641668928193746795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 54317254844468567399965813 5092242641668928193746795)
          ·
            refine ⟨7638363962503392290620193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5092242641668928193746795 7638363962503392290620193)
            ·
              refine ⟨5728772971877544217965145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7638363962503392290620193 5728772971877544217965145)
              ·
                refine ⟨4296579728908158163473859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5728772971877544217965145 4296579728908158163473859)
                ·
                  refine ⟨6444869593362237245210789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4296579728908158163473859 6444869593362237245210789)
                  ·
                    refine ⟨1208413048755419483477023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6444869593362237245210789 1208413048755419483477023)
                    ·
                      rfl

theorem cell23_7060128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 2, 2, 1, 4].length) (baseStart_7060128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7060128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7060128 prefixEnd_7060128 := by exact prefixLift 7060128
  have htrace : WordTrace (prefixWord ++ tailWord_7060128) baseStart_7060128 baseEnd_7060128 := by
    simpa [prefixWord, tailWord_7060128, baseEnd_7060128] using wordTrace_append hprefix tailTrace_7060128
  have hstable : (prefixWord ++ tailWord_7060128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7060128).length < 2 ^ (prefixWord ++ tailWord_7060128).sum := by decide
  have hdescent : baseEnd_7060128 < baseStart_7060128 := by decide
  rcases family_descends (prefixWord ++ tailWord_7060128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7060133 : List Nat := [1, 3, 1, 2, 1, 2, 1, 1, 5, 6]
def baseStart_7060133 : Nat := 118140960795 + 7060133 * 2 ^ 59
def prefixEnd_7060133 : Nat := 4983230072969 + 3 ^ 40 * 7060133 * 2
def baseEnd_7060133 : Nat := 1208413904556510310289515

theorem tailTrace_7060133 : CollatzResearch.WordTrace tailWord_7060133 prefixEnd_7060133 1208413904556510310289515 := by
  unfold tailWord_7060133
  simp only [CollatzResearch.WordTrace]
  refine ⟨257504205331351390564881053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171669470220900927043254035 257504205331351390564881053)
  ·
    refine ⟨96564076999256771461830395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 257504205331351390564881053 96564076999256771461830395)
    ·
      refine ⟨144846115498885157192745593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96564076999256771461830395 144846115498885157192745593)
      ·
        refine ⟨108634586624163867894559195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144846115498885157192745593 108634586624163867894559195)
        ·
          refine ⟨162951879936245801841838793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108634586624163867894559195 162951879936245801841838793)
          ·
            refine ⟨122213909952184351381379095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162951879936245801841838793 122213909952184351381379095)
            ·
              refine ⟨183320864928276527072068643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122213909952184351381379095 183320864928276527072068643)
              ·
                refine ⟨274981297392414790608102965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 183320864928276527072068643 274981297392414790608102965)
                ·
                  refine ⟨25779496630538886619509653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 274981297392414790608102965 25779496630538886619509653)
                  ·
                    refine ⟨1208413904556510310289515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25779496630538886619509653 1208413904556510310289515)
                    ·
                      rfl

theorem cell23_7060133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 1, 5, 6].length) (baseStart_7060133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7060133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7060133 prefixEnd_7060133 := by exact prefixLift 7060133
  have htrace : WordTrace (prefixWord ++ tailWord_7060133) baseStart_7060133 baseEnd_7060133 := by
    simpa [prefixWord, tailWord_7060133, baseEnd_7060133] using wordTrace_append hprefix tailTrace_7060133
  have hstable : (prefixWord ++ tailWord_7060133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7060133).length < 2 ^ (prefixWord ++ tailWord_7060133).sum := by decide
  have hdescent : baseEnd_7060133 < baseStart_7060133 := by decide
  rcases family_descends (prefixWord ++ tailWord_7060133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7060161 : List Nat := [1, 2, 6, 2, 1, 1, 1, 1, 1, 5, 2]
def baseStart_7060161 : Nat := 118140960795 + 7060161 * 2 ^ 59
def prefixEnd_7060161 : Nat := 4983230072969 + 3 ^ 40 * 7060161 * 2
def baseEnd_7060161 : Nat := 3625256091127856821318417

theorem tailTrace_7060161 : CollatzResearch.WordTrace tailWord_7060161 prefixEnd_7060161 3625256091127856821318417 := by
  unfold tailWord_7060161
  simp only [CollatzResearch.WordTrace]
  refine ⟨257505226575249951346900337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171670151050166634231266891 257505226575249951346900337)
  ·
    refine ⟨193128919931437463510175253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257505226575249951346900337 193128919931437463510175253)
    ·
      refine ⟨9052918121786131102039465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 193128919931437463510175253 9052918121786131102039465)
      ·
        refine ⟨6789688591339598326529599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9052918121786131102039465 6789688591339598326529599)
        ·
          refine ⟨10184532887009397489794399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6789688591339598326529599 10184532887009397489794399)
          ·
            refine ⟨15276799330514096234691599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10184532887009397489794399 15276799330514096234691599)
            ·
              refine ⟨22915198995771144352037399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15276799330514096234691599 22915198995771144352037399)
              ·
                refine ⟨34372798493656716528056099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22915198995771144352037399 34372798493656716528056099)
                ·
                  refine ⟨51559197740485074792084149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34372798493656716528056099 51559197740485074792084149)
                  ·
                    refine ⟨4833674788170475761757889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51559197740485074792084149 4833674788170475761757889)
                    ·
                      refine ⟨3625256091127856821318417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4833674788170475761757889 3625256091127856821318417)
                      ·
                        rfl

theorem cell23_7060161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 1, 1, 5, 2].length) (baseStart_7060161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7060161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7060161 prefixEnd_7060161 := by exact prefixLift 7060161
  have htrace : WordTrace (prefixWord ++ tailWord_7060161) baseStart_7060161 baseEnd_7060161 := by
    simpa [prefixWord, tailWord_7060161, baseEnd_7060161] using wordTrace_append hprefix tailTrace_7060161
  have hstable : (prefixWord ++ tailWord_7060161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7060161).length < 2 ^ (prefixWord ++ tailWord_7060161).sum := by decide
  have hdescent : baseEnd_7060161 < baseStart_7060161 := by decide
  rcases family_descends (prefixWord ++ tailWord_7060161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7060174 : List Nat := [4, 1, 1, 1, 3, 2, 4, 1, 1, 1, 4]
def baseStart_7060174 : Nat := 118140960795 + 7060174 * 2 ^ 59
def prefixEnd_7060174 : Nat := 4983230072969 + 3 ^ 40 * 7060174 * 2
def baseEnd_7060174 : Nat := 3625262766376365270455857

theorem tailTrace_7060174 : CollatzResearch.WordTrace tailWord_7060174 prefixEnd_7060174 3625262766376365270455857 := by
  unfold tailWord_7060174
  simp only [CollatzResearch.WordTrace]
  refine ⟨32188212590525356820890447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 171670467149468569711415717 32188212590525356820890447)
  ·
    refine ⟨48282318885788035231335671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32188212590525356820890447 48282318885788035231335671)
    ·
      refine ⟨72423478328682052847003507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48282318885788035231335671 72423478328682052847003507)
      ·
        refine ⟨108635217493023079270505261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72423478328682052847003507 108635217493023079270505261)
        ·
          refine ⟨40738206559883654726439473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108635217493023079270505261 40738206559883654726439473)
          ·
            refine ⟨30553654919912741044829605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40738206559883654726439473 30553654919912741044829605)
            ·
              refine ⟨5728810297483638945905551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30553654919912741044829605 5728810297483638945905551)
              ·
                refine ⟨8593215446225458418858327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5728810297483638945905551 8593215446225458418858327)
                ·
                  refine ⟨12889823169338187628287491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8593215446225458418858327 12889823169338187628287491)
                  ·
                    refine ⟨19334734754007281442431237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12889823169338187628287491 19334734754007281442431237)
                    ·
                      refine ⟨3625262766376365270455857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19334734754007281442431237 3625262766376365270455857)
                      ·
                        rfl

theorem cell23_7060174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 4, 1, 1, 1, 4].length) (baseStart_7060174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7060174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7060174 prefixEnd_7060174 := by exact prefixLift 7060174
  have htrace : WordTrace (prefixWord ++ tailWord_7060174) baseStart_7060174 baseEnd_7060174 := by
    simpa [prefixWord, tailWord_7060174, baseEnd_7060174] using wordTrace_append hprefix tailTrace_7060174
  have hstable : (prefixWord ++ tailWord_7060174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7060174).length < 2 ^ (prefixWord ++ tailWord_7060174).sum := by decide
  have hdescent : baseEnd_7060174 < baseStart_7060174 := by decide
  rcases family_descends (prefixWord ++ tailWord_7060174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7060177 : List Nat := [1, 2, 2, 1, 2, 3, 3, 3, 1, 2, 3]
def baseStart_7060177 : Nat := 118140960795 + 7060177 * 2 ^ 59
def prefixEnd_7060177 : Nat := 4983230072969 + 3 ^ 40 * 7060177 * 2
def baseEnd_7060177 : Nat := 3625264306818328758718343

theorem tailTrace_7060177 : CollatzResearch.WordTrace tailWord_7060177 prefixEnd_7060177 3625264306818328758718343 := by
  unfold tailWord_7060177
  simp only [CollatzResearch.WordTrace]
  refine ⟨257505810143191986079482785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171670540095461324052988523 257505810143191986079482785)
  ·
    refine ⟨193129357607393989559612089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257505810143191986079482785 193129357607393989559612089)
    ·
      refine ⟨144847018205545492169709067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193129357607393989559612089 144847018205545492169709067)
      ·
        refine ⟨217270527308318238254563601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144847018205545492169709067 217270527308318238254563601)
        ·
          refine ⟨162952895481238678690922701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 217270527308318238254563601 162952895481238678690922701)
          ·
            refine ⟨61107335805464504509096013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 162952895481238678690922701 61107335805464504509096013)
            ·
              refine ⟨22915250927049189190911005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61107335805464504509096013 22915250927049189190911005)
              ·
                refine ⟨8593219097643445946591627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22915250927049189190911005 8593219097643445946591627)
                ·
                  refine ⟨12889828646465168919887441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8593219097643445946591627 12889828646465168919887441)
                  ·
                    refine ⟨9667371484848876689915581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12889828646465168919887441 9667371484848876689915581)
                    ·
                      refine ⟨3625264306818328758718343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9667371484848876689915581 3625264306818328758718343)
                      ·
                        rfl

theorem cell23_7060177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 3, 1, 2, 3].length) (baseStart_7060177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7060177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7060177 prefixEnd_7060177 := by exact prefixLift 7060177
  have htrace : WordTrace (prefixWord ++ tailWord_7060177) baseStart_7060177 baseEnd_7060177 := by
    simpa [prefixWord, tailWord_7060177, baseEnd_7060177] using wordTrace_append hprefix tailTrace_7060177
  have hstable : (prefixWord ++ tailWord_7060177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7060177).length < 2 ^ (prefixWord ++ tailWord_7060177).sum := by decide
  have hdescent : baseEnd_7060177 < baseStart_7060177 := by decide
  rcases family_descends (prefixWord ++ tailWord_7060177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7060184 : List Nat := [2, 1, 2, 2, 3, 4, 1, 2, 2, 4]
def baseStart_7060184 : Nat := 118140960795 + 7060184 * 2 ^ 59
def prefixEnd_7060184 : Nat := 4983230072969 + 3 ^ 40 * 7060184 * 2
def baseEnd_7060184 : Nat := 1208422633727636743776937

theorem tailTrace_7060184 : CollatzResearch.WordTrace tailWord_7060184 prefixEnd_7060184 1208422633727636743776937 := by
  unfold tailWord_7060184
  simp only [CollatzResearch.WordTrace]
  refine ⟨128753032727083313137493803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171670710302777750849991737 128753032727083313137493803)
  ·
    refine ⟨193129549090624969706240705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128753032727083313137493803 193129549090624969706240705)
    ·
      refine ⟨144847161817968727279680529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193129549090624969706240705 144847161817968727279680529)
      ·
        refine ⟨108635371363476545459760397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144847161817968727279680529 108635371363476545459760397)
        ·
          refine ⟨40738264261303704547410149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108635371363476545459760397 40738264261303704547410149)
          ·
            refine ⟨7638424548994444602639403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40738264261303704547410149 7638424548994444602639403)
            ·
              refine ⟨11457636823491666903959105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7638424548994444602639403 11457636823491666903959105)
              ·
                refine ⟨8593227617618750177969329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11457636823491666903959105 8593227617618750177969329)
                ·
                  refine ⟨6444920713214062633476997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8593227617618750177969329 6444920713214062633476997)
                  ·
                    refine ⟨1208422633727636743776937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6444920713214062633476997 1208422633727636743776937)
                    ·
                      rfl

theorem cell23_7060184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 1, 2, 2, 4].length) (baseStart_7060184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7060184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7060184 prefixEnd_7060184 := by exact prefixLift 7060184
  have htrace : WordTrace (prefixWord ++ tailWord_7060184) baseStart_7060184 baseEnd_7060184 := by
    simpa [prefixWord, tailWord_7060184, baseEnd_7060184] using wordTrace_append hprefix tailTrace_7060184
  have hstable : (prefixWord ++ tailWord_7060184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7060184).length < 2 ^ (prefixWord ++ tailWord_7060184).sum := by decide
  have hdescent : baseEnd_7060184 < baseStart_7060184 := by decide
  rcases family_descends (prefixWord ++ tailWord_7060184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7060191 : List Nat := [1, 1, 2, 3, 2, 3, 2, 4, 1, 2, 2]
def baseStart_7060191 : Nat := 118140960795 + 7060191 * 2 ^ 59
def prefixEnd_7060191 : Nat := 4983230072969 + 3 ^ 40 * 7060191 * 2
def baseEnd_7060191 : Nat := 3625271495547491703943279

theorem tailTrace_7060191 : CollatzResearch.WordTrace tailWord_7060191 prefixEnd_7060191 3625271495547491703943279 := by
  unfold tailWord_7060191
  simp only [CollatzResearch.WordTrace]
  refine ⟨257506320765141266470492427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171670880510094177646994951 257506320765141266470492427)
  ·
    refine ⟨386259481147711899705738641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257506320765141266470492427 386259481147711899705738641)
    ·
      refine ⟨289694610860783924779303981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 386259481147711899705738641 289694610860783924779303981)
      ·
        refine ⟨108635479072793971792238993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 289694610860783924779303981 108635479072793971792238993)
        ·
          refine ⟨81476609304595478844179245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108635479072793971792238993 81476609304595478844179245)
          ·
            refine ⟨30553728489223304566567217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81476609304595478844179245 30553728489223304566567217)
            ·
              refine ⟨22915296366917478424925413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30553728489223304566567217 22915296366917478424925413)
              ·
                refine ⟨4296618068797027204673515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22915296366917478424925413 4296618068797027204673515)
                ·
                  refine ⟨6444927103195540807010273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4296618068797027204673515 6444927103195540807010273)
                  ·
                    refine ⟨4833695327396655605257705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6444927103195540807010273 4833695327396655605257705)
                    ·
                      refine ⟨3625271495547491703943279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4833695327396655605257705 3625271495547491703943279)
                      ·
                        rfl

theorem cell23_7060191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 4, 1, 2, 2].length) (baseStart_7060191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7060191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7060191 prefixEnd_7060191 := by exact prefixLift 7060191
  have htrace : WordTrace (prefixWord ++ tailWord_7060191) baseStart_7060191 baseEnd_7060191 := by
    simpa [prefixWord, tailWord_7060191, baseEnd_7060191] using wordTrace_append hprefix tailTrace_7060191
  have hstable : (prefixWord ++ tailWord_7060191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7060191).length < 2 ^ (prefixWord ++ tailWord_7060191).sum := by decide
  have hdescent : baseEnd_7060191 < baseStart_7060191 := by decide
  rcases family_descends (prefixWord ++ tailWord_7060191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7060207 : List Nat := [1, 1, 2, 1, 5, 2, 3, 1, 1, 3, 3]
def baseStart_7060207 : Nat := 118140960795 + 7060207 * 2 ^ 59
def prefixEnd_7060207 : Nat := 4983230072969 + 3 ^ 40 * 7060207 * 2
def baseEnd_7060207 : Nat := 3625279711237963641343205

theorem tailTrace_7060207 : CollatzResearch.WordTrace tailWord_7060207 prefixEnd_7060207 3625279711237963641343205 := by
  unfold tailWord_7060207
  simp only [CollatzResearch.WordTrace]
  refine ⟨257506904333083301203074875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171671269555388867468716583 257506904333083301203074875)
  ·
    refine ⟨386260356499624951804612313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257506904333083301203074875 386260356499624951804612313)
    ·
      refine ⟨289695267374718713853459235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 386260356499624951804612313 289695267374718713853459235)
      ·
        refine ⟨434542901062078070780188853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 289695267374718713853459235 434542901062078070780188853)
        ·
          refine ⟨40738396974569819135642705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 434542901062078070780188853 40738396974569819135642705)
          ·
            refine ⟨30553797730927364351732029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40738396974569819135642705 30553797730927364351732029)
            ·
              refine ⟨11457674149097761631899511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30553797730927364351732029 11457674149097761631899511)
              ·
                refine ⟨17186511223646642447849267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11457674149097761631899511 17186511223646642447849267)
                ·
                  refine ⟨25779766835469963671773901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17186511223646642447849267 25779766835469963671773901)
                  ·
                    refine ⟨9667412563301236376915213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25779766835469963671773901 9667412563301236376915213)
                    ·
                      refine ⟨3625279711237963641343205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9667412563301236376915213 3625279711237963641343205)
                      ·
                        rfl

theorem cell23_7060207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 3, 1, 1, 3, 3].length) (baseStart_7060207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7060207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7060207 prefixEnd_7060207 := by exact prefixLift 7060207
  have htrace : WordTrace (prefixWord ++ tailWord_7060207) baseStart_7060207 baseEnd_7060207 := by
    simpa [prefixWord, tailWord_7060207, baseEnd_7060207] using wordTrace_append hprefix tailTrace_7060207
  have hstable : (prefixWord ++ tailWord_7060207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7060207).length < 2 ^ (prefixWord ++ tailWord_7060207).sum := by decide
  have hdescent : baseEnd_7060207 < baseStart_7060207 := by decide
  rcases family_descends (prefixWord ++ tailWord_7060207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7060217 : List Nat := [1, 2, 1, 3, 1, 1, 1, 5, 3, 3, 2]
def baseStart_7060217 : Nat := 118140960795 + 7060217 * 2 ^ 59
def prefixEnd_7060217 : Nat := 4983230072969 + 3 ^ 40 * 7060217 * 2
def baseEnd_7060217 : Nat := 3625284846044508602218159

theorem tailTrace_7060217 : CollatzResearch.WordTrace tailWord_7060217 prefixEnd_7060217 3625284846044508602218159 := by
  unfold tailWord_7060217
  simp only [CollatzResearch.WordTrace]
  refine ⟨257507269063047072910938905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171671512708698048607292603 257507269063047072910938905)
  ·
    refine ⟨193130451797285304683204179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257507269063047072910938905 193130451797285304683204179)
    ·
      refine ⟨289695677695927957024806269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193130451797285304683204179 289695677695927957024806269)
      ·
        refine ⟨108635879135972983884302351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 289695677695927957024806269 108635879135972983884302351)
        ·
          refine ⟨162953818703959475826453527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108635879135972983884302351 162953818703959475826453527)
          ·
            refine ⟨244430728055939213739680291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162953818703959475826453527 244430728055939213739680291)
            ·
              refine ⟨366646092083908820609520437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 244430728055939213739680291 366646092083908820609520437)
              ·
                refine ⟨34373071132866451932142541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 366646092083908820609520437 34373071132866451932142541)
                ·
                  refine ⟨12889901674824919474553453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34373071132866451932142541 12889901674824919474553453)
                  ·
                    refine ⟨4833713128059344802957545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12889901674824919474553453 4833713128059344802957545)
                    ·
                      refine ⟨3625284846044508602218159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4833713128059344802957545 3625284846044508602218159)
                      ·
                        rfl

theorem cell23_7060217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 5, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 5, 3, 3, 2].length) (baseStart_7060217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7060217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7060217 prefixEnd_7060217 := by exact prefixLift 7060217
  have htrace : WordTrace (prefixWord ++ tailWord_7060217) baseStart_7060217 baseEnd_7060217 := by
    simpa [prefixWord, tailWord_7060217, baseEnd_7060217] using wordTrace_append hprefix tailTrace_7060217
  have hstable : (prefixWord ++ tailWord_7060217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7060217).length < 2 ^ (prefixWord ++ tailWord_7060217).sum := by decide
  have hdescent : baseEnd_7060217 < baseStart_7060217 := by decide
  rcases family_descends (prefixWord ++ tailWord_7060217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7060220 : List Nat := [2, 2, 2, 1, 3, 2, 1, 1, 2, 2, 5]
def baseStart_7060220 : Nat := 118140960795 + 7060220 * 2 ^ 59
def prefixEnd_7060220 : Nat := 4983230072969 + 3 ^ 40 * 7060220 * 2
def baseEnd_7060220 : Nat := 3625286386486472090480645

theorem tailTrace_7060220 : CollatzResearch.WordTrace tailWord_7060220 prefixEnd_7060220 3625286386486472090480645 := by
  unfold tailWord_7060220
  simp only [CollatzResearch.WordTrace]
  refine ⟨128753689241018102211649057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171671585654690802948865409 128753689241018102211649057)
  ·
    refine ⟨96565266930763576658736793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128753689241018102211649057 96565266930763576658736793)
    ·
      refine ⟨72423950198072682494052595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96565266930763576658736793 72423950198072682494052595)
      ·
        refine ⟨108635925297109023741078893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72423950198072682494052595 108635925297109023741078893)
        ·
          refine ⟨40738471986415883902904585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108635925297109023741078893 40738471986415883902904585)
          ·
            refine ⟨30553853989811912927178439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40738471986415883902904585 30553853989811912927178439)
            ·
              refine ⟨45830780984717869390767659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30553853989811912927178439 45830780984717869390767659)
              ·
                refine ⟨68746171477076804086151489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45830780984717869390767659 68746171477076804086151489)
                ·
                  refine ⟨51559628607807603064613617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68746171477076804086151489 51559628607807603064613617)
                  ·
                    refine ⟨38669721455855702298460213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51559628607807603064613617 38669721455855702298460213)
                    ·
                      refine ⟨3625286386486472090480645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38669721455855702298460213 3625286386486472090480645)
                      ·
                        rfl

theorem cell23_7060220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 1, 2, 2, 5].length) (baseStart_7060220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7060220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7060220 prefixEnd_7060220 := by exact prefixLift 7060220
  have htrace : WordTrace (prefixWord ++ tailWord_7060220) baseStart_7060220 baseEnd_7060220 := by
    simpa [prefixWord, tailWord_7060220, baseEnd_7060220] using wordTrace_append hprefix tailTrace_7060220
  have hstable : (prefixWord ++ tailWord_7060220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7060220).length < 2 ^ (prefixWord ++ tailWord_7060220).sum := by decide
  have hdescent : baseEnd_7060220 < baseStart_7060220 := by decide
  rcases family_descends (prefixWord ++ tailWord_7060220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7060234 : List Nat := [3, 1, 2, 2, 1, 2, 1, 5, 1, 3, 2]
def baseStart_7060234 : Nat := 118140960795 + 7060234 * 2 ^ 59
def prefixEnd_7060234 : Nat := 4983230072969 + 3 ^ 40 * 7060234 * 2
def baseEnd_7060234 : Nat := 3625293575215635035705581

theorem tailTrace_7060234 : CollatzResearch.WordTrace tailWord_7060234 prefixEnd_7060234 3625293575215635035705581 := by
  unfold tailWord_7060234
  simp only [CollatzResearch.WordTrace]
  refine ⟨64376972275996371203576939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171671926069323656542871837 64376972275996371203576939)
  ·
    refine ⟨96565458413994556805365409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64376972275996371203576939 96565458413994556805365409)
    ·
      refine ⟨72424093810495917604024057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96565458413994556805365409 72424093810495917604024057)
      ·
        refine ⟨54318070357871938203018043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72424093810495917604024057 54318070357871938203018043)
        ·
          refine ⟨81477105536807907304527065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54318070357871938203018043 81477105536807907304527065)
          ·
            refine ⟨61107829152605930478395299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81477105536807907304527065 61107829152605930478395299)
            ·
              refine ⟨91661743728908895717592949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61107829152605930478395299 91661743728908895717592949)
              ·
                refine ⟨8593288474585208973524339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 91661743728908895717592949 8593288474585208973524339)
                ·
                  refine ⟨12889932711877813460286509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8593288474585208973524339 12889932711877813460286509)
                  ·
                    refine ⟨4833724766954180047607441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12889932711877813460286509 4833724766954180047607441)
                    ·
                      refine ⟨3625293575215635035705581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4833724766954180047607441 3625293575215635035705581)
                      ·
                        rfl

theorem cell23_7060234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 5, 1, 3, 2].length) (baseStart_7060234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7060234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7060234 prefixEnd_7060234 := by exact prefixLift 7060234
  have htrace : WordTrace (prefixWord ++ tailWord_7060234) baseStart_7060234 baseEnd_7060234 := by
    simpa [prefixWord, tailWord_7060234, baseEnd_7060234] using wordTrace_append hprefix tailTrace_7060234
  have hstable : (prefixWord ++ tailWord_7060234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7060234).length < 2 ^ (prefixWord ++ tailWord_7060234).sum := by decide
  have hdescent : baseEnd_7060234 < baseStart_7060234 := by decide
  rcases family_descends (prefixWord ++ tailWord_7060234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7060242 : List Nat := [3, 2, 4, 1, 2, 1, 3, 2, 1, 2, 2]
def baseStart_7060242 : Nat := 118140960795 + 7060242 * 2 ^ 59
def prefixEnd_7060242 : Nat := 4983230072969 + 3 ^ 40 * 7060242 * 2
def baseEnd_7060242 : Nat := 3625297683060871004405545

theorem tailTrace_7060242 : CollatzResearch.WordTrace tailWord_7060242 prefixEnd_7060242 3625297683060871004405545 := by
  unfold tailWord_7060242
  simp only [CollatzResearch.WordTrace]
  refine ⟨64377045221989125545149745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171672120591971001453732653 64377045221989125545149745)
  ·
    refine ⟨48282783916491844158862309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64377045221989125545149745 48282783916491844158862309)
    ·
      refine ⟨9053021984342220779786683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48282783916491844158862309 9053021984342220779786683)
      ·
        refine ⟨13579532976513331169680025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9053021984342220779786683 13579532976513331169680025)
        ·
          refine ⟨10184649732384998377260019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13579532976513331169680025 10184649732384998377260019)
          ·
            refine ⟨15276974598577497565890029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10184649732384998377260019 15276974598577497565890029)
            ·
              refine ⟨5728865474466561587208761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15276974598577497565890029 5728865474466561587208761)
              ·
                refine ⟨4296649105849921190406571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5728865474466561587208761 4296649105849921190406571)
                ·
                  refine ⟨6444973658774881785609857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4296649105849921190406571 6444973658774881785609857)
                  ·
                    refine ⟨4833730244081161339207393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6444973658774881785609857 4833730244081161339207393)
                    ·
                      refine ⟨3625297683060871004405545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4833730244081161339207393 3625297683060871004405545)
                      ·
                        rfl

theorem cell23_7060242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 3, 2, 1, 2, 2].length) (baseStart_7060242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7060242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7060242 prefixEnd_7060242 := by exact prefixLift 7060242
  have htrace : WordTrace (prefixWord ++ tailWord_7060242) baseStart_7060242 baseEnd_7060242 := by
    simpa [prefixWord, tailWord_7060242, baseEnd_7060242] using wordTrace_append hprefix tailTrace_7060242
  have hstable : (prefixWord ++ tailWord_7060242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7060242).length < 2 ^ (prefixWord ++ tailWord_7060242).sum := by decide
  have hdescent : baseEnd_7060242 < baseStart_7060242 := by decide
  rcases family_descends (prefixWord ++ tailWord_7060242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7060250 : List Nat := [3, 1, 1, 3, 2, 1, 1, 2, 1, 3, 5]
def baseStart_7060250 : Nat := 118140960795 + 7060250 * 2 ^ 59
def prefixEnd_7060250 : Nat := 4983230072969 + 3 ^ 40 * 7060250 * 2
def baseEnd_7060250 : Nat := 3625301790906106973105507

theorem tailTrace_7060250 : CollatzResearch.WordTrace tailWord_7060250 prefixEnd_7060250 3625301790906106973105507 := by
  unfold tailWord_7060250
  simp only [CollatzResearch.WordTrace]
  refine ⟨64377118167981879886722551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171672315114618346364593469 64377118167981879886722551)
  ·
    refine ⟨96565677251972819830083827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64377118167981879886722551 96565677251972819830083827)
    ·
      refine ⟨144848515877959229745125741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96565677251972819830083827 144848515877959229745125741)
      ·
        refine ⟨54318193454234711154422153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144848515877959229745125741 54318193454234711154422153)
        ·
          refine ⟨40738645090676033365816615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54318193454234711154422153 40738645090676033365816615)
          ·
            refine ⟨61107967636014050048724923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40738645090676033365816615 61107967636014050048724923)
            ·
              refine ⟨91661951454021075073087385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61107967636014050048724923 91661951454021075073087385)
              ·
                refine ⟨68746463590515806304815539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91661951454021075073087385 68746463590515806304815539)
                ·
                  refine ⟨103119695385773709457223309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68746463590515806304815539 103119695385773709457223309)
                  ·
                    refine ⟨38669885769665141046458741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 103119695385773709457223309 38669885769665141046458741)
                    ·
                      refine ⟨3625301790906106973105507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38669885769665141046458741 3625301790906106973105507)
                      ·
                        rfl

theorem cell23_7060250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 2, 1, 3, 5].length) (baseStart_7060250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7060250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7060250 prefixEnd_7060250 := by exact prefixLift 7060250
  have htrace : WordTrace (prefixWord ++ tailWord_7060250) baseStart_7060250 baseEnd_7060250 := by
    simpa [prefixWord, tailWord_7060250, baseEnd_7060250] using wordTrace_append hprefix tailTrace_7060250
  have hstable : (prefixWord ++ tailWord_7060250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7060250).length < 2 ^ (prefixWord ++ tailWord_7060250).sum := by decide
  have hdescent : baseEnd_7060250 < baseStart_7060250 := by decide
  rcases family_descends (prefixWord ++ tailWord_7060250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7060258 : List Nat := [3, 3, 1, 1, 2, 4, 2, 1, 2, 1, 3]
def baseStart_7060258 : Nat := 118140960795 + 7060258 * 2 ^ 59
def prefixEnd_7060258 : Nat := 4983230072969 + 3 ^ 40 * 7060258 * 2
def baseEnd_7060258 : Nat := 3625305898751342941805471

theorem tailTrace_7060258 : CollatzResearch.WordTrace tailWord_7060258 prefixEnd_7060258 3625305898751342941805471 := by
  unfold tailWord_7060258
  simp only [CollatzResearch.WordTrace]
  refine ⟨64377191113974634228295357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171672509637265691275454285 64377191113974634228295357)
  ·
    refine ⟨24141446667740487835610759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64377191113974634228295357 24141446667740487835610759)
    ·
      refine ⟨36212170001610731753416139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24141446667740487835610759 36212170001610731753416139)
      ·
        refine ⟨54318255002416097630124209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36212170001610731753416139 54318255002416097630124209)
        ·
          refine ⟨40738691251812073222593157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54318255002416097630124209 40738691251812073222593157)
          ·
            refine ⟨7638504609714763729236217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40738691251812073222593157 7638504609714763729236217)
            ·
              refine ⟨5728878457286072796927163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7638504609714763729236217 5728878457286072796927163)
              ·
                refine ⟨8593317685929109195390745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5728878457286072796927163 8593317685929109195390745)
                ·
                  refine ⟨6444988264446831896543059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8593317685929109195390745 6444988264446831896543059)
                  ·
                    refine ⟨9667482396670247844814589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6444988264446831896543059 9667482396670247844814589)
                    ·
                      refine ⟨3625305898751342941805471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9667482396670247844814589 3625305898751342941805471)
                      ·
                        rfl

theorem cell23_7060258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 2, 1, 2, 1, 3].length) (baseStart_7060258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7060258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7060258 prefixEnd_7060258 := by exact prefixLift 7060258
  have htrace : WordTrace (prefixWord ++ tailWord_7060258) baseStart_7060258 baseEnd_7060258 := by
    simpa [prefixWord, tailWord_7060258, baseEnd_7060258] using wordTrace_append hprefix tailTrace_7060258
  have hstable : (prefixWord ++ tailWord_7060258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7060258).length < 2 ^ (prefixWord ++ tailWord_7060258).sum := by decide
  have hdescent : baseEnd_7060258 < baseStart_7060258 := by decide
  rcases family_descends (prefixWord ++ tailWord_7060258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7060264 : List Nat := [2, 1, 5, 1, 1, 1, 2, 3, 1, 4, 2]
def baseStart_7060264 : Nat := 118140960795 + 7060264 * 2 ^ 59
def prefixEnd_7060264 : Nat := 4983230072969 + 3 ^ 40 * 7060264 * 2
def baseEnd_7060264 : Nat := 3625308979635269918330443

theorem tailTrace_7060264 : CollatzResearch.WordTrace tailWord_7060264 prefixEnd_7060264 3625308979635269918330443 := by
  unfold tailWord_7060264
  simp only [CollatzResearch.WordTrace]
  refine ⟨128754491646938399968949923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171672655529251199958599897 128754491646938399968949923)
  ·
    refine ⟨193131737470407599953424885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128754491646938399968949923 193131737470407599953424885)
    ·
      refine ⟨18106100387850712495633583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 193131737470407599953424885 18106100387850712495633583)
      ·
        refine ⟨27159150581776068743450375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18106100387850712495633583 27159150581776068743450375)
        ·
          refine ⟨40738725872664103115175563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27159150581776068743450375 40738725872664103115175563)
          ·
            refine ⟨61108088808996154672763345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40738725872664103115175563 61108088808996154672763345)
            ·
              refine ⟨45831066606747116004572509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61108088808996154672763345 45831066606747116004572509)
              ·
                refine ⟨17186649977530168501714691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45831066606747116004572509 17186649977530168501714691)
                ·
                  refine ⟨25779974966295252752572037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17186649977530168501714691 25779974966295252752572037)
                  ·
                    refine ⟨4833745306180359891107257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25779974966295252752572037 4833745306180359891107257)
                    ·
                      refine ⟨3625308979635269918330443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4833745306180359891107257 3625308979635269918330443)
                      ·
                        rfl

theorem cell23_7060264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 3, 1, 4, 2].length) (baseStart_7060264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7060264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7060264 prefixEnd_7060264 := by exact prefixLift 7060264
  have htrace : WordTrace (prefixWord ++ tailWord_7060264) baseStart_7060264 baseEnd_7060264 := by
    simpa [prefixWord, tailWord_7060264, baseEnd_7060264] using wordTrace_append hprefix tailTrace_7060264
  have hstable : (prefixWord ++ tailWord_7060264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7060264).length < 2 ^ (prefixWord ++ tailWord_7060264).sum := by decide
  have hdescent : baseEnd_7060264 < baseStart_7060264 := by decide
  rcases family_descends (prefixWord ++ tailWord_7060264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7060304 : List Nat := [2, 1, 1, 1, 1, 4, 6, 2, 5]
def baseStart_7060304 : Nat := 118140960795 + 7060304 * 2 ^ 59
def prefixEnd_7060304 : Nat := 4983230072969 + 3 ^ 40 * 7060304 * 2
def baseEnd_7060304 : Nat := 402814390984605529092251

theorem tailTrace_7060304 : CollatzResearch.WordTrace tailWord_7060304 prefixEnd_7060304 402814390984605529092251 := by
  unfold tailWord_7060304
  simp only [CollatzResearch.WordTrace]
  refine ⟨128755221106865943384677983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171673628142487924512903977 128755221106865943384677983)
  ·
    refine ⟨193132831660298915077016975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128755221106865943384677983 193132831660298915077016975)
    ·
      refine ⟨289699247490448372615525463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193132831660298915077016975 289699247490448372615525463)
      ·
        refine ⟨434548871235672558923288195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 289699247490448372615525463 434548871235672558923288195)
        ·
          refine ⟨651823306853508838384932293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 434548871235672558923288195 651823306853508838384932293)
          ·
            refine ⟨122216870035032907197174805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 651823306853508838384932293 122216870035032907197174805)
            ·
              refine ⟨5728915782892167524867569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 122216870035032907197174805 5728915782892167524867569)
              ·
                refine ⟨4296686837169125643650677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5728915782892167524867569 4296686837169125643650677)
                ·
                  refine ⟨402814390984605529092251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4296686837169125643650677 402814390984605529092251)
                  ·
                    rfl

theorem cell23_7060304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 6, 2, 5].length) (baseStart_7060304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7060304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7060304 prefixEnd_7060304 := by exact prefixLift 7060304
  have htrace : WordTrace (prefixWord ++ tailWord_7060304) baseStart_7060304 baseEnd_7060304 := by
    simpa [prefixWord, tailWord_7060304, baseEnd_7060304] using wordTrace_append hprefix tailTrace_7060304
  have hstable : (prefixWord ++ tailWord_7060304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7060304).length < 2 ^ (prefixWord ++ tailWord_7060304).sum := by decide
  have hdescent : baseEnd_7060304 < baseStart_7060304 := by decide
  rcases family_descends (prefixWord ++ tailWord_7060304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7060334 : List Nat := [4, 1, 2, 3, 2, 1, 1, 1, 1, 7]
def baseStart_7060334 : Nat := 118140960795 + 7060334 * 2 ^ 59
def prefixEnd_7060334 : Nat := 4983230072969 + 3 ^ 40 * 7060334 * 2
def baseEnd_7060334 : Nat := 1208448307760361548151707

theorem tailTrace_7060334 : CollatzResearch.WordTrace tailWord_7060334 prefixEnd_7060334 1208448307760361548151707 := by
  unfold tailWord_7060334
  simp only [CollatzResearch.WordTrace]
  refine ⟨32188942050452900236618507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 171674357602415467928632037 32188942050452900236618507)
  ·
    refine ⟨48283413075679350354927761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32188942050452900236618507 48283413075679350354927761)
    ·
      refine ⟨36212559806759512766195821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48283413075679350354927761 36212559806759512766195821)
      ·
        refine ⟨13579709927534817287323433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36212559806759512766195821 13579709927534817287323433)
        ·
          refine ⟨10184782445651112965492575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13579709927534817287323433 10184782445651112965492575)
          ·
            refine ⟨15277173668476669448238863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10184782445651112965492575 15277173668476669448238863)
            ·
              refine ⟨22915760502715004172358295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15277173668476669448238863 22915760502715004172358295)
              ·
                refine ⟨34373640754072506258537443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22915760502715004172358295 34373640754072506258537443)
                ·
                  refine ⟨51560461131108759387806165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34373640754072506258537443 51560461131108759387806165)
                  ·
                    refine ⟨1208448307760361548151707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51560461131108759387806165 1208448307760361548151707)
                    ·
                      rfl

theorem cell23_7060334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 1, 1, 7].length) (baseStart_7060334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7060334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7060334 prefixEnd_7060334 := by exact prefixLift 7060334
  have htrace : WordTrace (prefixWord ++ tailWord_7060334) baseStart_7060334 baseEnd_7060334 := by
    simpa [prefixWord, tailWord_7060334, baseEnd_7060334] using wordTrace_append hprefix tailTrace_7060334
  have hstable : (prefixWord ++ tailWord_7060334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7060334).length < 2 ^ (prefixWord ++ tailWord_7060334).sum := by decide
  have hdescent : baseEnd_7060334 < baseStart_7060334 := by decide
  rcases family_descends (prefixWord ++ tailWord_7060334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7060337 : List Nat := [1, 2, 2, 2, 1, 5, 1, 1, 1, 3, 4]
def baseStart_7060337 : Nat := 118140960795 + 7060337 * 2 ^ 59
def prefixEnd_7060337 : Nat := 4983230072969 + 3 ^ 40 * 7060337 * 2
def baseEnd_7060337 : Nat := 3625346463723048132717607

theorem tailTrace_7060337 : CollatzResearch.WordTrace tailWord_7060337 prefixEnd_7060337 3625346463723048132717607 := by
  unfold tailWord_7060337
  simp only [CollatzResearch.WordTrace]
  refine ⟨257511645822612333405307265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171674430548408222270204843 257511645822612333405307265)
  ·
    refine ⟨193133734366959250053980449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257511645822612333405307265 193133734366959250053980449)
    ·
      refine ⟨144850300775219437540485337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193133734366959250053980449 144850300775219437540485337)
      ·
        refine ⟨108637725581414578155364003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144850300775219437540485337 108637725581414578155364003)
        ·
          refine ⟨162956588372121867233046005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108637725581414578155364003 162956588372121867233046005)
          ·
            refine ⟨15277180159886425053098063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 162956588372121867233046005 15277180159886425053098063)
            ·
              refine ⟨22915770239829637579647095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15277180159886425053098063 22915770239829637579647095)
              ·
                refine ⟨34373655359744456369470643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22915770239829637579647095 34373655359744456369470643)
                ·
                  refine ⟨51560483039616684554205965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34373655359744456369470643 51560483039616684554205965)
                  ·
                    refine ⟨19335181139856256707827237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51560483039616684554205965 19335181139856256707827237)
                    ·
                      refine ⟨3625346463723048132717607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19335181139856256707827237 3625346463723048132717607)
                      ·
                        rfl

theorem cell23_7060337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 1, 1, 3, 4].length) (baseStart_7060337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7060337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7060337 prefixEnd_7060337 := by exact prefixLift 7060337
  have htrace : WordTrace (prefixWord ++ tailWord_7060337) baseStart_7060337 baseEnd_7060337 := by
    simpa [prefixWord, tailWord_7060337, baseEnd_7060337] using wordTrace_append hprefix tailTrace_7060337
  have hstable : (prefixWord ++ tailWord_7060337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7060337).length < 2 ^ (prefixWord ++ tailWord_7060337).sum := by decide
  have hdescent : baseEnd_7060337 < baseStart_7060337 := by decide
  rcases family_descends (prefixWord ++ tailWord_7060337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7060441 : List Nat := [1, 2, 1, 2, 5, 3, 1, 2, 1, 5]
def baseStart_7060441 : Nat := 118140960795 + 7060441 * 2 ^ 59
def prefixEnd_7060441 : Nat := 4983230072969 + 3 ^ 40 * 7060441 * 2
def baseEnd_7060441 : Nat := 1208466621903705241939043

theorem tailTrace_7060441 : CollatzResearch.WordTrace tailWord_7060441 prefixEnd_7060441 1208466621903705241939043 := by
  unfold tailWord_7060441
  simp only [CollatzResearch.WordTrace]
  refine ⟨257515439014235559167093177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171676959342823706111395451 257515439014235559167093177)
  ·
    refine ⟨193136579260676669375319883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257515439014235559167093177 193136579260676669375319883)
    ·
      refine ⟨289704868891015004062979825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193136579260676669375319883 289704868891015004062979825)
      ·
        refine ⟨217278651668261253047234869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 289704868891015004062979825 217278651668261253047234869)
        ·
          refine ⟨20369873593899492473178269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 217278651668261253047234869 20369873593899492473178269)
          ·
            refine ⟨7638702597712309677441851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20369873593899492473178269 7638702597712309677441851)
            ·
              refine ⟨11458053896568464516162777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7638702597712309677441851 11458053896568464516162777)
              ·
                refine ⟨8593540422426348387122083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11458053896568464516162777 8593540422426348387122083)
                ·
                  refine ⟨12890310633639522580683125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8593540422426348387122083 12890310633639522580683125)
                  ·
                    refine ⟨1208466621903705241939043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12890310633639522580683125 1208466621903705241939043)
                    ·
                      rfl

theorem cell23_7060441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 1, 2, 1, 5].length) (baseStart_7060441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7060441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7060441 prefixEnd_7060441 := by exact prefixLift 7060441
  have htrace : WordTrace (prefixWord ++ tailWord_7060441) baseStart_7060441 baseEnd_7060441 := by
    simpa [prefixWord, tailWord_7060441, baseEnd_7060441] using wordTrace_append hprefix tailTrace_7060441
  have hstable : (prefixWord ++ tailWord_7060441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7060441).length < 2 ^ (prefixWord ++ tailWord_7060441).sum := by decide
  have hdescent : baseEnd_7060441 < baseStart_7060441 := by decide
  rcases family_descends (prefixWord ++ tailWord_7060441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7060512 : List Nat := [2, 1, 1, 7, 2, 1, 2, 1, 1, 1, 4]
def baseStart_7060512 : Nat := 118140960795 + 7060512 * 2 ^ 59
def prefixEnd_7060512 : Nat := 4983230072969 + 3 ^ 40 * 7060512 * 2
def baseEnd_7060512 : Nat := 3625436322837584948029303

theorem tailTrace_7060512 : CollatzResearch.WordTrace tailWord_7060512 prefixEnd_7060512 3625436322837584948029303 := by
  unfold tailWord_7060512
  simp only [CollatzResearch.WordTrace]
  refine ⟨128759014298489169146463895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171678685731318892195285193 128759014298489169146463895)
  ·
    refine ⟨193138521447733753719695843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128759014298489169146463895 193138521447733753719695843)
    ·
      refine ⟨289707782171600630579543765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193138521447733753719695843 289707782171600630579543765)
      ·
        refine ⟨6790026144646889779208057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 289707782171600630579543765 6790026144646889779208057)
        ·
          refine ⟨5092519608485167334406043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6790026144646889779208057 5092519608485167334406043)
          ·
            refine ⟨7638779412727751001609065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5092519608485167334406043 7638779412727751001609065)
            ·
              refine ⟨5729084559545813251206799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7638779412727751001609065 5729084559545813251206799)
              ·
                refine ⟨8593626839318719876810199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5729084559545813251206799 8593626839318719876810199)
                ·
                  refine ⟨12890440258978079815215299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8593626839318719876810199 12890440258978079815215299)
                  ·
                    refine ⟨19335660388467119722822949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12890440258978079815215299 19335660388467119722822949)
                    ·
                      refine ⟨3625436322837584948029303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19335660388467119722822949 3625436322837584948029303)
                      ·
                        rfl

theorem cell23_7060512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 2, 1, 1, 1, 4].length) (baseStart_7060512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7060512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7060512 prefixEnd_7060512 := by exact prefixLift 7060512
  have htrace : WordTrace (prefixWord ++ tailWord_7060512) baseStart_7060512 baseEnd_7060512 := by
    simpa [prefixWord, tailWord_7060512, baseEnd_7060512] using wordTrace_append hprefix tailTrace_7060512
  have hstable : (prefixWord ++ tailWord_7060512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7060512).length < 2 ^ (prefixWord ++ tailWord_7060512).sum := by decide
  have hdescent : baseEnd_7060512 < baseStart_7060512 := by decide
  rcases family_descends (prefixWord ++ tailWord_7060512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7060545 : List Nat := [1, 2, 5, 1, 4, 1, 1, 1, 1, 3, 3]
def baseStart_7060545 : Nat := 118140960795 + 7060545 * 2 ^ 59
def prefixEnd_7060545 : Nat := 4983230072969 + 3 ^ 40 * 7060545 * 2
def baseEnd_7060545 : Nat := 3625453267699183318916651

theorem tailTrace_7060545 : CollatzResearch.WordTrace tailWord_7060545 prefixEnd_7060545 3625453267699183318916651 := by
  unfold tailWord_7060545
  simp only [CollatzResearch.WordTrace]
  refine ⟨257519232205858784928879089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171679488137239189952586059 257519232205858784928879089)
  ·
    refine ⟨193139424154394088696659317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257519232205858784928879089 193139424154394088696659317)
    ·
      refine ⟨18106821014474445815311811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 193139424154394088696659317 18106821014474445815311811)
      ·
        refine ⟨27160231521711668722967717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18106821014474445815311811 27160231521711668722967717)
        ·
          refine ⟨5092543410320937885556447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27160231521711668722967717 5092543410320937885556447)
          ·
            refine ⟨7638815115481406828334671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5092543410320937885556447 7638815115481406828334671)
            ·
              refine ⟨11458222673222110242502007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7638815115481406828334671 11458222673222110242502007)
              ·
                refine ⟨17187334009833165363753011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11458222673222110242502007 17187334009833165363753011)
                ·
                  refine ⟨25781001014749748045629517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17187334009833165363753011 25781001014749748045629517)
                  ·
                    refine ⟨9667875380531155517111069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25781001014749748045629517 9667875380531155517111069)
                    ·
                      refine ⟨3625453267699183318916651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9667875380531155517111069 3625453267699183318916651)
                      ·
                        rfl

theorem cell23_7060545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 1, 1, 1, 3, 3].length) (baseStart_7060545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7060545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7060545 prefixEnd_7060545 := by exact prefixLift 7060545
  have htrace : WordTrace (prefixWord ++ tailWord_7060545) baseStart_7060545 baseEnd_7060545 := by
    simpa [prefixWord, tailWord_7060545, baseEnd_7060545] using wordTrace_append hprefix tailTrace_7060545
  have hstable : (prefixWord ++ tailWord_7060545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7060545).length < 2 ^ (prefixWord ++ tailWord_7060545).sum := by decide
  have hdescent : baseEnd_7060545 < baseStart_7060545 := by decide
  rcases family_descends (prefixWord ++ tailWord_7060545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7060554 : List Nat := [3, 1, 2, 1, 1, 2, 2, 2, 2, 4, 3]
def baseStart_7060554 : Nat := 118140960795 + 7060554 * 2 ^ 59
def prefixEnd_7060554 : Nat := 4983230072969 + 3 ^ 40 * 7060554 * 2
def baseEnd_7060554 : Nat := 3625457889025073783704109

theorem tailTrace_7060554 : CollatzResearch.WordTrace tailWord_7060554 prefixEnd_7060554 3625457889025073783704109 := by
  unfold tailWord_7060554
  simp only [CollatzResearch.WordTrace]
  refine ⟨64379890115706544866489179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171679706975217452977304477 64379890115706544866489179)
  ·
    refine ⟨96569835173559817299733769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64379890115706544866489179 96569835173559817299733769)
    ·
      refine ⟨72427376380169862974800327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96569835173559817299733769 72427376380169862974800327)
      ·
        refine ⟨108641064570254794462200491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72427376380169862974800327 108641064570254794462200491)
        ·
          refine ⟨162961596855382191693300737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108641064570254794462200491 162961596855382191693300737)
          ·
            refine ⟨122221197641536643769975553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162961596855382191693300737 122221197641536643769975553)
            ·
              refine ⟨91665898231152482827481665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122221197641536643769975553 91665898231152482827481665)
              ·
                refine ⟨68749423673364362120611249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91665898231152482827481665 68749423673364362120611249)
                ·
                  refine ⟨51562067755023271590458437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68749423673364362120611249 51562067755023271590458437)
                  ·
                    refine ⟨9667887704066863423210957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51562067755023271590458437 9667887704066863423210957)
                    ·
                      refine ⟨3625457889025073783704109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9667887704066863423210957 3625457889025073783704109)
                      ·
                        rfl

theorem cell23_7060554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 2, 2, 4, 3].length) (baseStart_7060554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7060554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7060554 prefixEnd_7060554 := by exact prefixLift 7060554
  have htrace : WordTrace (prefixWord ++ tailWord_7060554) baseStart_7060554 baseEnd_7060554 := by
    simpa [prefixWord, tailWord_7060554, baseEnd_7060554] using wordTrace_append hprefix tailTrace_7060554
  have hstable : (prefixWord ++ tailWord_7060554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7060554).length < 2 ^ (prefixWord ++ tailWord_7060554).sum := by decide
  have hdescent : baseEnd_7060554 < baseStart_7060554 := by decide
  rcases family_descends (prefixWord ++ tailWord_7060554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7060564 : List Nat := [2, 4, 1, 1, 1, 1, 2, 2, 1, 4, 4]
def baseStart_7060564 : Nat := 118140960795 + 7060564 * 2 ^ 59
def prefixEnd_7060564 : Nat := 4983230072969 + 3 ^ 40 * 7060564 * 2
def baseEnd_7060564 : Nat := 3625463023831618744579063

theorem tailTrace_7060564 : CollatzResearch.WordTrace tailWord_7060564 prefixEnd_7060564 3625463023831618744579063 := by
  unfold tailWord_7060564
  simp only [CollatzResearch.WordTrace]
  refine ⟨128759962596394975586910373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171679950128526634115880497 128759962596394975586910373)
  ·
    refine ⟨24142492986824057922545695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 128759962596394975586910373 24142492986824057922545695)
    ·
      refine ⟨36213739480236086883818543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24142492986824057922545695 36213739480236086883818543)
      ·
        refine ⟨54320609220354130325727815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36213739480236086883818543 54320609220354130325727815)
        ·
          refine ⟨81480913830531195488591723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54320609220354130325727815 81480913830531195488591723)
          ·
            refine ⟨122221370745796793232887585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81480913830531195488591723 122221370745796793232887585)
            ·
              refine ⟨91666028059347594924665689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122221370745796793232887585 91666028059347594924665689)
              ·
                refine ⟨68749521044510696193499267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91666028059347594924665689 68749521044510696193499267)
                ·
                  refine ⟨103124281566766044290248901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68749521044510696193499267 103124281566766044290248901)
                  ·
                    refine ⟨19335802793768633304421669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 103124281566766044290248901 19335802793768633304421669)
                    ·
                      refine ⟨3625463023831618744579063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19335802793768633304421669 3625463023831618744579063)
                      ·
                        rfl

theorem cell23_7060564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 2, 1, 4, 4].length) (baseStart_7060564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7060564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7060564 prefixEnd_7060564 := by exact prefixLift 7060564
  have htrace : WordTrace (prefixWord ++ tailWord_7060564) baseStart_7060564 baseEnd_7060564 := by
    simpa [prefixWord, tailWord_7060564, baseEnd_7060564] using wordTrace_append hprefix tailTrace_7060564
  have hstable : (prefixWord ++ tailWord_7060564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7060564).length < 2 ^ (prefixWord ++ tailWord_7060564).sum := by decide
  have hdescent : baseEnd_7060564 < baseStart_7060564 := by decide
  rcases family_descends (prefixWord ++ tailWord_7060564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7060587 : List Nat := [1, 1, 1, 1, 2, 2, 1, 1, 2, 11]
def baseStart_7060587 : Nat := 118140960795 + 7060587 * 2 ^ 59
def prefixEnd_7060587 : Nat := 4983230072969 + 3 ^ 40 * 7060587 * 2
def baseEnd_7060587 : Nat := 1208491611295557384863819

theorem tailTrace_7060587 : CollatzResearch.WordTrace tailWord_7060587 prefixEnd_7060587 1208491611295557384863819 := by
  unfold tailWord_7060587
  simp only [CollatzResearch.WordTrace]
  refine ⟨257520764071706626101908015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171680509381137750734605343 257520764071706626101908015)
  ·
    refine ⟨386281146107559939152862023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257520764071706626101908015 386281146107559939152862023)
    ·
      refine ⟨579421719161339908729293035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 386281146107559939152862023 579421719161339908729293035)
      ·
        refine ⟨869132578742009863093939553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 579421719161339908729293035 869132578742009863093939553)
        ·
          refine ⟨651849434056507397320454665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 869132578742009863093939553 651849434056507397320454665)
          ·
            refine ⟨488887075542380547990340999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 651849434056507397320454665 488887075542380547990340999)
            ·
              refine ⟨733330613313570821985511499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 488887075542380547990340999 733330613313570821985511499)
              ·
                refine ⟨1099995919970356232978267249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 733330613313570821985511499 1099995919970356232978267249)
                ·
                  refine ⟨824996939977767174733700437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1099995919970356232978267249 824996939977767174733700437)
                  ·
                    refine ⟨1208491611295557384863819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 824996939977767174733700437 1208491611295557384863819)
                    ·
                      rfl

theorem cell23_7060587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 11].length) (baseStart_7060587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7060587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7060587 prefixEnd_7060587 := by exact prefixLift 7060587
  have htrace : WordTrace (prefixWord ++ tailWord_7060587) baseStart_7060587 baseEnd_7060587 := by
    simpa [prefixWord, tailWord_7060587, baseEnd_7060587] using wordTrace_append hprefix tailTrace_7060587
  have hstable : (prefixWord ++ tailWord_7060587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7060587).length < 2 ^ (prefixWord ++ tailWord_7060587).sum := by decide
  have hdescent : baseEnd_7060587 < baseStart_7060587 := by decide
  rcases family_descends (prefixWord ++ tailWord_7060587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7060604 : List Nat := [2, 2, 2, 1, 1, 3, 1, 2, 4, 5]
def baseStart_7060604 : Nat := 118140960795 + 7060604 * 2 ^ 59
def prefixEnd_7060604 : Nat := 4983230072969 + 3 ^ 40 * 7060604 * 2
def baseEnd_7060604 : Nat := 1208494521019266196026293

theorem tailTrace_7060604 : CollatzResearch.WordTrace tailWord_7060604 prefixEnd_7060604 1208494521019266196026293 := by
  unfold tailWord_7060604
  simp only [CollatzResearch.WordTrace]
  refine ⟨128760692056322519002638433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171680922741763358670184577 128760692056322519002638433)
  ·
    refine ⟨96570519042241889251978825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128760692056322519002638433 96570519042241889251978825)
    ·
      refine ⟨72427889281681416938984119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96570519042241889251978825 72427889281681416938984119)
      ·
        refine ⟨108641833922522125408476179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72427889281681416938984119 108641833922522125408476179)
        ·
          refine ⟨162962750883783188112714269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108641833922522125408476179 162962750883783188112714269)
          ·
            refine ⟨61111031581418695542267851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 162962750883783188112714269 61111031581418695542267851)
            ·
              refine ⟨91666547372128043313401777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61111031581418695542267851 91666547372128043313401777)
              ·
                refine ⟨68749910529096032485051333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91666547372128043313401777 68749910529096032485051333)
                ·
                  refine ⟨12890608224205506090947125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 68749910529096032485051333 12890608224205506090947125)
                  ·
                    refine ⟨1208494521019266196026293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12890608224205506090947125 1208494521019266196026293)
                    ·
                      rfl

theorem cell23_7060604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 2, 4, 5].length) (baseStart_7060604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7060604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7060604 prefixEnd_7060604 := by exact prefixLift 7060604
  have htrace : WordTrace (prefixWord ++ tailWord_7060604) baseStart_7060604 baseEnd_7060604 := by
    simpa [prefixWord, tailWord_7060604, baseEnd_7060604] using wordTrace_append hprefix tailTrace_7060604
  have hstable : (prefixWord ++ tailWord_7060604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7060604).length < 2 ^ (prefixWord ++ tailWord_7060604).sum := by decide
  have hdescent : baseEnd_7060604 < baseStart_7060604 := by decide
  rcases family_descends (prefixWord ++ tailWord_7060604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7060606 : List Nat := [4, 2, 4, 1, 1, 2, 1, 2, 1, 3, 2]
def baseStart_7060606 : Nat := 118140960795 + 7060606 * 2 ^ 59
def prefixEnd_7060606 : Nat := 4983230072969 + 3 ^ 40 * 7060606 * 2
def baseEnd_7060606 : Nat := 3625484590019107580253871

theorem tailTrace_7060606 : CollatzResearch.WordTrace tailWord_7060606 prefixEnd_7060606 3625484590019107580253871 := by
  unfold tailWord_7060606
  simp only [CollatzResearch.WordTrace]
  refine ⟨32190182132329724043356209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 171680971372425194897899781 32190182132329724043356209)
  ·
    refine ⟨24142636599247293032517157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32190182132329724043356209 24142636599247293032517157)
    ·
      refine ⟨4526744362358867443596967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24142636599247293032517157 4526744362358867443596967)
      ·
        refine ⟨6790116543538301165395451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4526744362358867443596967 6790116543538301165395451)
        ·
          refine ⟨10185174815307451748093177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6790116543538301165395451 10185174815307451748093177)
          ·
            refine ⟨7638881111480588811069883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10185174815307451748093177 7638881111480588811069883)
            ·
              refine ⟨11458321667220883216604825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7638881111480588811069883 11458321667220883216604825)
              ·
                refine ⟨8593741250415662412453619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11458321667220883216604825 8593741250415662412453619)
                ·
                  refine ⟨12890611875623493618680429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8593741250415662412453619 12890611875623493618680429)
                  ·
                    refine ⟨4833979453358810107005161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12890611875623493618680429 4833979453358810107005161)
                    ·
                      refine ⟨3625484590019107580253871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4833979453358810107005161 3625484590019107580253871)
                      ·
                        rfl

theorem cell23_7060606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 1, 2, 1, 3, 2].length) (baseStart_7060606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7060606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7060606 prefixEnd_7060606 := by exact prefixLift 7060606
  have htrace : WordTrace (prefixWord ++ tailWord_7060606) baseStart_7060606 baseEnd_7060606 := by
    simpa [prefixWord, tailWord_7060606, baseEnd_7060606] using wordTrace_append hprefix tailTrace_7060606
  have hstable : (prefixWord ++ tailWord_7060606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7060606).length < 2 ^ (prefixWord ++ tailWord_7060606).sum := by decide
  have hdescent : baseEnd_7060606 < baseStart_7060606 := by decide
  rcases family_descends (prefixWord ++ tailWord_7060606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7060638 : List Nat := [4, 3, 1, 1, 2, 1, 2, 2, 2, 5]
def baseStart_7060638 : Nat := 118140960795 + 7060638 * 2 ^ 59
def prefixEnd_7060638 : Nat := 4983230072969 + 3 ^ 40 * 7060638 * 2
def baseEnd_7060638 : Nat := 1208500340466683818351241

theorem tailTrace_7060638 : CollatzResearch.WordTrace tailWord_7060638 prefixEnd_7060638 1208500340466683818351241 := by
  unfold tailWord_7060638
  simp only [CollatzResearch.WordTrace]
  refine ⟨32190328024315232726501821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 171681749463014574541343045 32190328024315232726501821)
  ·
    refine ⟨12071373009118212272438183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32190328024315232726501821 12071373009118212272438183)
    ·
      refine ⟨18107059513677318408657275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12071373009118212272438183 18107059513677318408657275)
      ·
        refine ⟨27160589270515977612985913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18107059513677318408657275 27160589270515977612985913)
        ·
          refine ⟨20370441952886983209739435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27160589270515977612985913 20370441952886983209739435)
          ·
            refine ⟨30555662929330474814609153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20370441952886983209739435 30555662929330474814609153)
            ·
              refine ⟨22916747196997856110956865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30555662929330474814609153 22916747196997856110956865)
              ·
                refine ⟨17187560397748392083217649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22916747196997856110956865 17187560397748392083217649)
                ·
                  refine ⟨12890670298311294062413237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17187560397748392083217649 12890670298311294062413237)
                  ·
                    refine ⟨1208500340466683818351241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12890670298311294062413237 1208500340466683818351241)
                    ·
                      rfl

theorem cell23_7060638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 2, 2, 5].length) (baseStart_7060638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7060638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7060638 prefixEnd_7060638 := by exact prefixLift 7060638
  have htrace : WordTrace (prefixWord ++ tailWord_7060638) baseStart_7060638 baseEnd_7060638 := by
    simpa [prefixWord, tailWord_7060638, baseEnd_7060638] using wordTrace_append hprefix tailTrace_7060638
  have hstable : (prefixWord ++ tailWord_7060638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7060638).length < 2 ^ (prefixWord ++ tailWord_7060638).sum := by decide
  have hdescent : baseEnd_7060638 < baseStart_7060638 := by decide
  rcases family_descends (prefixWord ++ tailWord_7060638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7060641 : List Nat := [1, 2, 3, 3, 1, 1, 1, 4, 2, 1, 4]
def baseStart_7060641 : Nat := 118140960795 + 7060641 * 2 ^ 59
def prefixEnd_7060641 : Nat := 4983230072969 + 3 ^ 40 * 7060641 * 2
def baseEnd_7060641 : Nat := 3625502561842014943316209

theorem tailTrace_7060641 : CollatzResearch.WordTrace tailWord_7060641 prefixEnd_7060641 3625502561842014943316209 := by
  unfold tailWord_7060641
  simp only [CollatzResearch.WordTrace]
  refine ⟨257522733613510993324373777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171681822409007328882915851 257522733613510993324373777)
  ·
    refine ⟨193142050210133244993280333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257522733613510993324373777 193142050210133244993280333)
    ·
      refine ⟨72428268828799966872480125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 193142050210133244993280333 72428268828799966872480125)
      ·
        refine ⟨27160600810799987577180047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72428268828799966872480125 27160600810799987577180047)
        ·
          refine ⟨40740901216199981365770071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27160600810799987577180047 40740901216199981365770071)
          ·
            refine ⟨61111351824299972048655107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40740901216199981365770071 61111351824299972048655107)
            ·
              refine ⟨91667027736449958072982661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61111351824299972048655107 91667027736449958072982661)
              ·
                refine ⟨17187567700584367138684249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 91667027736449958072982661 17187567700584367138684249)
                ·
                  refine ⟨12890675775438275354013187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17187567700584367138684249 12890675775438275354013187)
                  ·
                    refine ⟨19336013663157413031019781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12890675775438275354013187 19336013663157413031019781)
                    ·
                      refine ⟨3625502561842014943316209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19336013663157413031019781 3625502561842014943316209)
                      ·
                        rfl

theorem cell23_7060641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 4, 2, 1, 4].length) (baseStart_7060641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7060641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7060641 prefixEnd_7060641 := by exact prefixLift 7060641
  have htrace : WordTrace (prefixWord ++ tailWord_7060641) baseStart_7060641 baseEnd_7060641 := by
    simpa [prefixWord, tailWord_7060641, baseEnd_7060641] using wordTrace_append hprefix tailTrace_7060641
  have hstable : (prefixWord ++ tailWord_7060641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7060641).length < 2 ^ (prefixWord ++ tailWord_7060641).sum := by decide
  have hdescent : baseEnd_7060641 < baseStart_7060641 := by decide
  rcases family_descends (prefixWord ++ tailWord_7060641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7060642 : List Nat := [3, 3, 1, 3, 2, 2, 2, 2, 5]
def baseStart_7060642 : Nat := 118140960795 + 7060642 * 2 ^ 59
def prefixEnd_7060642 : Nat := 4983230072969 + 3 ^ 40 * 7060642 * 2
def baseEnd_7060642 : Nat := 402833675035852159933745

theorem tailTrace_7060642 : CollatzResearch.WordTrace tailWord_7060642 prefixEnd_7060642 402833675035852159933745 := by
  unfold tailWord_7060642
  simp only [CollatzResearch.WordTrace]
  refine ⟨64380692521626842623790045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171681846724338246996773453 64380692521626842623790045)
  ·
    refine ⟨24142759695610065983921267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64380692521626842623790045 24142759695610065983921267)
    ·
      refine ⟨36214139543415098975881901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24142759695610065983921267 36214139543415098975881901)
      ·
        refine ⟨13580302328780662115955713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36214139543415098975881901 13580302328780662115955713)
        ·
          refine ⟨10185226746585496586966785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13580302328780662115955713 10185226746585496586966785)
          ·
            refine ⟨7638920059939122440225089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10185226746585496586966785 7638920059939122440225089)
            ·
              refine ⟨5729190044954341830168817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7638920059939122440225089 5729190044954341830168817)
              ·
                refine ⟨4296892533715756372626613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5729190044954341830168817 4296892533715756372626613)
                ·
                  refine ⟨402833675035852159933745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4296892533715756372626613 402833675035852159933745)
                  ·
                    rfl

theorem cell23_7060642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 2, 2, 5].length) (baseStart_7060642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7060642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7060642 prefixEnd_7060642 := by exact prefixLift 7060642
  have htrace : WordTrace (prefixWord ++ tailWord_7060642) baseStart_7060642 baseEnd_7060642 := by
    simpa [prefixWord, tailWord_7060642, baseEnd_7060642] using wordTrace_append hprefix tailTrace_7060642
  have hstable : (prefixWord ++ tailWord_7060642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7060642).length < 2 ^ (prefixWord ++ tailWord_7060642).sum := by decide
  have hdescent : baseEnd_7060642 < baseStart_7060642 := by decide
  rcases family_descends (prefixWord ++ tailWord_7060642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7060658 : List Nat := [3, 2, 1, 1, 1, 5, 1, 1, 2, 4, 2]
def baseStart_7060658 : Nat := 118140960795 + 7060658 * 2 ^ 59
def prefixEnd_7060658 : Nat := 4983230072969 + 3 ^ 40 * 7060658 * 2
def baseEnd_7060658 : Nat := 3625511291013141376803631

theorem tailTrace_7060658 : CollatzResearch.WordTrace tailWord_7060658 prefixEnd_7060658 3625511291013141376803631 := by
  unfold tailWord_7060658
  simp only [CollatzResearch.WordTrace]
  refine ⟨64380838413612351306935657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171682235769632936818495085 64380838413612351306935657)
  ·
    refine ⟨48285628810209263480201743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64380838413612351306935657 48285628810209263480201743)
    ·
      refine ⟨72428443215313895220302615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48285628810209263480201743 72428443215313895220302615)
      ·
        refine ⟨108642664822970842830453923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72428443215313895220302615 108642664822970842830453923)
        ·
          refine ⟨162963997234456264245680885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108642664822970842830453923 162963997234456264245680885)
          ·
            refine ⟨15277874740730274773032583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 162963997234456264245680885 15277874740730274773032583)
            ·
              refine ⟨22916812111095412159548875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15277874740730274773032583 22916812111095412159548875)
              ·
                refine ⟨34375218166643118239323313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22916812111095412159548875 34375218166643118239323313)
                ·
                  refine ⟨25781413624982338679492485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34375218166643118239323313 25781413624982338679492485)
                  ·
                    refine ⟨4834015054684188502404841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25781413624982338679492485 4834015054684188502404841)
                    ·
                      refine ⟨3625511291013141376803631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4834015054684188502404841 3625511291013141376803631)
                      ·
                        rfl

theorem cell23_7060658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 1, 2, 4, 2].length) (baseStart_7060658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7060658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7060658 prefixEnd_7060658 := by exact prefixLift 7060658
  have htrace : WordTrace (prefixWord ++ tailWord_7060658) baseStart_7060658 baseEnd_7060658 := by
    simpa [prefixWord, tailWord_7060658, baseEnd_7060658] using wordTrace_append hprefix tailTrace_7060658
  have hstable : (prefixWord ++ tailWord_7060658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7060658).length < 2 ^ (prefixWord ++ tailWord_7060658).sum := by decide
  have hdescent : baseEnd_7060658 < baseStart_7060658 := by decide
  rcases family_descends (prefixWord ++ tailWord_7060658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7060668 : List Nat := [2, 2, 2, 3, 2, 2, 1, 2, 3, 4]
def baseStart_7060668 : Nat := 118140960795 + 7060668 * 2 ^ 59
def prefixEnd_7060668 : Nat := 4983230072969 + 3 ^ 40 * 7060668 * 2
def baseEnd_7060668 : Nat := 1208505475273228779226195

theorem tailTrace_7060668 : CollatzResearch.WordTrace tailWord_7060668 prefixEnd_7060668 1208505475273228779226195 := by
  unfold tailWord_7060668
  simp only [CollatzResearch.WordTrace]
  refine ⟨128761859192206588467803329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171682478922942117957071105 128761859192206588467803329)
  ·
    refine ⟨96571394394154941350852497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128761859192206588467803329 96571394394154941350852497)
    ·
      refine ⟨72428545795616206013139373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96571394394154941350852497 72428545795616206013139373)
      ·
        refine ⟨27160704673356077254927265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72428545795616206013139373 27160704673356077254927265)
        ·
          refine ⟨20370528505017057941195449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27160704673356077254927265 20370528505017057941195449)
          ·
            refine ⟨15277896378762793455896587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20370528505017057941195449 15277896378762793455896587)
            ·
              refine ⟨22916844568144190183844881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15277896378762793455896587 22916844568144190183844881)
              ·
                refine ⟨17187633426108142637883661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22916844568144190183844881 17187633426108142637883661)
                ·
                  refine ⟨6445362534790553489206373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17187633426108142637883661 6445362534790553489206373)
                  ·
                    refine ⟨1208505475273228779226195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6445362534790553489206373 1208505475273228779226195)
                    ·
                      rfl

theorem cell23_7060668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 2, 3, 4].length) (baseStart_7060668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7060668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7060668 prefixEnd_7060668 := by exact prefixLift 7060668
  have htrace : WordTrace (prefixWord ++ tailWord_7060668) baseStart_7060668 baseEnd_7060668 := by
    simpa [prefixWord, tailWord_7060668, baseEnd_7060668] using wordTrace_append hprefix tailTrace_7060668
  have hstable : (prefixWord ++ tailWord_7060668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7060668).length < 2 ^ (prefixWord ++ tailWord_7060668).sum := by decide
  have hdescent : baseEnd_7060668 < baseStart_7060668 := by decide
  rcases family_descends (prefixWord ++ tailWord_7060668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7060708 : List Nat := [2, 3, 1, 1, 1, 2, 3, 3, 3, 1, 3]
def baseStart_7060708 : Nat := 118140960795 + 7060708 * 2 ^ 59
def prefixEnd_7060708 : Nat := 4983230072969 + 3 ^ 40 * 7060708 * 2
def baseEnd_7060708 : Nat := 3625536965045866181178401

theorem tailTrace_7060708 : CollatzResearch.WordTrace tailWord_7060708 prefixEnd_7060708 3625536965045866181178401 := by
  unfold tailWord_7060708
  simp only [CollatzResearch.WordTrace]
  refine ⟨128762588652134131883531389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171683451536178842511375185 128762588652134131883531389)
  ·
    refine ⟨48285970744550299456324271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128762588652134131883531389 48285970744550299456324271)
    ·
      refine ⟨72428956116825449184486407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48285970744550299456324271 72428956116825449184486407)
      ·
        refine ⟨108643434175238173776729611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72428956116825449184486407 108643434175238173776729611)
        ·
          refine ⟨162965151262857260665094417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108643434175238173776729611 162965151262857260665094417)
          ·
            refine ⟨122223863447142945498820813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162965151262857260665094417 122223863447142945498820813)
            ·
              refine ⟨45833948792678604562057805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 122223863447142945498820813 45833948792678604562057805)
              ·
                refine ⟨17187730797254476710771677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45833948792678604562057805 17187730797254476710771677)
                ·
                  refine ⟨6445399048970428766539379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17187730797254476710771677 6445399048970428766539379)
                  ·
                    refine ⟨9668098573455643149809069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6445399048970428766539379 9668098573455643149809069)
                    ·
                      refine ⟨3625536965045866181178401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9668098573455643149809069 3625536965045866181178401)
                      ·
                        rfl

theorem cell23_7060708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 3, 3, 1, 3].length) (baseStart_7060708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7060708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7060708 prefixEnd_7060708 := by exact prefixLift 7060708
  have htrace : WordTrace (prefixWord ++ tailWord_7060708) baseStart_7060708 baseEnd_7060708 := by
    simpa [prefixWord, tailWord_7060708, baseEnd_7060708] using wordTrace_append hprefix tailTrace_7060708
  have hstable : (prefixWord ++ tailWord_7060708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7060708).length < 2 ^ (prefixWord ++ tailWord_7060708).sum := by decide
  have hdescent : baseEnd_7060708 < baseStart_7060708 := by decide
  rcases family_descends (prefixWord ++ tailWord_7060708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7060718 : List Nat := [4, 1, 2, 1, 1, 1, 3, 2, 1, 5, 2]
def baseStart_7060718 : Nat := 118140960795 + 7060718 * 2 ^ 59
def prefixEnd_7060718 : Nat := 4983230072969 + 3 ^ 40 * 7060718 * 2
def baseEnd_7060718 : Nat := 3625542099852411142053355

theorem tailTrace_7060718 : CollatzResearch.WordTrace tailWord_7060718 prefixEnd_7060718 3625542099852411142053355 := by
  unfold tailWord_7060718
  simp only [CollatzResearch.WordTrace]
  refine ⟨32190692754279004434365851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 171683694689488023649951205 32190692754279004434365851)
  ·
    refine ⟨48286039131418506651548777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32190692754279004434365851 48286039131418506651548777)
    ·
      refine ⟨36214529348563879988661583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48286039131418506651548777 36214529348563879988661583)
      ·
        refine ⟨54321794022845819982992375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36214529348563879988661583 54321794022845819982992375)
        ·
          refine ⟨81482691034268729974488563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54321794022845819982992375 81482691034268729974488563)
          ·
            refine ⟨122224036551403094961732845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81482691034268729974488563 122224036551403094961732845)
            ·
              refine ⟨45834013706776160610649817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 122224036551403094961732845 45834013706776160610649817)
              ·
                refine ⟨34375510280082120457987363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45834013706776160610649817 34375510280082120457987363)
                ·
                  refine ⟨51563265420123180686981045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34375510280082120457987363 51563265420123180686981045)
                  ·
                    refine ⟨4834056133136548189404473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51563265420123180686981045 4834056133136548189404473)
                    ·
                      refine ⟨3625542099852411142053355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4834056133136548189404473 3625542099852411142053355)
                      ·
                        rfl

theorem cell23_7060718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 2, 1, 5, 2].length) (baseStart_7060718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7060718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7060718 prefixEnd_7060718 := by exact prefixLift 7060718
  have htrace : WordTrace (prefixWord ++ tailWord_7060718) baseStart_7060718 baseEnd_7060718 := by
    simpa [prefixWord, tailWord_7060718, baseEnd_7060718] using wordTrace_append hprefix tailTrace_7060718
  have hstable : (prefixWord ++ tailWord_7060718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7060718).length < 2 ^ (prefixWord ++ tailWord_7060718).sum := by decide
  have hdescent : baseEnd_7060718 < baseStart_7060718 := by decide
  rcases family_descends (prefixWord ++ tailWord_7060718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7060741 : List Nat := [1, 3, 1, 1, 2, 1, 3, 1, 6, 4]
def baseStart_7060741 : Nat := 118140960795 + 7060741 * 2 ^ 59
def prefixEnd_7060741 : Nat := 4983230072969 + 3 ^ 40 * 7060741 * 2
def baseEnd_7060741 : Nat := 1208517969969154850688583

theorem tailTrace_7060741 : CollatzResearch.WordTrace tailWord_7060741 prefixEnd_7060741 1208517969969154850688583 := by
  unfold tailWord_7060741
  simp only [CollatzResearch.WordTrace]
  refine ⟨257526380913148710403014077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171684253942099140268676051 257526380913148710403014077)
  ·
    refine ⟨96572392842430766401130279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 257526380913148710403014077 96572392842430766401130279)
    ·
      refine ⟨144858589263646149601695419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96572392842430766401130279 144858589263646149601695419)
      ·
        refine ⟨217287883895469224402543129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144858589263646149601695419 217287883895469224402543129)
        ·
          refine ⟨162965912921601918301907347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 217287883895469224402543129 162965912921601918301907347)
          ·
            refine ⟨244448869382402877452861021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162965912921601918301907347 244448869382402877452861021)
            ·
              refine ⟨91668326018401079044822883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 244448869382402877452861021 91668326018401079044822883)
              ·
                refine ⟨137502489027601618567234325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91668326018401079044822883 137502489027601618567234325)
                ·
                  refine ⟨6445429173168825870339109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 137502489027601618567234325 6445429173168825870339109)
                  ·
                    refine ⟨1208517969969154850688583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6445429173168825870339109 1208517969969154850688583)
                    ·
                      rfl

theorem cell23_7060741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 1, 6, 4].length) (baseStart_7060741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7060741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7060741 prefixEnd_7060741 := by exact prefixLift 7060741
  have htrace : WordTrace (prefixWord ++ tailWord_7060741) baseStart_7060741 baseEnd_7060741 := by
    simpa [prefixWord, tailWord_7060741, baseEnd_7060741] using wordTrace_append hprefix tailTrace_7060741
  have hstable : (prefixWord ++ tailWord_7060741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7060741).length < 2 ^ (prefixWord ++ tailWord_7060741).sum := by decide
  have hdescent : baseEnd_7060741 < baseStart_7060741 := by decide
  rcases family_descends (prefixWord ++ tailWord_7060741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7060748 : List Nat := [2, 2, 1, 2, 2, 3, 2, 3, 1, 1, 4]
def baseStart_7060748 : Nat := 118140960795 + 7060748 * 2 ^ 59
def prefixEnd_7060748 : Nat := 4983230072969 + 3 ^ 40 * 7060748 * 2
def baseEnd_7060748 : Nat := 3625557504272046024678217

theorem tailTrace_7060748 : CollatzResearch.WordTrace tailWord_7060748 prefixEnd_7060748 3625557504272046024678217 := by
  unfold tailWord_7060748
  simp only [CollatzResearch.WordTrace]
  refine ⟨128763318112061675299259449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171684424149415567065679265 128763318112061675299259449)
  ·
    refine ⟨96572488584046256474444587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128763318112061675299259449 96572488584046256474444587)
    ·
      refine ⟨144858732876069384711666881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96572488584046256474444587 144858732876069384711666881)
      ·
        refine ⟨108644049657052038533750161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144858732876069384711666881 108644049657052038533750161)
        ·
          refine ⟨81483037242789028900312621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108644049657052038533750161 81483037242789028900312621)
          ·
            refine ⟨30556138966045885837617233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81483037242789028900312621 30556138966045885837617233)
            ·
              refine ⟨22917104224534414378212925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30556138966045885837617233 22917104224534414378212925)
              ·
                refine ⟨8593914084200405391829847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22917104224534414378212925 8593914084200405391829847)
                ·
                  refine ⟨12890871126300608087744771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8593914084200405391829847 12890871126300608087744771)
                  ·
                    refine ⟨19336306689450912131617157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12890871126300608087744771 19336306689450912131617157)
                    ·
                      refine ⟨3625557504272046024678217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19336306689450912131617157 3625557504272046024678217)
                      ·
                        rfl

theorem cell23_7060748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 3, 1, 1, 4].length) (baseStart_7060748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7060748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7060748 prefixEnd_7060748 := by exact prefixLift 7060748
  have htrace : WordTrace (prefixWord ++ tailWord_7060748) baseStart_7060748 baseEnd_7060748 := by
    simpa [prefixWord, tailWord_7060748, baseEnd_7060748] using wordTrace_append hprefix tailTrace_7060748
  have hstable : (prefixWord ++ tailWord_7060748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7060748).length < 2 ^ (prefixWord ++ tailWord_7060748).sum := by decide
  have hdescent : baseEnd_7060748 < baseStart_7060748 := by decide
  rcases family_descends (prefixWord ++ tailWord_7060748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7060751 : List Nat := [1, 1, 2, 1, 1, 1, 3, 1, 7, 2, 3]
def baseStart_7060751 : Nat := 118140960795 + 7060751 * 2 ^ 59
def prefixEnd_7060751 : Nat := 4983230072969 + 3 ^ 40 * 7060751 * 2
def baseEnd_7060751 : Nat := 3625559044714009512940703

theorem tailTrace_7060751 : CollatzResearch.WordTrace tailWord_7060751 prefixEnd_7060751 3625559044714009512940703 := by
  unfold tailWord_7060751
  simp only [CollatzResearch.WordTrace]
  refine ⟨257526745643112482110878107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171684497095408321407252071 257526745643112482110878107)
  ·
    refine ⟨386290118464668723166317161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257526745643112482110878107 386290118464668723166317161)
    ·
      refine ⟨289717588848501542374737871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 386290118464668723166317161 289717588848501542374737871)
      ·
        refine ⟨434576383272752313562106807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 289717588848501542374737871 434576383272752313562106807)
        ·
          refine ⟨651864574909128470343160211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 434576383272752313562106807 651864574909128470343160211)
          ·
            refine ⟨977796862363692705514740317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 651864574909128470343160211 977796862363692705514740317)
            ·
              refine ⟨366673823386384764568027619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 977796862363692705514740317 366673823386384764568027619)
              ·
                refine ⟨550010735079577146852041429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 366673823386384764568027619 550010735079577146852041429)
                ·
                  refine ⟨12890876603427589379344721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 550010735079577146852041429 12890876603427589379344721)
                  ·
                    refine ⟨9668157452570692034508541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12890876603427589379344721 9668157452570692034508541)
                    ·
                      refine ⟨3625559044714009512940703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9668157452570692034508541 3625559044714009512940703)
                      ·
                        rfl

theorem cell23_7060751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 7, 2, 3].length) (baseStart_7060751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7060751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7060751 prefixEnd_7060751 := by exact prefixLift 7060751
  have htrace : WordTrace (prefixWord ++ tailWord_7060751) baseStart_7060751 baseEnd_7060751 := by
    simpa [prefixWord, tailWord_7060751, baseEnd_7060751] using wordTrace_append hprefix tailTrace_7060751
  have hstable : (prefixWord ++ tailWord_7060751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7060751).length < 2 ^ (prefixWord ++ tailWord_7060751).sum := by decide
  have hdescent : baseEnd_7060751 < baseStart_7060751 := by decide
  rcases family_descends (prefixWord ++ tailWord_7060751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7060771 : List Nat := [1, 1, 1, 4, 2, 4, 2, 8]
def baseStart_7060771 : Nat := 118140960795 + 7060771 * 2 ^ 59
def prefixEnd_7060771 : Nat := 4983230072969 + 3 ^ 40 * 7060771 * 2
def baseEnd_7060771 : Nat := 134280344975077756840393

theorem tailTrace_7060771 : CollatzResearch.WordTrace tailWord_7060771 prefixEnd_7060771 134280344975077756840393 := by
  unfold tailWord_7060771
  simp only [CollatzResearch.WordTrace]
  refine ⟨257527475103040025526606167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171684983402026683684404111 257527475103040025526606167)
  ·
    refine ⟨386291212654560038289909251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257527475103040025526606167 386291212654560038289909251)
    ·
      refine ⟨579436818981840057434863877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 386291212654560038289909251 579436818981840057434863877)
      ·
        refine ⟨108644403559095010769036977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 579436818981840057434863877 108644403559095010769036977)
        ·
          refine ⟨81483302669321258076777733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108644403559095010769036977 81483302669321258076777733)
          ·
            refine ⟨15278119250497735889395825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 81483302669321258076777733 15278119250497735889395825)
            ·
              refine ⟨11458589437873301917046869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15278119250497735889395825 11458589437873301917046869)
              ·
                refine ⟨134280344975077756840393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11458589437873301917046869 134280344975077756840393)
                ·
                  rfl

theorem cell23_7060771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 2, 8].length) (baseStart_7060771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7060771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7060771 prefixEnd_7060771 := by exact prefixLift 7060771
  have htrace : WordTrace (prefixWord ++ tailWord_7060771) baseStart_7060771 baseEnd_7060771 := by
    simpa [prefixWord, tailWord_7060771, baseEnd_7060771] using wordTrace_append hprefix tailTrace_7060771
  have hstable : (prefixWord ++ tailWord_7060771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7060771).length < 2 ^ (prefixWord ++ tailWord_7060771).sum := by decide
  have hdescent : baseEnd_7060771 < baseStart_7060771 := by decide
  rcases family_descends (prefixWord ++ tailWord_7060771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7060778 : List Nat := [3, 1, 4, 2, 1, 1, 2, 1, 1, 1, 6]
def baseStart_7060778 : Nat := 118140960795 + 7060778 * 2 ^ 59
def prefixEnd_7060778 : Nat := 4983230072969 + 3 ^ 40 * 7060778 * 2
def baseEnd_7060778 : Nat := 3625572908691680907303079

theorem tailTrace_7060778 : CollatzResearch.WordTrace tailWord_7060778 prefixEnd_7060778 3625572908691680907303079 := by
  unfold tailWord_7060778
  simp only [CollatzResearch.WordTrace]
  refine ⟨64381932603503666430527747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171685153609343110481407325 64381932603503666430527747)
  ·
    refine ⟨96572898905255499645791621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64381932603503666430527747 96572898905255499645791621)
    ·
      refine ⟨18107418544735406183585929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 96572898905255499645791621 18107418544735406183585929)
      ·
        refine ⟨13580563908551554637689447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18107418544735406183585929 13580563908551554637689447)
        ·
          refine ⟨20370845862827331956534171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13580563908551554637689447 20370845862827331956534171)
          ·
            refine ⟨30556268794240997934801257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20370845862827331956534171 30556268794240997934801257)
            ·
              refine ⟨22917201595680748451100943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30556268794240997934801257 22917201595680748451100943)
              ·
                refine ⟨34375802393521122676651415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22917201595680748451100943 34375802393521122676651415)
                ·
                  refine ⟨51563703590281684014977123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34375802393521122676651415 51563703590281684014977123)
                  ·
                    refine ⟨77345555385422526022465685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51563703590281684014977123 77345555385422526022465685)
                    ·
                      refine ⟨3625572908691680907303079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 77345555385422526022465685 3625572908691680907303079)
                      ·
                        rfl

theorem cell23_7060778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_7060778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7060778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7060778 prefixEnd_7060778 := by exact prefixLift 7060778
  have htrace : WordTrace (prefixWord ++ tailWord_7060778) baseStart_7060778 baseEnd_7060778 := by
    simpa [prefixWord, tailWord_7060778, baseEnd_7060778] using wordTrace_append hprefix tailTrace_7060778
  have hstable : (prefixWord ++ tailWord_7060778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7060778).length < 2 ^ (prefixWord ++ tailWord_7060778).sum := by decide
  have hdescent : baseEnd_7060778 < baseStart_7060778 := by decide
  rcases family_descends (prefixWord ++ tailWord_7060778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7060785 : List Nat := [1, 2, 2, 3, 3, 1, 3, 2, 1, 2, 3]
def baseStart_7060785 : Nat := 118140960795 + 7060785 * 2 ^ 59
def prefixEnd_7060785 : Nat := 4983230072969 + 3 ^ 40 * 7060785 * 2
def baseEnd_7060785 : Nat := 3625576503056262379915547

theorem tailTrace_7060785 : CollatzResearch.WordTrace tailWord_7060785 prefixEnd_7060785 3625576503056262379915547 := by
  unfold tailWord_7060785
  simp only [CollatzResearch.WordTrace]
  refine ⟨257527985724989305917615809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171685323816659537278410539 257527985724989305917615809)
  ·
    refine ⟨193145989293741979438211857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257527985724989305917615809 193145989293741979438211857)
    ·
      refine ⟨144859491970306484578658893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193145989293741979438211857 144859491970306484578658893)
      ·
        refine ⟨54322309488864931716997085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144859491970306484578658893 54322309488864931716997085)
        ·
          refine ⟨20370866058324349393873907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54322309488864931716997085 20370866058324349393873907)
          ·
            refine ⟨30556299087486524090810861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20370866058324349393873907 30556299087486524090810861)
            ·
              refine ⟨11458612157807446534054073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30556299087486524090810861 11458612157807446534054073)
              ·
                refine ⟨8593959118355584900540555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11458612157807446534054073 8593959118355584900540555)
                ·
                  refine ⟨12890938677533377350810833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8593959118355584900540555 12890938677533377350810833)
                  ·
                    refine ⟨9668204008150033013108125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12890938677533377350810833 9668204008150033013108125)
                    ·
                      refine ⟨3625576503056262379915547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9668204008150033013108125 3625576503056262379915547)
                      ·
                        rfl

theorem cell23_7060785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 3, 2, 1, 2, 3].length) (baseStart_7060785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7060785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7060785 prefixEnd_7060785 := by exact prefixLift 7060785
  have htrace : WordTrace (prefixWord ++ tailWord_7060785) baseStart_7060785 baseEnd_7060785 := by
    simpa [prefixWord, tailWord_7060785, baseEnd_7060785] using wordTrace_append hprefix tailTrace_7060785
  have hstable : (prefixWord ++ tailWord_7060785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7060785).length < 2 ^ (prefixWord ++ tailWord_7060785).sum := by decide
  have hdescent : baseEnd_7060785 < baseStart_7060785 := by decide
  rcases family_descends (prefixWord ++ tailWord_7060785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7060829 : List Nat := [1, 4, 5, 1, 1, 1, 2, 1, 1, 2, 4]
def baseStart_7060829 : Nat := 118140960795 + 7060829 * 2 ^ 59
def prefixEnd_7060829 : Nat := 4983230072969 + 3 ^ 40 * 7060829 * 2
def baseEnd_7060829 : Nat := 3625599096205060207765345

theorem tailTrace_7060829 : CollatzResearch.WordTrace tailWord_7060829 prefixEnd_7060829 3625599096205060207765345 := by
  unfold tailWord_7060829
  simp only [CollatzResearch.WordTrace]
  refine ⟨257529590536829901432217541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171686393691219934288145027 257529590536829901432217541)
  ·
    refine ⟨48286798225655606518540789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 257529590536829901432217541 48286798225655606518540789)
    ·
      refine ⟨4526887333655213111113199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 48286798225655606518540789 4526887333655213111113199)
      ·
        refine ⟨6790331000482819666669799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4526887333655213111113199 6790331000482819666669799)
        ·
          refine ⟨10185496500724229500004699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6790331000482819666669799 10185496500724229500004699)
          ·
            refine ⟨15278244751086344250007049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10185496500724229500004699 15278244751086344250007049)
            ·
              refine ⟨11458683563314758187505287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15278244751086344250007049 11458683563314758187505287)
              ·
                refine ⟨17188025344972137281257931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11458683563314758187505287 17188025344972137281257931)
                ·
                  refine ⟨25782038017458205921886897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17188025344972137281257931 25782038017458205921886897)
                  ·
                    refine ⟨19336528513093654441415173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25782038017458205921886897 19336528513093654441415173)
                    ·
                      refine ⟨3625599096205060207765345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19336528513093654441415173 3625599096205060207765345)
                      ·
                        rfl

theorem cell23_7060829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_7060829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7060829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7060829 prefixEnd_7060829 := by exact prefixLift 7060829
  have htrace : WordTrace (prefixWord ++ tailWord_7060829) baseStart_7060829 baseEnd_7060829 := by
    simpa [prefixWord, tailWord_7060829, baseEnd_7060829] using wordTrace_append hprefix tailTrace_7060829
  have hstable : (prefixWord ++ tailWord_7060829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7060829).length < 2 ^ (prefixWord ++ tailWord_7060829).sum := by decide
  have hdescent : baseEnd_7060829 < baseStart_7060829 := by decide
  rcases family_descends (prefixWord ++ tailWord_7060829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7060841 : List Nat := [1, 2, 1, 1, 1, 3, 2, 4, 2, 1, 5]
def baseStart_7060841 : Nat := 118140960795 + 7060841 * 2 ^ 59
def prefixEnd_7060841 : Nat := 4983230072969 + 3 ^ 40 * 7060841 * 2
def baseEnd_7060841 : Nat := 3625605257972914160815289

theorem tailTrace_7060841 : CollatzResearch.WordTrace tailWord_7060841 prefixEnd_7060841 3625605257972914160815289 := by
  unfold tailWord_7060841
  simp only [CollatzResearch.WordTrace]
  refine ⟨257530028212786427481654377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171686685475190951654436251 257530028212786427481654377)
  ·
    refine ⟨193147521159589820611240783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257530028212786427481654377 193147521159589820611240783)
    ·
      refine ⟨289721281739384730916861175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193147521159589820611240783 289721281739384730916861175)
      ·
        refine ⟨434581922609077096375291763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 289721281739384730916861175 434581922609077096375291763)
        ·
          refine ⟨651872883913615644562937645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 434581922609077096375291763 651872883913615644562937645)
          ·
            refine ⟨244452331467605866711101617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 651872883913615644562937645 244452331467605866711101617)
            ·
              refine ⟨183339248600704400033326213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 244452331467605866711101617 183339248600704400033326213)
              ·
                refine ⟨34376109112632075006248665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 183339248600704400033326213 34376109112632075006248665)
                ·
                  refine ⟨25782081834474056254686499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34376109112632075006248665 25782081834474056254686499)
                  ·
                    refine ⟨38673122751711084382029749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25782081834474056254686499 38673122751711084382029749)
                    ·
                      refine ⟨3625605257972914160815289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38673122751711084382029749 3625605257972914160815289)
                      ·
                        rfl

theorem cell23_7060841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 4, 2, 1, 5].length) (baseStart_7060841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7060841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7060841 prefixEnd_7060841 := by exact prefixLift 7060841
  have htrace : WordTrace (prefixWord ++ tailWord_7060841) baseStart_7060841 baseEnd_7060841 := by
    simpa [prefixWord, tailWord_7060841, baseEnd_7060841] using wordTrace_append hprefix tailTrace_7060841
  have hstable : (prefixWord ++ tailWord_7060841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7060841).length < 2 ^ (prefixWord ++ tailWord_7060841).sum := by decide
  have hdescent : baseEnd_7060841 < baseStart_7060841 := by decide
  rcases family_descends (prefixWord ++ tailWord_7060841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7060851 : List Nat := [1, 1, 1, 2, 2, 1, 2, 1, 6, 2, 4]
def baseStart_7060851 : Nat := 118140960795 + 7060851 * 2 ^ 59
def prefixEnd_7060851 : Nat := 4983230072969 + 3 ^ 40 * 7060851 * 2
def baseEnd_7060851 : Nat := 3625610392779459121690243

theorem tailTrace_7060851 : CollatzResearch.WordTrace tailWord_7060851 prefixEnd_7060851 3625610392779459121690243 := by
  unfold tailWord_7060851
  simp only [CollatzResearch.WordTrace]
  refine ⟨257530392942750199189518407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171686928628500132793012271 257530392942750199189518407)
  ·
    refine ⟨386295589414125298784277611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257530392942750199189518407 386295589414125298784277611)
    ·
      refine ⟨579443384121187948176416417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 386295589414125298784277611 579443384121187948176416417)
      ·
        refine ⟨434582538090890961132312313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 579443384121187948176416417 434582538090890961132312313)
        ·
          refine ⟨325936903568168220849234235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 434582538090890961132312313 325936903568168220849234235)
          ·
            refine ⟨488905355352252331273851353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 325936903568168220849234235 488905355352252331273851353)
            ·
              refine ⟨366679016514189248455388515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 488905355352252331273851353 366679016514189248455388515)
              ·
                refine ⟨550018524771283872683082773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 366679016514189248455388515 550018524771283872683082773)
                ·
                  refine ⟨25782118348653931532019505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 550018524771283872683082773 25782118348653931532019505)
                  ·
                    refine ⟨19336588761490448649014629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25782118348653931532019505 19336588761490448649014629)
                    ·
                      refine ⟨3625610392779459121690243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19336588761490448649014629 3625610392779459121690243)
                      ·
                        rfl

theorem cell23_7060851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 6, 2, 4].length) (baseStart_7060851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7060851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7060851 prefixEnd_7060851 := by exact prefixLift 7060851
  have htrace : WordTrace (prefixWord ++ tailWord_7060851) baseStart_7060851 baseEnd_7060851 := by
    simpa [prefixWord, tailWord_7060851, baseEnd_7060851] using wordTrace_append hprefix tailTrace_7060851
  have hstable : (prefixWord ++ tailWord_7060851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7060851).length < 2 ^ (prefixWord ++ tailWord_7060851).sum := by decide
  have hdescent : baseEnd_7060851 < baseStart_7060851 := by decide
  rcases family_descends (prefixWord ++ tailWord_7060851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7060855 : List Nat := [1, 1, 3, 1, 1, 2, 4, 2, 4, 2, 2]
def baseStart_7060855 : Nat := 118140960795 + 7060855 * 2 ^ 59
def prefixEnd_7060855 : Nat := 4983230072969 + 3 ^ 40 * 7060855 * 2
def baseEnd_7060855 : Nat := 3625612446702077106040225

theorem tailTrace_7060855 : CollatzResearch.WordTrace tailWord_7060855 prefixEnd_7060855 3625612446702077106040225 := by
  unfold tailWord_7060855
  simp only [CollatzResearch.WordTrace]
  refine ⟨257530538834735707872664019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171687025889823805248442679 257530538834735707872664019)
  ·
    refine ⟨386295808252103561808996029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257530538834735707872664019 386295808252103561808996029)
    ·
      refine ⟨144860928094538835678373511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 386295808252103561808996029 144860928094538835678373511)
      ·
        refine ⟨217291392141808253517560267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144860928094538835678373511 217291392141808253517560267)
        ·
          refine ⟨325937088212712380276340401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217291392141808253517560267 325937088212712380276340401)
          ·
            refine ⟨244452816159534285207255301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 325937088212712380276340401 244452816159534285207255301)
            ·
              refine ⟨45834903029912678476360369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 244452816159534285207255301 45834903029912678476360369)
              ·
                refine ⟨34376177272434508857270277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45834903029912678476360369 34376177272434508857270277)
                ·
                  refine ⟨6445533238581470410738177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34376177272434508857270277 6445533238581470410738177)
                  ·
                    refine ⟨4834149928936102808053633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6445533238581470410738177 4834149928936102808053633)
                    ·
                      refine ⟨3625612446702077106040225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4834149928936102808053633 3625612446702077106040225)
                      ·
                        rfl

theorem cell23_7060855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 2, 4, 2, 2].length) (baseStart_7060855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7060855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7060855 prefixEnd_7060855 := by exact prefixLift 7060855
  have htrace : WordTrace (prefixWord ++ tailWord_7060855) baseStart_7060855 baseEnd_7060855 := by
    simpa [prefixWord, tailWord_7060855, baseEnd_7060855] using wordTrace_append hprefix tailTrace_7060855
  have hstable : (prefixWord ++ tailWord_7060855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7060855).length < 2 ^ (prefixWord ++ tailWord_7060855).sum := by decide
  have hdescent : baseEnd_7060855 < baseStart_7060855 := by decide
  rcases family_descends (prefixWord ++ tailWord_7060855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7060861 : List Nat := [1, 4, 1, 1, 2, 2, 1, 2, 9]
def baseStart_7060861 : Nat := 118140960795 + 7060861 * 2 ^ 59
def prefixEnd_7060861 : Nat := 4983230072969 + 3 ^ 40 * 7060861 * 2
def baseEnd_7060861 : Nat := 402846169731778231396133

theorem tailTrace_7060861 : CollatzResearch.WordTrace tailWord_7060861 prefixEnd_7060861 402846169731778231396133 := by
  unfold tailWord_7060861
  simp only [CollatzResearch.WordTrace]
  refine ⟨257530757672713970897382437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171687171781809313931588291 257530757672713970897382437)
  ·
    refine ⟨48287017063633869543259207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 257530757672713970897382437 48287017063633869543259207)
    ·
      refine ⟨72430525595450804314888811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48287017063633869543259207 72430525595450804314888811)
      ·
        refine ⟨108645788393176206472333217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72430525595450804314888811 108645788393176206472333217)
        ·
          refine ⟨81484341294882154854249913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108645788393176206472333217 81484341294882154854249913)
          ·
            refine ⟨61113255971161616140687435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81484341294882154854249913 61113255971161616140687435)
            ·
              refine ⟨91669883956742424211031153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61113255971161616140687435 91669883956742424211031153)
              ·
                refine ⟨68752412967556818158273365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91669883956742424211031153 68752412967556818158273365)
                ·
                  refine ⟨402846169731778231396133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 68752412967556818158273365 402846169731778231396133)
                  ·
                    rfl

theorem cell23_7060861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 2, 9].length) (baseStart_7060861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7060861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7060861 prefixEnd_7060861 := by exact prefixLift 7060861
  have htrace : WordTrace (prefixWord ++ tailWord_7060861) baseStart_7060861 baseEnd_7060861 := by
    simpa [prefixWord, tailWord_7060861, baseEnd_7060861] using wordTrace_append hprefix tailTrace_7060861
  have hstable : (prefixWord ++ tailWord_7060861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7060861).length < 2 ^ (prefixWord ++ tailWord_7060861).sum := by decide
  have hdescent : baseEnd_7060861 < baseStart_7060861 := by decide
  rcases family_descends (prefixWord ++ tailWord_7060861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7060866 : List Nat := [3, 4, 2, 1, 1, 3, 1, 2, 2, 1, 3]
def baseStart_7060866 : Nat := 118140960795 + 7060866 * 2 ^ 59
def prefixEnd_7060866 : Nat := 4983230072969 + 3 ^ 40 * 7060866 * 2
def baseEnd_7060866 : Nat := 3625618094989276563002675

theorem tailTrace_7060866 : CollatzResearch.WordTrace tailWord_7060866 prefixEnd_7060866 3625618094989276563002675 := by
  unfold tailWord_7060866
  simp only [CollatzResearch.WordTrace]
  refine ⟨64382735009423964187828613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171687293358463904500876301 64382735009423964187828613)
  ·
    refine ⟨12071762814266993285217865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64382735009423964187828613 12071762814266993285217865)
    ·
      refine ⟨9053822110700244963913399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12071762814266993285217865 9053822110700244963913399)
      ·
        refine ⟨13580733166050367445870099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9053822110700244963913399 13580733166050367445870099)
        ·
          refine ⟨20371099749075551168805149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13580733166050367445870099 20371099749075551168805149)
          ·
            refine ⟨7639162405903331688301931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20371099749075551168805149 7639162405903331688301931)
            ·
              refine ⟨11458743608854997532452897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7639162405903331688301931 11458743608854997532452897)
              ·
                refine ⟨8594057706641248149339673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11458743608854997532452897 8594057706641248149339673)
                ·
                  refine ⟨6445543279980936112004755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8594057706641248149339673 6445543279980936112004755)
                  ·
                    refine ⟨9668314919971404168007133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6445543279980936112004755 9668314919971404168007133)
                    ·
                      refine ⟨3625618094989276563002675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9668314919971404168007133 3625618094989276563002675)
                      ·
                        rfl

theorem cell23_7060866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 1, 2, 2, 1, 3].length) (baseStart_7060866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7060866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7060866 prefixEnd_7060866 := by exact prefixLift 7060866
  have htrace : WordTrace (prefixWord ++ tailWord_7060866) baseStart_7060866 baseEnd_7060866 := by
    simpa [prefixWord, tailWord_7060866, baseEnd_7060866] using wordTrace_append hprefix tailTrace_7060866
  have hstable : (prefixWord ++ tailWord_7060866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7060866).length < 2 ^ (prefixWord ++ tailWord_7060866).sum := by decide
  have hdescent : baseEnd_7060866 < baseStart_7060866 := by decide
  rcases family_descends (prefixWord ++ tailWord_7060866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7060868 : List Nat := [2, 3, 2, 1, 1, 3, 1, 2, 2, 2, 4]
def baseStart_7060868 : Nat := 118140960795 + 7060868 * 2 ^ 59
def prefixEnd_7060868 : Nat := 4983230072969 + 3 ^ 40 * 7060868 * 2
def baseEnd_7060868 : Nat := 3625619121950585555177665

theorem tailTrace_7060868 : CollatzResearch.WordTrace tailWord_7060868 prefixEnd_7060868 3625619121950585555177665 := by
  unfold tailWord_7060868
  simp only [CollatzResearch.WordTrace]
  refine ⟨128765506491844305546443629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171687341989125740728591505 128765506491844305546443629)
  ·
    refine ⟨48287064934441614579916361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128765506491844305546443629 48287064934441614579916361)
    ·
      refine ⟨36215298700831210934937271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48287064934441614579916361 36215298700831210934937271)
      ·
        refine ⟨54322948051246816402405907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36215298700831210934937271 54322948051246816402405907)
        ·
          refine ⟨81484422076870224603608861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54322948051246816402405907 81484422076870224603608861)
          ·
            refine ⟨30556658278826334226353323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81484422076870224603608861 30556658278826334226353323)
            ·
              refine ⟨45834987418239501339529985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30556658278826334226353323 45834987418239501339529985)
              ·
                refine ⟨34376240563679626004647489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45834987418239501339529985 34376240563679626004647489)
                ·
                  refine ⟨25782180422759719503485617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34376240563679626004647489 25782180422759719503485617)
                  ·
                    refine ⟨19336635317069789627614213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25782180422759719503485617 19336635317069789627614213)
                    ·
                      refine ⟨3625619121950585555177665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19336635317069789627614213 3625619121950585555177665)
                      ·
                        rfl

theorem cell23_7060868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 2, 2, 2, 4].length) (baseStart_7060868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7060868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7060868 prefixEnd_7060868 := by exact prefixLift 7060868
  have htrace : WordTrace (prefixWord ++ tailWord_7060868) baseStart_7060868 baseEnd_7060868 := by
    simpa [prefixWord, tailWord_7060868, baseEnd_7060868] using wordTrace_append hprefix tailTrace_7060868
  have hstable : (prefixWord ++ tailWord_7060868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7060868).length < 2 ^ (prefixWord ++ tailWord_7060868).sum := by decide
  have hdescent : baseEnd_7060868 < baseStart_7060868 := by decide
  rcases family_descends (prefixWord ++ tailWord_7060868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7060872 : List Nat := [2, 1, 3, 3, 1, 3, 1, 1, 4, 2, 2]
def baseStart_7060872 : Nat := 118140960795 + 7060872 * 2 ^ 59
def prefixEnd_7060872 : Nat := 4983230072969 + 3 ^ 40 * 7060872 * 2
def baseEnd_7060872 : Nat := 3625621175873203539527647

theorem tailTrace_7060872 : CollatzResearch.WordTrace tailWord_7060872 prefixEnd_7060872 3625621175873203539527647 := by
  unfold tailWord_7060872
  simp only [CollatzResearch.WordTrace]
  refine ⟨128765579437837059888016435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171687439250449413184021913 128765579437837059888016435)
  ·
    refine ⟨193148369156755589832024653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128765579437837059888016435 193148369156755589832024653)
    ·
      refine ⟨72430638433783346187009245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 193148369156755589832024653 72430638433783346187009245)
      ·
        refine ⟨27161489412668754820128467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72430638433783346187009245 27161489412668754820128467)
        ·
          refine ⟨40742234119003132230192701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27161489412668754820128467 40742234119003132230192701)
          ·
            refine ⟨15278337794626174586322263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40742234119003132230192701 15278337794626174586322263)
            ·
              refine ⟨22917506691939261879483395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15278337794626174586322263 22917506691939261879483395)
              ·
                refine ⟨34376260037908892819225093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22917506691939261879483395 34376260037908892819225093)
                ·
                  refine ⟨6445548757107917403604705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34376260037908892819225093 6445548757107917403604705)
                  ·
                    refine ⟨4834161567830938052703529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6445548757107917403604705 4834161567830938052703529)
                    ·
                      refine ⟨3625621175873203539527647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4834161567830938052703529 3625621175873203539527647)
                      ·
                        rfl

theorem cell23_7060872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 1, 4, 2, 2].length) (baseStart_7060872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7060872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7060872 prefixEnd_7060872 := by exact prefixLift 7060872
  have htrace : WordTrace (prefixWord ++ tailWord_7060872) baseStart_7060872 baseEnd_7060872 := by
    simpa [prefixWord, tailWord_7060872, baseEnd_7060872] using wordTrace_append hprefix tailTrace_7060872
  have hstable : (prefixWord ++ tailWord_7060872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7060872).length < 2 ^ (prefixWord ++ tailWord_7060872).sum := by decide
  have hdescent : baseEnd_7060872 < baseStart_7060872 := by decide
  rcases family_descends (prefixWord ++ tailWord_7060872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7060889 : List Nat := [1, 2, 1, 2, 1, 6, 3, 1, 2, 2, 2]
def baseStart_7060889 : Nat := 118140960795 + 7060889 * 2 ^ 59
def prefixEnd_7060889 : Nat := 4983230072969 + 3 ^ 40 * 7060889 * 2
def baseEnd_7060889 : Nat := 3625629905044329973015069

theorem tailTrace_7060889 : CollatzResearch.WordTrace tailWord_7060889 prefixEnd_7060889 3625629905044329973015069 := by
  unfold tailWord_7060889
  simp only [CollatzResearch.WordTrace]
  refine ⟨257531778916612531679401721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171687852611075021119601147 257531778916612531679401721)
  ·
    refine ⟨193148834187459398759551291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257531778916612531679401721 193148834187459398759551291)
    ·
      refine ⟨289723251281189098139326937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193148834187459398759551291 289723251281189098139326937)
      ·
        refine ⟨217292438460891823604495203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 289723251281189098139326937 217292438460891823604495203)
        ·
          refine ⟨325938657691337735406742805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217292438460891823604495203 325938657691337735406742805)
          ·
            refine ⟨15278374579281456347191069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 325938657691337735406742805 15278374579281456347191069)
            ·
              refine ⟨5729390467230546130196651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15278374579281456347191069 5729390467230546130196651)
              ·
                refine ⟨8594085700845819195294977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5729390467230546130196651 8594085700845819195294977)
                ·
                  refine ⟨6445564275634364396471233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8594085700845819195294977 6445564275634364396471233)
                  ·
                    refine ⟨4834173206725773297353425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6445564275634364396471233 4834173206725773297353425)
                    ·
                      refine ⟨3625629905044329973015069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4834173206725773297353425 3625629905044329973015069)
                      ·
                        rfl

theorem cell23_7060889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 3, 1, 2, 2, 2].length) (baseStart_7060889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7060889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7060889 prefixEnd_7060889 := by exact prefixLift 7060889
  have htrace : WordTrace (prefixWord ++ tailWord_7060889) baseStart_7060889 baseEnd_7060889 := by
    simpa [prefixWord, tailWord_7060889, baseEnd_7060889] using wordTrace_append hprefix tailTrace_7060889
  have hstable : (prefixWord ++ tailWord_7060889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7060889).length < 2 ^ (prefixWord ++ tailWord_7060889).sum := by decide
  have hdescent : baseEnd_7060889 < baseStart_7060889 := by decide
  rcases family_descends (prefixWord ++ tailWord_7060889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7060901 : List Nat := [1, 3, 1, 2, 1, 1, 2, 1, 3, 1, 7]
def baseStart_7060901 : Nat := 118140960795 + 7060901 * 2 ^ 59
def prefixEnd_7060901 : Nat := 4983230072969 + 3 ^ 40 * 7060901 * 2
def baseEnd_7060901 : Nat := 3625636066812183926065013

theorem tailTrace_7060901 : CollatzResearch.WordTrace tailWord_7060901 prefixEnd_7060901 3625636066812183926065013 := by
  unfold tailWord_7060901
  simp only [CollatzResearch.WordTrace]
  refine ⟨257532216592569057728838557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171688144395046038485892371 257532216592569057728838557)
  ·
    refine ⟨96574581222213396648314459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 257532216592569057728838557 96574581222213396648314459)
    ·
      refine ⟨144861871833320094972471689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96574581222213396648314459 144861871833320094972471689)
      ·
        refine ⟨108646403874990071229353767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144861871833320094972471689 108646403874990071229353767)
        ·
          refine ⟨162969605812485106844030651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108646403874990071229353767 162969605812485106844030651)
          ·
            refine ⟨244454408718727660266045977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162969605812485106844030651 244454408718727660266045977)
            ·
              refine ⟨183340806539045745199534483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 244454408718727660266045977 183340806539045745199534483)
              ·
                refine ⟨275011209808568617799301725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 183340806539045745199534483 275011209808568617799301725)
                ·
                  refine ⟨103129203678213231674738147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 275011209808568617799301725 103129203678213231674738147)
                  ·
                    refine ⟨154693805517319847512107221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 103129203678213231674738147 154693805517319847512107221)
                    ·
                      refine ⟨3625636066812183926065013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 154693805517319847512107221 3625636066812183926065013)
                      ·
                        rfl

theorem cell23_7060901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 1, 3, 1, 7].length) (baseStart_7060901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7060901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7060901 prefixEnd_7060901 := by exact prefixLift 7060901
  have htrace : WordTrace (prefixWord ++ tailWord_7060901) baseStart_7060901 baseEnd_7060901 := by
    simpa [prefixWord, tailWord_7060901, baseEnd_7060901] using wordTrace_append hprefix tailTrace_7060901
  have hstable : (prefixWord ++ tailWord_7060901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7060901).length < 2 ^ (prefixWord ++ tailWord_7060901).sum := by decide
  have hdescent : baseEnd_7060901 < baseStart_7060901 := by decide
  rcases family_descends (prefixWord ++ tailWord_7060901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7060928 : List Nat := [2, 1, 1, 2, 3, 1, 3, 1, 4, 1, 4]
def baseStart_7060928 : Nat := 118140960795 + 7060928 * 2 ^ 59
def prefixEnd_7060928 : Nat := 4983230072969 + 3 ^ 40 * 7060928 * 2
def baseEnd_7060928 : Nat := 3625649930789855320427389

theorem tailTrace_7060928 : CollatzResearch.WordTrace tailWord_7060928 prefixEnd_7060928 3625649930789855320427389 := by
  unfold tailWord_7060928
  simp only [CollatzResearch.WordTrace]
  refine ⟨128766600681735620670035719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171688800908980827560047625 128766600681735620670035719)
  ·
    refine ⟨193149901022603431005053579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128766600681735620670035719 193149901022603431005053579)
    ·
      refine ⟨289724851533905146507580369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193149901022603431005053579 289724851533905146507580369)
      ·
        refine ⟨217293638650428859880685277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 289724851533905146507580369 217293638650428859880685277)
        ·
          refine ⟨81485114493910822455256979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 217293638650428859880685277 81485114493910822455256979)
          ·
            refine ⟨122227671740866233682885469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81485114493910822455256979 122227671740866233682885469)
            ·
              refine ⟨45835376902824837631082051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 122227671740866233682885469 45835376902824837631082051)
              ·
                refine ⟨68753065354237256446623077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45835376902824837631082051 68753065354237256446623077)
                ·
                  refine ⟨12891199753919485583741827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 68753065354237256446623077 12891199753919485583741827)
                  ·
                    refine ⟨19336799630879228375612741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12891199753919485583741827 19336799630879228375612741)
                    ·
                      refine ⟨3625649930789855320427389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19336799630879228375612741 3625649930789855320427389)
                      ·
                        rfl

theorem cell23_7060928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 1, 4, 1, 4].length) (baseStart_7060928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7060928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7060928 prefixEnd_7060928 := by exact prefixLift 7060928
  have htrace : WordTrace (prefixWord ++ tailWord_7060928) baseStart_7060928 baseEnd_7060928 := by
    simpa [prefixWord, tailWord_7060928, baseEnd_7060928] using wordTrace_append hprefix tailTrace_7060928
  have hstable : (prefixWord ++ tailWord_7060928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7060928).length < 2 ^ (prefixWord ++ tailWord_7060928).sum := by decide
  have hdescent : baseEnd_7060928 < baseStart_7060928 := by decide
  rcases family_descends (prefixWord ++ tailWord_7060928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7060982 : List Nat := [5, 1, 1, 1, 2, 2, 2, 2, 2, 2, 3]
def baseStart_7060982 : Nat := 118140960795 + 7060982 * 2 ^ 59
def prefixEnd_7060982 : Nat := 4983230072969 + 3 ^ 40 * 7060982 * 2
def baseEnd_7060982 : Nat := 3625677658745198109152141

theorem tailTrace_7060982 : CollatzResearch.WordTrace tailWord_7060982 prefixEnd_7060982 3625677658745198109152141 := by
  unfold tailWord_7060982
  simp only [CollatzResearch.WordTrace]
  refine ⟨16095948181579725535158575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 171690113936850405708358133 16095948181579725535158575)
  ·
    refine ⟨24143922272369588302737863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16095948181579725535158575 24143922272369588302737863)
    ·
      refine ⟨36215883408554382454106795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24143922272369588302737863 36215883408554382454106795)
      ·
        refine ⟨54323825112831573681160193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36215883408554382454106795 54323825112831573681160193)
        ·
          refine ⟨40742868834623680260870145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54323825112831573681160193 40742868834623680260870145)
          ·
            refine ⟨30557151625967760195652609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40742868834623680260870145 30557151625967760195652609)
            ·
              refine ⟨22917863719475820146739457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30557151625967760195652609 22917863719475820146739457)
              ·
                refine ⟨17188397789606865110054593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22917863719475820146739457 17188397789606865110054593)
                ·
                  refine ⟨12891298342205148832540945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17188397789606865110054593 12891298342205148832540945)
                  ·
                    refine ⟨9668473756653861624405709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12891298342205148832540945 9668473756653861624405709)
                    ·
                      refine ⟨3625677658745198109152141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9668473756653861624405709 3625677658745198109152141)
                      ·
                        rfl

theorem cell23_7060982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 2, 2, 2, 3].length) (baseStart_7060982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7060982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7060982 prefixEnd_7060982 := by exact prefixLift 7060982
  have htrace : WordTrace (prefixWord ++ tailWord_7060982) baseStart_7060982 baseEnd_7060982 := by
    simpa [prefixWord, tailWord_7060982, baseEnd_7060982] using wordTrace_append hprefix tailTrace_7060982
  have hstable : (prefixWord ++ tailWord_7060982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7060982).length < 2 ^ (prefixWord ++ tailWord_7060982).sum := by decide
  have hdescent : baseEnd_7060982 < baseStart_7060982 := by decide
  rcases family_descends (prefixWord ++ tailWord_7060982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7060989 : List Nat := [1, 4, 1, 1, 1, 4, 4, 2, 1, 4]
def baseStart_7060989 : Nat := 118140960795 + 7060989 * 2 ^ 59
def prefixEnd_7060989 : Nat := 4983230072969 + 3 ^ 40 * 7060989 * 2
def baseEnd_7060989 : Nat := 1208560417703259860588203

theorem tailTrace_7060989 : CollatzResearch.WordTrace tailWord_7060989 prefixEnd_7060989 1208560417703259860588203 := by
  unfold tailWord_7060989
  simp only [CollatzResearch.WordTrace]
  refine ⟨257535426216250248758042021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171690284144166832505361347 257535426216250248758042021)
  ·
    refine ⟨48287892415546921642132879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 257535426216250248758042021 48287892415546921642132879)
    ·
      refine ⟨72431838623320382463199319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48287892415546921642132879 72431838623320382463199319)
      ·
        refine ⟨108647757934980573694798979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72431838623320382463199319 108647757934980573694798979)
        ·
          refine ⟨162971636902470860542198469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108647757934980573694798979 162971636902470860542198469)
          ·
            refine ⟨30557181919213286351662213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 162971636902470860542198469 30557181919213286351662213)
            ·
              refine ⟨5729471609852491190936665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30557181919213286351662213 5729471609852491190936665)
              ·
                refine ⟨4297103707389368393202499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5729471609852491190936665 4297103707389368393202499)
                ·
                  refine ⟨6445655561084052589803749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4297103707389368393202499 6445655561084052589803749)
                  ·
                    refine ⟨1208560417703259860588203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6445655561084052589803749 1208560417703259860588203)
                    ·
                      rfl

theorem cell23_7060989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 4, 2, 1, 4].length) (baseStart_7060989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7060989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7060989 prefixEnd_7060989 := by exact prefixLift 7060989
  have htrace : WordTrace (prefixWord ++ tailWord_7060989) baseStart_7060989 baseEnd_7060989 := by
    simpa [prefixWord, tailWord_7060989, baseEnd_7060989] using wordTrace_append hprefix tailTrace_7060989
  have hstable : (prefixWord ++ tailWord_7060989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7060989).length < 2 ^ (prefixWord ++ tailWord_7060989).sum := by decide
  have hdescent : baseEnd_7060989 < baseStart_7060989 := by decide
  rcases family_descends (prefixWord ++ tailWord_7060989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7061046 : List Nat := [5, 1, 2, 1, 3, 1, 2, 1, 3, 1, 3]
def baseStart_7061046 : Nat := 118140960795 + 7061046 * 2 ^ 59
def prefixEnd_7061046 : Nat := 4983230072969 + 3 ^ 40 * 7061046 * 2
def baseEnd_7061046 : Nat := 3625710521507085858751847

theorem tailTrace_7061046 : CollatzResearch.WordTrace tailWord_7061046 prefixEnd_7061046 3625710521507085858751847 := by
  unfold tailWord_7061046
  simp only [CollatzResearch.WordTrace]
  refine ⟨16096094073565234218304187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 171691670118029164995244661 16096094073565234218304187)
  ·
    refine ⟨24144141110347851327456281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16096094073565234218304187 24144141110347851327456281)
    ·
      refine ⟨18108105832760888495592211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24144141110347851327456281 18108105832760888495592211)
      ·
        refine ⟨27162158749141332743388317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18108105832760888495592211 27162158749141332743388317)
        ·
          refine ⟨10185809530927999778770619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27162158749141332743388317 10185809530927999778770619)
          ·
            refine ⟨15278714296391999668155929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10185809530927999778770619 15278714296391999668155929)
            ·
              refine ⟨11459035722293999751116947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15278714296391999668155929 11459035722293999751116947)
              ·
                refine ⟨17188553583440999626675421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11459035722293999751116947 17188553583440999626675421)
                ·
                  refine ⟨6445707593790374860003283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17188553583440999626675421 6445707593790374860003283)
                  ·
                    refine ⟨9668561390685562290004925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6445707593790374860003283 9668561390685562290004925)
                    ·
                      refine ⟨3625710521507085858751847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9668561390685562290004925 3625710521507085858751847)
                      ·
                        rfl

theorem cell23_7061046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 2, 1, 3, 1, 3].length) (baseStart_7061046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7061046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7061046 prefixEnd_7061046 := by exact prefixLift 7061046
  have htrace : WordTrace (prefixWord ++ tailWord_7061046) baseStart_7061046 baseEnd_7061046 := by
    simpa [prefixWord, tailWord_7061046, baseEnd_7061046] using wordTrace_append hprefix tailTrace_7061046
  have hstable : (prefixWord ++ tailWord_7061046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7061046).length < 2 ^ (prefixWord ++ tailWord_7061046).sum := by decide
  have hdescent : baseEnd_7061046 < baseStart_7061046 := by decide
  rcases family_descends (prefixWord ++ tailWord_7061046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7061055 : List Nat := [1, 1, 2, 2, 3, 4, 1, 2, 1, 1, 5]
def baseStart_7061055 : Nat := 118140960795 + 7061055 * 2 ^ 59
def prefixEnd_7061055 : Nat := 4983230072969 + 3 ^ 40 * 7061055 * 2
def baseEnd_7061055 : Nat := 3625715142832976323539305

theorem tailTrace_7061055 : CollatzResearch.WordTrace tailWord_7061055 prefixEnd_7061055 3625715142832976323539305 := by
  unfold tailWord_7061055
  simp only [CollatzResearch.WordTrace]
  refine ⟨257537833434011142029944619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171691888956007428019963079 257537833434011142029944619)
  ·
    refine ⟨386306750151016713044916929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257537833434011142029944619 386306750151016713044916929)
    ·
      refine ⟨289730062613262534783687697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 386306750151016713044916929 289730062613262534783687697)
      ·
        refine ⟨217297546959946901087765773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 289730062613262534783687697 217297546959946901087765773)
        ·
          refine ⟨81486580109980087907912165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 217297546959946901087765773 81486580109980087907912165)
          ·
            refine ⟨15278733770621266482733531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 81486580109980087907912165 15278733770621266482733531)
            ·
              refine ⟨22918100655931899724100297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15278733770621266482733531 22918100655931899724100297)
              ·
                refine ⟨17188575491948924793075223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22918100655931899724100297 17188575491948924793075223)
                ·
                  refine ⟨25782863237923387189612835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17188575491948924793075223 25782863237923387189612835)
                  ·
                    refine ⟨38674294856885080784419253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25782863237923387189612835 38674294856885080784419253)
                    ·
                      refine ⟨3625715142832976323539305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38674294856885080784419253 3625715142832976323539305)
                      ·
                        rfl

theorem cell23_7061055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 2, 1, 1, 5].length) (baseStart_7061055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7061055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7061055 prefixEnd_7061055 := by exact prefixLift 7061055
  have htrace : WordTrace (prefixWord ++ tailWord_7061055) baseStart_7061055 baseEnd_7061055 := by
    simpa [prefixWord, tailWord_7061055, baseEnd_7061055] using wordTrace_append hprefix tailTrace_7061055
  have hstable : (prefixWord ++ tailWord_7061055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7061055).length < 2 ^ (prefixWord ++ tailWord_7061055).sum := by decide
  have hdescent : baseEnd_7061055 < baseStart_7061055 := by decide
  rcases family_descends (prefixWord ++ tailWord_7061055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7061072 : List Nat := [2, 1, 1, 1, 1, 3, 6, 2, 1, 2, 3]
def baseStart_7061072 : Nat := 118140960795 + 7061072 * 2 ^ 59
def prefixEnd_7061072 : Nat := 4983230072969 + 3 ^ 40 * 7061072 * 2
def baseEnd_7061072 : Nat := 3625723872004102757026727

theorem tailTrace_7061072 : CollatzResearch.WordTrace tailWord_7061072 prefixEnd_7061072 3625723872004102757026727 := by
  unfold tailWord_7061072
  simp only [CollatzResearch.WordTrace]
  refine ⟨128769226737474776966656735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171692302316633035955542313 128769226737474776966656735)
  ·
    refine ⟨193153840106212165449985103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128769226737474776966656735 193153840106212165449985103)
    ·
      refine ⟨289730760159318248174977655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193153840106212165449985103 289730760159318248174977655)
      ·
        refine ⟨434596140238977372262466483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 289730760159318248174977655 434596140238977372262466483)
        ·
          refine ⟨651894210358466058393699725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 434596140238977372262466483 651894210358466058393699725)
          ·
            refine ⟨244460328884424771897637397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 651894210358466058393699725 244460328884424771897637397)
            ·
              refine ⟨11459077916457411182701753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 244460328884424771897637397 11459077916457411182701753)
              ·
                refine ⟨8594308437343058387026315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11459077916457411182701753 8594308437343058387026315)
                ·
                  refine ⟨12891462656014587580539473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8594308437343058387026315 12891462656014587580539473)
                  ·
                    refine ⟨9668596992010940685404605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12891462656014587580539473 9668596992010940685404605)
                    ·
                      refine ⟨3625723872004102757026727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9668596992010940685404605 3625723872004102757026727)
                      ·
                        rfl

theorem cell23_7061072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 6, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 6, 2, 1, 2, 3].length) (baseStart_7061072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7061072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7061072 prefixEnd_7061072 := by exact prefixLift 7061072
  have htrace : WordTrace (prefixWord ++ tailWord_7061072) baseStart_7061072 baseEnd_7061072 := by
    simpa [prefixWord, tailWord_7061072, baseEnd_7061072] using wordTrace_append hprefix tailTrace_7061072
  have hstable : (prefixWord ++ tailWord_7061072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7061072).length < 2 ^ (prefixWord ++ tailWord_7061072).sum := by decide
  have hdescent : baseEnd_7061072 < baseStart_7061072 := by decide
  rcases family_descends (prefixWord ++ tailWord_7061072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7061088 : List Nat := [2, 1, 1, 3, 2, 1, 1, 2, 1, 9]
def baseStart_7061088 : Nat := 118140960795 + 7061088 * 2 ^ 59
def prefixEnd_7061088 : Nat := 4983230072969 + 3 ^ 40 * 7061088 * 2
def baseEnd_7061088 : Nat := 1208577362564858231475551

theorem tailTrace_7061088 : CollatzResearch.WordTrace tailWord_7061088 prefixEnd_7061088 1208577362564858231475551 := by
  unfold tailWord_7061088
  simp only [CollatzResearch.WordTrace]
  refine ⟨128769518521445794332947959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171692691361927725777263945 128769518521445794332947959)
  ·
    refine ⟨193154277782168691499421939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128769518521445794332947959 193154277782168691499421939)
    ·
      refine ⟨289731416673253037249132909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193154277782168691499421939 289731416673253037249132909)
      ·
        refine ⟨108649281252469888968424841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 289731416673253037249132909 108649281252469888968424841)
        ·
          refine ⟨81486960939352416726318631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108649281252469888968424841 81486960939352416726318631)
          ·
            refine ⟨122230441409028625089477947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81486960939352416726318631 122230441409028625089477947)
            ·
              refine ⟨183345662113542937634216921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122230441409028625089477947 183345662113542937634216921)
              ·
                refine ⟨137509246585157203225662691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 183345662113542937634216921 137509246585157203225662691)
                ·
                  refine ⟨206263869877735804838494037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 137509246585157203225662691 206263869877735804838494037)
                  ·
                    refine ⟨1208577362564858231475551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 206263869877735804838494037 1208577362564858231475551)
                    ·
                      rfl

theorem cell23_7061088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 2, 1, 9].length) (baseStart_7061088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7061088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7061088 prefixEnd_7061088 := by exact prefixLift 7061088
  have htrace : WordTrace (prefixWord ++ tailWord_7061088) baseStart_7061088 baseEnd_7061088 := by
    simpa [prefixWord, tailWord_7061088, baseEnd_7061088] using wordTrace_append hprefix tailTrace_7061088
  have hstable : (prefixWord ++ tailWord_7061088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7061088).length < 2 ^ (prefixWord ++ tailWord_7061088).sum := by decide
  have hdescent : baseEnd_7061088 < baseStart_7061088 := by decide
  rcases family_descends (prefixWord ++ tailWord_7061088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7061129 : List Nat := [1, 2, 1, 1, 4, 1, 5, 2, 1, 3, 2]
def baseStart_7061129 : Nat := 118140960795 + 7061129 * 2 ^ 59
def prefixEnd_7061129 : Nat := 4983230072969 + 3 ^ 40 * 7061129 * 2
def baseEnd_7061129 : Nat := 3625753140401409034013965

theorem tailTrace_7061129 : CollatzResearch.WordTrace tailWord_7061129 prefixEnd_7061129 3625753140401409034013965 := by
  unfold tailWord_7061129
  simp only [CollatzResearch.WordTrace]
  refine ⟨257540532435743052668138441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171693688290495368445425627 257540532435743052668138441)
  ·
    refine ⟨193155399326807289501103831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257540532435743052668138441 193155399326807289501103831)
    ·
      refine ⟨289733098990210934251655747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193155399326807289501103831 289733098990210934251655747)
      ·
        refine ⟨434599648485316401377483621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 289733098990210934251655747 434599648485316401377483621)
        ·
          refine ⟨81487434090996825258278179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 434599648485316401377483621 81487434090996825258278179)
          ·
            refine ⟨122231151136495237887417269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81487434090996825258278179 122231151136495237887417269)
            ·
              refine ⟨11459170419046428551945369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 122231151136495237887417269 11459170419046428551945369)
              ·
                refine ⟨8594377814284821413959027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11459170419046428551945369 8594377814284821413959027)
                ·
                  refine ⟨12891566721427232120938541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8594377814284821413959027 12891566721427232120938541)
                  ·
                    refine ⟨4834337520535212045351953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12891566721427232120938541 4834337520535212045351953)
                    ·
                      refine ⟨3625753140401409034013965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4834337520535212045351953 3625753140401409034013965)
                      ·
                        rfl

theorem cell23_7061129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 5, 2, 1, 3, 2].length) (baseStart_7061129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7061129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7061129 prefixEnd_7061129 := by exact prefixLift 7061129
  have htrace : WordTrace (prefixWord ++ tailWord_7061129) baseStart_7061129 baseEnd_7061129 := by
    simpa [prefixWord, tailWord_7061129, baseEnd_7061129] using wordTrace_append hprefix tailTrace_7061129
  have hstable : (prefixWord ++ tailWord_7061129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7061129).length < 2 ^ (prefixWord ++ tailWord_7061129).sum := by decide
  have hdescent : baseEnd_7061129 < baseStart_7061129 := by decide
  rcases family_descends (prefixWord ++ tailWord_7061129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7061154 : List Nat := [3, 3, 1, 4, 2, 1, 2, 2, 1, 2, 2]
def baseStart_7061154 : Nat := 118140960795 + 7061154 * 2 ^ 59
def prefixEnd_7061154 : Nat := 4983230072969 + 3 ^ 40 * 7061154 * 2
def baseEnd_7061154 : Nat := 3625765977417771436201351

theorem tailTrace_7061154 : CollatzResearch.WordTrace tailWord_7061154 prefixEnd_7061154 3625765977417771436201351 := by
  unfold tailWord_7061154
  simp only [CollatzResearch.WordTrace]
  refine ⟨64385361065163120484449629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171694296173768321291865677 64385361065163120484449629)
  ·
    refine ⟨24144510399436170181668611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64385361065163120484449629 24144510399436170181668611)
    ·
      refine ⟨36216765599154255272502917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24144510399436170181668611 36216765599154255272502917)
      ·
        refine ⟨6790643549841422863594297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36216765599154255272502917 6790643549841422863594297)
        ·
          refine ⟨5092982662381067147695723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6790643549841422863594297 5092982662381067147695723)
          ·
            refine ⟨7639473993571600721543585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5092982662381067147695723 7639473993571600721543585)
            ·
              refine ⟨5729605495178700541157689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7639473993571600721543585 5729605495178700541157689)
              ·
                refine ⟨4297204121384025405868267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5729605495178700541157689 4297204121384025405868267)
                ·
                  refine ⟨6445806182076038108802401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4297204121384025405868267 6445806182076038108802401)
                  ·
                    refine ⟨4834354636557028581601801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6445806182076038108802401 4834354636557028581601801)
                    ·
                      refine ⟨3625765977417771436201351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4834354636557028581601801 3625765977417771436201351)
                      ·
                        rfl

theorem cell23_7061154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 2, 2, 1, 2, 2].length) (baseStart_7061154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7061154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7061154 prefixEnd_7061154 := by exact prefixLift 7061154
  have htrace : WordTrace (prefixWord ++ tailWord_7061154) baseStart_7061154 baseEnd_7061154 := by
    simpa [prefixWord, tailWord_7061154, baseEnd_7061154] using wordTrace_append hprefix tailTrace_7061154
  have hstable : (prefixWord ++ tailWord_7061154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7061154).length < 2 ^ (prefixWord ++ tailWord_7061154).sum := by decide
  have hdescent : baseEnd_7061154 < baseStart_7061154 := by decide
  rcases family_descends (prefixWord ++ tailWord_7061154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7061155 : List Nat := [1, 1, 1, 4, 1, 1, 4, 2, 2, 2, 4]
def baseStart_7061155 : Nat := 118140960795 + 7061155 * 2 ^ 59
def prefixEnd_7061155 : Nat := 4983230072969 + 3 ^ 40 * 7061155 * 2
def baseEnd_7061155 : Nat := 3625766490898425932288845

theorem tailTrace_7061155 : CollatzResearch.WordTrace tailWord_7061155 prefixEnd_7061155 3625766490898425932288845 := by
  unfold tailWord_7061155
  simp only [CollatzResearch.WordTrace]
  refine ⟨257541480733648859108584919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171694320489099239405723279 257541480733648859108584919)
  ·
    refine ⟨386312221100473288662877379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257541480733648859108584919 386312221100473288662877379)
    ·
      refine ⟨579468331650709932994316069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 386312221100473288662877379 579468331650709932994316069)
      ·
        refine ⟨108650312184508112436434263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 579468331650709932994316069 108650312184508112436434263)
        ·
          refine ⟨162975468276762168654651395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108650312184508112436434263 162975468276762168654651395)
          ·
            refine ⟨244463202415143252981977093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162975468276762168654651395 244463202415143252981977093)
            ·
              refine ⟨45836850452839359934120705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 244463202415143252981977093 45836850452839359934120705)
              ·
                refine ⟨34377637839629519950590529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45836850452839359934120705 34377637839629519950590529)
                ·
                  refine ⟨25783228379722139962942897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34377637839629519950590529 25783228379722139962942897)
                  ·
                    refine ⟨19337421284791604972207173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25783228379722139962942897 19337421284791604972207173)
                    ·
                      refine ⟨3625766490898425932288845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19337421284791604972207173 3625766490898425932288845)
                      ·
                        rfl

theorem cell23_7061155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 2, 2, 2, 4].length) (baseStart_7061155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7061155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7061155 prefixEnd_7061155 := by exact prefixLift 7061155
  have htrace : WordTrace (prefixWord ++ tailWord_7061155) baseStart_7061155 baseEnd_7061155 := by
    simpa [prefixWord, tailWord_7061155, baseEnd_7061155] using wordTrace_append hprefix tailTrace_7061155
  have hstable : (prefixWord ++ tailWord_7061155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7061155).length < 2 ^ (prefixWord ++ tailWord_7061155).sum := by decide
  have hdescent : baseEnd_7061155 < baseStart_7061155 := by decide
  rcases family_descends (prefixWord ++ tailWord_7061155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7061182 : List Nat := [4, 2, 1, 1, 2, 3, 1, 2, 7]
def baseStart_7061182 : Nat := 118140960795 + 7061182 * 2 ^ 59
def prefixEnd_7061182 : Nat := 4983230072969 + 3 ^ 40 * 7061182 * 2
def baseEnd_7061182 : Nat := 402864483875121925183469

theorem tailTrace_7061182 : CollatzResearch.WordTrace tailWord_7061182 prefixEnd_7061182 402864483875121925183469 := by
  unfold tailWord_7061182
  simp only [CollatzResearch.WordTrace]
  refine ⟨32192808188068880339977225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 171694977003034028479878533 32192808188068880339977225)
  ·
    refine ⟨24144606141051660254982919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32192808188068880339977225 24144606141051660254982919)
    ·
      refine ⟨36216909211577490382474379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24144606141051660254982919 36216909211577490382474379)
      ·
        refine ⟨54325363817366235573711569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36216909211577490382474379 54325363817366235573711569)
        ·
          refine ⟨40744022863024676680283677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54325363817366235573711569 40744022863024676680283677)
          ·
            refine ⟨15279008573634253755106379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40744022863024676680283677 15279008573634253755106379)
            ·
              refine ⟨22918512860451380632659569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15279008573634253755106379 22918512860451380632659569)
              ·
                refine ⟨17188884645338535474494677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22918512860451380632659569 17188884645338535474494677)
                ·
                  refine ⟨402864483875121925183469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17188884645338535474494677 402864483875121925183469)
                  ·
                    rfl

theorem cell23_7061182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 2, 7].length) (baseStart_7061182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7061182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7061182 prefixEnd_7061182 := by exact prefixLift 7061182
  have htrace : WordTrace (prefixWord ++ tailWord_7061182) baseStart_7061182 baseEnd_7061182 := by
    simpa [prefixWord, tailWord_7061182, baseEnd_7061182] using wordTrace_append hprefix tailTrace_7061182
  have hstable : (prefixWord ++ tailWord_7061182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7061182).length < 2 ^ (prefixWord ++ tailWord_7061182).sum := by decide
  have hdescent : baseEnd_7061182 < baseStart_7061182 := by decide
  rcases family_descends (prefixWord ++ tailWord_7061182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7061232 : List Nat := [2, 1, 1, 1, 3, 1, 2, 3, 1, 6, 2]
def baseStart_7061232 : Nat := 118140960795 + 7061232 * 2 ^ 59
def prefixEnd_7061232 : Nat := 4983230072969 + 3 ^ 40 * 7061232 * 2
def baseEnd_7061232 : Nat := 3625806028908822131025991

theorem tailTrace_7061232 : CollatzResearch.WordTrace tailWord_7061232 prefixEnd_7061232 3625806028908822131025991 := by
  unfold tailWord_7061232
  simp only [CollatzResearch.WordTrace]
  refine ⟨128772144577184950629568975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171696192769579934172758633 128772144577184950629568975)
  ·
    refine ⟨193158216865777425944353463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128772144577184950629568975 193158216865777425944353463)
    ·
      refine ⟨289737325298666138916530195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193158216865777425944353463 289737325298666138916530195)
      ·
        refine ⟨434605987947999208374795293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 289737325298666138916530195 434605987947999208374795293)
        ·
          refine ⟨162977245480499703140548235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 434605987947999208374795293 162977245480499703140548235)
          ·
            refine ⟨244465868220749554710822353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162977245480499703140548235 244465868220749554710822353)
            ·
              refine ⟨183349401165562166033116765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 244465868220749554710822353 183349401165562166033116765)
              ·
                refine ⟨68756025437085812262418787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 183349401165562166033116765 68756025437085812262418787)
                ·
                  refine ⟨103134038155628718393628181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68756025437085812262418787 103134038155628718393628181)
                  ·
                    refine ⟨4834408038545096174701321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 103134038155628718393628181 4834408038545096174701321)
                    ·
                      refine ⟨3625806028908822131025991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4834408038545096174701321 3625806028908822131025991)
                      ·
                        rfl

theorem cell23_7061232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 3, 1, 6, 2].length) (baseStart_7061232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7061232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7061232 prefixEnd_7061232 := by exact prefixLift 7061232
  have htrace : WordTrace (prefixWord ++ tailWord_7061232) baseStart_7061232 baseEnd_7061232 := by
    simpa [prefixWord, tailWord_7061232, baseEnd_7061232] using wordTrace_append hprefix tailTrace_7061232
  have hstable : (prefixWord ++ tailWord_7061232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7061232).length < 2 ^ (prefixWord ++ tailWord_7061232).sum := by decide
  have hdescent : baseEnd_7061232 < baseStart_7061232 := by decide
  rcases family_descends (prefixWord ++ tailWord_7061232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7061245 : List Nat := [1, 4, 1, 1, 1, 1, 2, 2, 1, 3, 6]
def baseStart_7061245 : Nat := 118140960795 + 7061245 * 2 ^ 59
def prefixEnd_7061245 : Nat := 4983230072969 + 3 ^ 40 * 7061245 * 2
def baseEnd_7061245 : Nat := 3625812704157330580163431

theorem tailTrace_7061245 : CollatzResearch.WordTrace tailWord_7061245 prefixEnd_7061245 3625812704157330580163431 := by
  unfold tailWord_7061245
  simp only [CollatzResearch.WordTrace]
  refine ⟨257544763303322804479361189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171696508868881869652907459 257544763303322804479361189)
  ·
    refine ⟨48289643119373025839880223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 257544763303322804479361189 48289643119373025839880223)
    ·
      refine ⟨72434464679059538759820335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48289643119373025839880223 72434464679059538759820335)
      ·
        refine ⟨108651697018589308139730503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72434464679059538759820335 108651697018589308139730503)
        ·
          refine ⟨162977545527883962209595755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108651697018589308139730503 162977545527883962209595755)
          ·
            refine ⟨244466318291825943314393633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162977545527883962209595755 244466318291825943314393633)
            ·
              refine ⟨183349738718869457485795225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 244466318291825943314393633 183349738718869457485795225)
              ·
                refine ⟨137512304039152093114346419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 183349738718869457485795225 137512304039152093114346419)
                ·
                  refine ⟨206268456058728139671519629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 137512304039152093114346419 206268456058728139671519629)
                  ·
                    refine ⟨77350671022023052376819861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 206268456058728139671519629 77350671022023052376819861)
                    ·
                      refine ⟨3625812704157330580163431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 77350671022023052376819861 3625812704157330580163431)
                      ·
                        rfl

theorem cell23_7061245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 2, 1, 3, 6].length) (baseStart_7061245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7061245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7061245 prefixEnd_7061245 := by exact prefixLift 7061245
  have htrace : WordTrace (prefixWord ++ tailWord_7061245) baseStart_7061245 baseEnd_7061245 := by
    simpa [prefixWord, tailWord_7061245, baseEnd_7061245] using wordTrace_append hprefix tailTrace_7061245
  have hstable : (prefixWord ++ tailWord_7061245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7061245).length < 2 ^ (prefixWord ++ tailWord_7061245).sum := by decide
  have hdescent : baseEnd_7061245 < baseStart_7061245 := by decide
  rcases family_descends (prefixWord ++ tailWord_7061245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7061266 : List Nat := [3, 2, 4, 1, 1, 2, 1, 2, 2, 1, 4]
def baseStart_7061266 : Nat := 118140960795 + 7061266 * 2 ^ 59
def prefixEnd_7061266 : Nat := 4983230072969 + 3 ^ 40 * 7061266 * 2
def baseEnd_7061266 : Nat := 3625823487251074998000835

theorem tailTrace_7061266 : CollatzResearch.WordTrace tailWord_7061266 prefixEnd_7061266 3625823487251074998000835 := by
  unfold tailWord_7061266
  simp only [CollatzResearch.WordTrace]
  refine ⟨64386382309061681266468913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171697019490831150043917101 64386382309061681266468913)
  ·
    refine ⟨48289786731796260949851685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64386382309061681266468913 48289786731796260949851685)
    ·
      refine ⟨9054335012211798928097191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48289786731796260949851685 9054335012211798928097191)
      ·
        refine ⟨13581502518317698392145787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9054335012211798928097191 13581502518317698392145787)
        ·
          refine ⟨20372253777476547588218681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13581502518317698392145787 20372253777476547588218681)
          ·
            refine ⟨15279190333107410691164011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20372253777476547588218681 15279190333107410691164011)
            ·
              refine ⟨22918785499661116036746017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15279190333107410691164011 22918785499661116036746017)
              ·
                refine ⟨17189089124745837027559513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22918785499661116036746017 17189089124745837027559513)
                ·
                  refine ⟨12891816843559377770669635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17189089124745837027559513 12891816843559377770669635)
                  ·
                    refine ⟨19337725265339066656004453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12891816843559377770669635 19337725265339066656004453)
                    ·
                      refine ⟨3625823487251074998000835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19337725265339066656004453 3625823487251074998000835)
                      ·
                        rfl

theorem cell23_7061266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_7061266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7061266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7061266 prefixEnd_7061266 := by exact prefixLift 7061266
  have htrace : WordTrace (prefixWord ++ tailWord_7061266) baseStart_7061266 baseEnd_7061266 := by
    simpa [prefixWord, tailWord_7061266, baseEnd_7061266] using wordTrace_append hprefix tailTrace_7061266
  have hstable : (prefixWord ++ tailWord_7061266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7061266).length < 2 ^ (prefixWord ++ tailWord_7061266).sum := by decide
  have hdescent : baseEnd_7061266 < baseStart_7061266 := by decide
  rcases family_descends (prefixWord ++ tailWord_7061266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7061269 : List Nat := [1, 3, 2, 1, 2, 4, 1, 2, 2, 2, 3]
def baseStart_7061269 : Nat := 118140960795 + 7061269 * 2 ^ 59
def prefixEnd_7061269 : Nat := 4983230072969 + 3 ^ 40 * 7061269 * 2
def baseEnd_7061269 : Nat := 3625825027693038486263321

theorem tailTrace_7061269 : CollatzResearch.WordTrace tailWord_7061269 prefixEnd_7061269 3625825027693038486263321 := by
  unfold tailWord_7061269
  simp only [CollatzResearch.WordTrace]
  refine ⟨257545638655235856578234861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171697092436823904385489907 257545638655235856578234861)
  ·
    refine ⟨96579614495713446216838073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 257545638655235856578234861 96579614495713446216838073)
    ·
      refine ⟨72434710871785084662628555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96579614495713446216838073 72434710871785084662628555)
      ·
        refine ⟨108652066307677626993942833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72434710871785084662628555 108652066307677626993942833)
        ·
          refine ⟨81489049730758220245457125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108652066307677626993942833 81489049730758220245457125)
          ·
            refine ⟨15279196824517166296023211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 81489049730758220245457125 15279196824517166296023211)
            ·
              refine ⟨22918795236775749444034817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15279196824517166296023211 22918795236775749444034817)
              ·
                refine ⟨17189096427581812083026113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22918795236775749444034817 17189096427581812083026113)
                ·
                  refine ⟨12891822320686359062269585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17189096427581812083026113 12891822320686359062269585)
                  ·
                    refine ⟨9668866740514769296702189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12891822320686359062269585 9668866740514769296702189)
                    ·
                      refine ⟨3625825027693038486263321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9668866740514769296702189 3625825027693038486263321)
                      ·
                        rfl

theorem cell23_7061269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 2, 2, 2, 3].length) (baseStart_7061269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7061269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7061269 prefixEnd_7061269 := by exact prefixLift 7061269
  have htrace : WordTrace (prefixWord ++ tailWord_7061269) baseStart_7061269 baseEnd_7061269 := by
    simpa [prefixWord, tailWord_7061269, baseEnd_7061269] using wordTrace_append hprefix tailTrace_7061269
  have hstable : (prefixWord ++ tailWord_7061269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7061269).length < 2 ^ (prefixWord ++ tailWord_7061269).sum := by decide
  have hdescent : baseEnd_7061269 < baseStart_7061269 := by decide
  rcases family_descends (prefixWord ++ tailWord_7061269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7061295 : List Nat := [1, 1, 2, 1, 2, 1, 2, 3, 2, 1, 7]
def baseStart_7061295 : Nat := 118140960795 + 7061295 * 2 ^ 59
def prefixEnd_7061295 : Nat := 4983230072969 + 3 ^ 40 * 7061295 * 2
def baseEnd_7061295 : Nat := 3625838378190055384538201

theorem tailTrace_7061295 : CollatzResearch.WordTrace tailWord_7061295 prefixEnd_7061295 3625838378190055384538201 := by
  unfold tailWord_7061295
  simp only [CollatzResearch.WordTrace]
  refine ⟨257546586953141663018681339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171697724635427775345787559 257546586953141663018681339)
  ·
    refine ⟨386319880429712494528022009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257546586953141663018681339 386319880429712494528022009)
    ·
      refine ⟨289739910322284370896016507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 386319880429712494528022009 289739910322284370896016507)
      ·
        refine ⟨434609865483426556344024761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 289739910322284370896016507 434609865483426556344024761)
        ·
          refine ⟨325957399112569917258018571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 434609865483426556344024761 325957399112569917258018571)
          ·
            refine ⟨488936098668854875887027857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 325957399112569917258018571 488936098668854875887027857)
            ·
              refine ⟨366702074001641156915270893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 488936098668854875887027857 366702074001641156915270893)
              ·
                refine ⟨137513277750615433843226585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 366702074001641156915270893 137513277750615433843226585)
                ·
                  refine ⟨103134958312961575382419939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 137513277750615433843226585 103134958312961575382419939)
                  ·
                    refine ⟨154702437469442363073629909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 103134958312961575382419939 154702437469442363073629909)
                    ·
                      refine ⟨3625838378190055384538201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 154702437469442363073629909 3625838378190055384538201)
                      ·
                        rfl

theorem cell23_7061295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 3, 2, 1, 7].length) (baseStart_7061295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7061295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7061295 prefixEnd_7061295 := by exact prefixLift 7061295
  have htrace : WordTrace (prefixWord ++ tailWord_7061295) baseStart_7061295 baseEnd_7061295 := by
    simpa [prefixWord, tailWord_7061295, baseEnd_7061295] using wordTrace_append hprefix tailTrace_7061295
  have hstable : (prefixWord ++ tailWord_7061295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7061295).length < 2 ^ (prefixWord ++ tailWord_7061295).sum := by decide
  have hdescent : baseEnd_7061295 < baseStart_7061295 := by decide
  rcases family_descends (prefixWord ++ tailWord_7061295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7061333 : List Nat := [1, 3, 2, 2, 2, 3, 1, 4, 1, 1, 3]
def baseStart_7061333 : Nat := 118140960795 + 7061333 * 2 ^ 59
def prefixEnd_7061333 : Nat := 4983230072969 + 3 ^ 40 * 7061333 * 2
def baseEnd_7061333 : Nat := 3625857890454926235863027

theorem tailTrace_7061333 : CollatzResearch.WordTrace tailWord_7061333 prefixEnd_7061333 3625857890454926235863027 := by
  unfold tailWord_7061333
  simp only [CollatzResearch.WordTrace]
  refine ⟨257547972927003995508564653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171698648618002663672376435 257547972927003995508564653)
  ·
    refine ⟨96580489847626498315711745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 257547972927003995508564653 96580489847626498315711745)
    ·
      refine ⟨72435367385719873736783809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96580489847626498315711745 72435367385719873736783809)
      ·
        refine ⟨54326525539289905302587857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72435367385719873736783809 54326525539289905302587857)
        ·
          refine ⟨40744894154467428976940893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54326525539289905302587857 40744894154467428976940893)
          ·
            refine ⟨15279335307925285866352835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40744894154467428976940893 15279335307925285866352835)
            ·
              refine ⟨22919002961887928799529253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15279335307925285866352835 22919002961887928799529253)
              ·
                refine ⟨4297313055353986649911735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22919002961887928799529253 4297313055353986649911735)
                ·
                  refine ⟨6445969583030979974867603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4297313055353986649911735 6445969583030979974867603)
                  ·
                    refine ⟨9668954374546469962301405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6445969583030979974867603 9668954374546469962301405)
                    ·
                      refine ⟨3625857890454926235863027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9668954374546469962301405 3625857890454926235863027)
                      ·
                        rfl

theorem cell23_7061333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 4, 1, 1, 3].length) (baseStart_7061333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7061333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7061333 prefixEnd_7061333 := by exact prefixLift 7061333
  have htrace : WordTrace (prefixWord ++ tailWord_7061333) baseStart_7061333 baseEnd_7061333 := by
    simpa [prefixWord, tailWord_7061333, baseEnd_7061333] using wordTrace_append hprefix tailTrace_7061333
  have hstable : (prefixWord ++ tailWord_7061333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7061333).length < 2 ^ (prefixWord ++ tailWord_7061333).sum := by decide
  have hdescent : baseEnd_7061333 < baseStart_7061333 := by decide
  rcases family_descends (prefixWord ++ tailWord_7061333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7061356 : List Nat := [2, 2, 1, 1, 4, 2, 1, 1, 5, 2, 2]
def baseStart_7061356 : Nat := 118140960795 + 7061356 * 2 ^ 59
def prefixEnd_7061356 : Nat := 4983230072969 + 3 ^ 40 * 7061356 * 2
def baseEnd_7061356 : Nat := 3625869700509979645875421

theorem tailTrace_7061356 : CollatzResearch.WordTrace tailWord_7061356 prefixEnd_7061356 3625869700509979645875421 := by
  unfold tailWord_7061356
  simp only [CollatzResearch.WordTrace]
  refine ⟨128774405902960335218325961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171699207870613780291101281 128774405902960335218325961)
  ·
    refine ⟨96580804427220251413744471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128774405902960335218325961 96580804427220251413744471)
    ·
      refine ⟨144871206640830377120616707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96580804427220251413744471 144871206640830377120616707)
      ·
        refine ⟨217306809961245565680925061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144871206640830377120616707 217306809961245565680925061)
        ·
          refine ⟨40745026867733543565173449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 217306809961245565680925061 40745026867733543565173449)
          ·
            refine ⟨30558770150800157673880087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40745026867733543565173449 30558770150800157673880087)
            ·
              refine ⟨45838155226200236510820131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30558770150800157673880087 45838155226200236510820131)
              ·
                refine ⟨68757232839300354766230197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45838155226200236510820131 68757232839300354766230197)
                ·
                  refine ⟨6445990578684408259334081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 68757232839300354766230197 6445990578684408259334081)
                  ·
                    refine ⟨4834492934013306194500561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6445990578684408259334081 4834492934013306194500561)
                    ·
                      refine ⟨3625869700509979645875421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4834492934013306194500561 3625869700509979645875421)
                      ·
                        rfl

theorem cell23_7061356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 2, 2].length) (baseStart_7061356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7061356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7061356 prefixEnd_7061356 := by exact prefixLift 7061356
  have htrace : WordTrace (prefixWord ++ tailWord_7061356) baseStart_7061356 baseEnd_7061356 := by
    simpa [prefixWord, tailWord_7061356, baseEnd_7061356] using wordTrace_append hprefix tailTrace_7061356
  have hstable : (prefixWord ++ tailWord_7061356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7061356).length < 2 ^ (prefixWord ++ tailWord_7061356).sum := by decide
  have hdescent : baseEnd_7061356 < baseStart_7061356 := by decide
  rcases family_descends (prefixWord ++ tailWord_7061356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7061383 : List Nat := [1, 1, 4, 2, 4, 2, 1, 2, 2, 4]
def baseStart_7061383 : Nat := 118140960795 + 7061383 * 2 ^ 59
def prefixEnd_7061383 : Nat := 4983230072969 + 3 ^ 40 * 7061383 * 2
def baseEnd_7061383 : Nat := 1208627854829217013412599

theorem tailTrace_7061383 : CollatzResearch.WordTrace tailWord_7061383 prefixEnd_7061383 1208627854829217013412599 := by
  unfold tailWord_7061383
  simp only [CollatzResearch.WordTrace]
  refine ⟨257549796576822854047884803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171699864384548569365256535 257549796576822854047884803)
  ·
    refine ⟨386324694865234281071827205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257549796576822854047884803 386324694865234281071827205)
    ·
      refine ⟨72435880287231427700967601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 386324694865234281071827205 72435880287231427700967601)
      ·
        refine ⟨54326910215423570775725701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72435880287231427700967601 54326910215423570775725701)
        ·
          refine ⟨10186295665391919520448569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54326910215423570775725701 10186295665391919520448569)
          ·
            refine ⟨7639721749043939640336427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10186295665391919520448569 7639721749043939640336427)
            ·
              refine ⟨11459582623565909460504641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7639721749043939640336427 11459582623565909460504641)
              ·
                refine ⟨8594686967674432095378481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11459582623565909460504641 8594686967674432095378481)
                ·
                  refine ⟨6446015225755824071533861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8594686967674432095378481 6446015225755824071533861)
                  ·
                    refine ⟨1208627854829217013412599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6446015225755824071533861 1208627854829217013412599)
                    ·
                      rfl

theorem cell23_7061383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 1, 2, 2, 4].length) (baseStart_7061383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7061383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7061383 prefixEnd_7061383 := by exact prefixLift 7061383
  have htrace : WordTrace (prefixWord ++ tailWord_7061383) baseStart_7061383 baseEnd_7061383 := by
    simpa [prefixWord, tailWord_7061383, baseEnd_7061383] using wordTrace_append hprefix tailTrace_7061383
  have hstable : (prefixWord ++ tailWord_7061383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7061383).length < 2 ^ (prefixWord ++ tailWord_7061383).sum := by decide
  have hdescent : baseEnd_7061383 < baseStart_7061383 := by decide
  rcases family_descends (prefixWord ++ tailWord_7061383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7061400 : List Nat := [2, 1, 2, 6, 1, 1, 3, 1, 2, 4]
def baseStart_7061400 : Nat := 118140960795 + 7061400 * 2 ^ 59
def prefixEnd_7061400 : Nat := 4983230072969 + 3 ^ 40 * 7061400 * 2
def baseEnd_7061400 : Nat := 1208630764552925824575073

theorem tailTrace_7061400 : CollatzResearch.WordTrace tailWord_7061400 prefixEnd_7061400 1208630764552925824575073 := by
  unfold tailWord_7061400
  simp only [CollatzResearch.WordTrace]
  refine ⟨128775208308880632975626827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171700277745174177300835769 128775208308880632975626827)
  ·
    refine ⟨193162812463320949463440241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128775208308880632975626827 193162812463320949463440241)
    ·
      refine ⟨144872109347490712097580181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193162812463320949463440241 144872109347490712097580181)
      ·
        refine ⟨6790880125663627129574071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 144872109347490712097580181 6790880125663627129574071)
        ·
          refine ⟨10186320188495440694361107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6790880125663627129574071 10186320188495440694361107)
          ·
            refine ⟨15279480282743161041541661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10186320188495440694361107 15279480282743161041541661)
            ·
              refine ⟨5729805106028685390578123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15279480282743161041541661 5729805106028685390578123)
              ·
                refine ⟨8594707659043028085867185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5729805106028685390578123 8594707659043028085867185)
                ·
                  refine ⟨6446030744282271064400389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8594707659043028085867185 6446030744282271064400389)
                  ·
                    refine ⟨1208630764552925824575073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6446030744282271064400389 1208630764552925824575073)
                    ·
                      rfl

theorem cell23_7061400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 3, 1, 2, 4].length) (baseStart_7061400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7061400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7061400 prefixEnd_7061400 := by exact prefixLift 7061400
  have htrace : WordTrace (prefixWord ++ tailWord_7061400) baseStart_7061400 baseEnd_7061400 := by
    simpa [prefixWord, tailWord_7061400, baseEnd_7061400] using wordTrace_append hprefix tailTrace_7061400
  have hstable : (prefixWord ++ tailWord_7061400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7061400).length < 2 ^ (prefixWord ++ tailWord_7061400).sum := by decide
  have hdescent : baseEnd_7061400 < baseStart_7061400 := by decide
  rcases family_descends (prefixWord ++ tailWord_7061400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7061463 : List Nat := [1, 1, 3, 2, 1, 1, 5, 3, 2, 2, 2]
def baseStart_7061463 : Nat := 118140960795 + 7061463 * 2 ^ 59
def prefixEnd_7061463 : Nat := 4983230072969 + 3 ^ 40 * 7061463 * 2
def baseEnd_7061463 : Nat := 3625924642940010727237429

theorem tailTrace_7061463 : CollatzResearch.WordTrace tailWord_7061463 prefixEnd_7061463 3625924642940010727237429 := by
  unfold tailWord_7061463
  simp only [CollatzResearch.WordTrace]
  refine ⟨257552714416533027710797043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171701809611022018473864695 257552714416533027710797043)
  ·
    refine ⟨386329071624799541566195565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257552714416533027710797043 386329071624799541566195565)
    ·
      refine ⟨144873401859299828087323337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 386329071624799541566195565 144873401859299828087323337)
      ·
        refine ⟨108655051394474871065492503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144873401859299828087323337 108655051394474871065492503)
        ·
          refine ⟨162982577091712306598238755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108655051394474871065492503 162982577091712306598238755)
          ·
            refine ⟨244473865637568459897358133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162982577091712306598238755 244473865637568459897358133)
            ·
              refine ⟨22919424903522043115377325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 244473865637568459897358133 22919424903522043115377325)
              ·
                refine ⟨8594784338820766168266497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22919424903522043115377325 8594784338820766168266497)
                ·
                  refine ⟨6446088254115574626199873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8594784338820766168266497 6446088254115574626199873)
                  ·
                    refine ⟨4834566190586680969649905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6446088254115574626199873 4834566190586680969649905)
                    ·
                      refine ⟨3625924642940010727237429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4834566190586680969649905 3625924642940010727237429)
                      ·
                        rfl

theorem cell23_7061463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 3, 2, 2, 2].length) (baseStart_7061463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7061463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7061463 prefixEnd_7061463 := by exact prefixLift 7061463
  have htrace : WordTrace (prefixWord ++ tailWord_7061463) baseStart_7061463 baseEnd_7061463 := by
    simpa [prefixWord, tailWord_7061463, baseEnd_7061463] using wordTrace_append hprefix tailTrace_7061463
  have hstable : (prefixWord ++ tailWord_7061463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7061463).length < 2 ^ (prefixWord ++ tailWord_7061463).sum := by decide
  have hdescent : baseEnd_7061463 < baseStart_7061463 := by decide
  rcases family_descends (prefixWord ++ tailWord_7061463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7061472 : List Nat := [2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 8]
def baseStart_7061472 : Nat := 118140960795 + 7061472 * 2 ^ 59
def prefixEnd_7061472 : Nat := 4983230072969 + 3 ^ 40 * 7061472 * 2
def baseEnd_7061472 : Nat := 3625929264265901192024887

theorem tailTrace_7061472 : CollatzResearch.WordTrace tailWord_7061472 prefixEnd_7061472 3625929264265901192024887 := by
  unfold tailWord_7061472
  simp only [CollatzResearch.WordTrace]
  refine ⟨128776521336750211123937335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171702028449000281498583113 128776521336750211123937335)
  ·
    refine ⟨193164782005125316685906003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128776521336750211123937335 193164782005125316685906003)
    ·
      refine ⟨289747173007687975028859005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193164782005125316685906003 289747173007687975028859005)
      ·
        refine ⟨108655189877882990635822127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 289747173007687975028859005 108655189877882990635822127)
        ·
          refine ⟨162982784816824485953733191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108655189877882990635822127 162982784816824485953733191)
          ·
            refine ⟨244474177225236728930599787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162982784816824485953733191 244474177225236728930599787)
            ·
              refine ⟨366711265837855093395899681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 244474177225236728930599787 366711265837855093395899681)
              ·
                refine ⟨275033449378391320046924761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 366711265837855093395899681 275033449378391320046924761)
                ·
                  refine ⟨206275087033793490035193571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 275033449378391320046924761 206275087033793490035193571)
                  ·
                    refine ⟨309412630550690235052790357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 206275087033793490035193571 309412630550690235052790357)
                    ·
                      refine ⟨3625929264265901192024887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 309412630550690235052790357 3625929264265901192024887)
                      ·
                        rfl

theorem cell23_7061472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 8].length) (baseStart_7061472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7061472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7061472 prefixEnd_7061472 := by exact prefixLift 7061472
  have htrace : WordTrace (prefixWord ++ tailWord_7061472) baseStart_7061472 baseEnd_7061472 := by
    simpa [prefixWord, tailWord_7061472, baseEnd_7061472] using wordTrace_append hprefix tailTrace_7061472
  have hstable : (prefixWord ++ tailWord_7061472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7061472).length < 2 ^ (prefixWord ++ tailWord_7061472).sum := by decide
  have hdescent : baseEnd_7061472 < baseStart_7061472 := by decide
  rcases family_descends (prefixWord ++ tailWord_7061472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7061499 : List Nat := [1, 1, 1, 1, 1, 3, 6, 2, 2, 5]
def baseStart_7061499 : Nat := 118140960795 + 7061499 * 2 ^ 59
def prefixEnd_7061499 : Nat := 4983230072969 + 3 ^ 40 * 7061499 * 2
def baseEnd_7061499 : Nat := 1208647709414524195462421

theorem tailTrace_7061499 : CollatzResearch.WordTrace tailWord_7061499 prefixEnd_7061499 1208647709414524195462421 := by
  unfold tailWord_7061499
  simp only [CollatzResearch.WordTrace]
  refine ⟨257554027444402605859107551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171702684962935070572738367 257554027444402605859107551)
  ·
    refine ⟨386331041166603908788661327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257554027444402605859107551 386331041166603908788661327)
    ·
      refine ⟨579496561749905863182991991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 386331041166603908788661327 579496561749905863182991991)
      ·
        refine ⟨869244842624858794774487987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 579496561749905863182991991 869244842624858794774487987)
        ·
          refine ⟨1303867263937288192161731981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 869244842624858794774487987 1303867263937288192161731981)
          ·
            refine ⟨488950223976483072060649493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1303867263937288192161731981 488950223976483072060649493)
            ·
              refine ⟨22919541748897644002842945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 488950223976483072060649493 22919541748897644002842945)
              ·
                refine ⟨17189656311673233002132209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22919541748897644002842945 17189656311673233002132209)
                ·
                  refine ⟨12892242233754924751599157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17189656311673233002132209 12892242233754924751599157)
                  ·
                    refine ⟨1208647709414524195462421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12892242233754924751599157 1208647709414524195462421)
                    ·
                      rfl

theorem cell23_7061499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 2, 2, 5].length) (baseStart_7061499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7061499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7061499 prefixEnd_7061499 := by exact prefixLift 7061499
  have htrace : WordTrace (prefixWord ++ tailWord_7061499) baseStart_7061499 baseEnd_7061499 := by
    simpa [prefixWord, tailWord_7061499, baseEnd_7061499] using wordTrace_append hprefix tailTrace_7061499
  have hstable : (prefixWord ++ tailWord_7061499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7061499).length < 2 ^ (prefixWord ++ tailWord_7061499).sum := by decide
  have hdescent : baseEnd_7061499 < baseStart_7061499 := by decide
  rcases family_descends (prefixWord ++ tailWord_7061499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7061509 : List Nat := [1, 3, 1, 1, 2, 4, 2, 1, 1, 2, 5]
def baseStart_7061509 : Nat := 118140960795 + 7061509 * 2 ^ 59
def prefixEnd_7061509 : Nat := 4983230072969 + 3 ^ 40 * 7061509 * 2
def baseEnd_7061509 : Nat := 3625948263050117547262217

theorem tailTrace_7061509 : CollatzResearch.WordTrace tailWord_7061509 prefixEnd_7061509 3625948263050117547262217 := by
  unfold tailWord_7061509
  simp only [CollatzResearch.WordTrace]
  refine ⟨257554392174366377566971581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171702928116244251711314387 257554392174366377566971581)
  ·
    refine ⟨96582897065387391587614343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 257554392174366377566971581 96582897065387391587614343)
    ·
      refine ⟨144874345598081087381421515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96582897065387391587614343 144874345598081087381421515)
      ·
        refine ⟨217311518397121631072132273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144874345598081087381421515 217311518397121631072132273)
        ·
          refine ⟨162983638797841223304099205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 217311518397121631072132273 162983638797841223304099205)
          ·
            refine ⟨30559432274595229369518601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 162983638797841223304099205 30559432274595229369518601)
            ·
              refine ⟨22919574205946422027138951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30559432274595229369518601 22919574205946422027138951)
              ·
                refine ⟨34379361308919633040708427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22919574205946422027138951 34379361308919633040708427)
                ·
                  refine ⟨51569041963379449561062641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34379361308919633040708427 51569041963379449561062641)
                  ·
                    refine ⟨38676781472534587170796981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51569041963379449561062641 38676781472534587170796981)
                    ·
                      refine ⟨3625948263050117547262217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38676781472534587170796981 3625948263050117547262217)
                      ·
                        rfl

theorem cell23_7061509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 1, 1, 2, 5].length) (baseStart_7061509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7061509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7061509 prefixEnd_7061509 := by exact prefixLift 7061509
  have htrace : WordTrace (prefixWord ++ tailWord_7061509) baseStart_7061509 baseEnd_7061509 := by
    simpa [prefixWord, tailWord_7061509, baseEnd_7061509] using wordTrace_append hprefix tailTrace_7061509
  have hstable : (prefixWord ++ tailWord_7061509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7061509).length < 2 ^ (prefixWord ++ tailWord_7061509).sum := by decide
  have hdescent : baseEnd_7061509 < baseStart_7061509 := by decide
  rcases family_descends (prefixWord ++ tailWord_7061509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7061533 : List Nat := [1, 4, 2, 2, 2, 3, 1, 1, 2, 5]
def baseStart_7061533 : Nat := 118140960795 + 7061533 * 2 ^ 59
def prefixEnd_7061533 : Nat := 4983230072969 + 3 ^ 40 * 7061533 * 2
def baseEnd_7061533 : Nat := 1208653528861941817787369

theorem tailTrace_7061533 : CollatzResearch.WordTrace tailWord_7061533 prefixEnd_7061533 1208653528861941817787369 := by
  unfold tailWord_7061533
  simp only [CollatzResearch.WordTrace]
  refine ⟨257555267526279429665845253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171703511684186286443896835 257555267526279429665845253)
  ·
    refine ⟨48291612661177393062345985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 257555267526279429665845253 48291612661177393062345985)
    ·
      refine ⟨36218709495883044796759489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48291612661177393062345985 36218709495883044796759489)
      ·
        refine ⟨27164032121912283597569617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36218709495883044796759489 27164032121912283597569617)
        ·
          refine ⟨20373024091434212698177213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27164032121912283597569617 20373024091434212698177213)
          ·
            refine ⟨7639884034287829761816455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20373024091434212698177213 7639884034287829761816455)
            ·
              refine ⟨11459826051431744642724683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7639884034287829761816455 11459826051431744642724683)
              ·
                refine ⟨17189739077147616964087025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11459826051431744642724683 17189739077147616964087025)
                ·
                  refine ⟨12892304307860712723065269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17189739077147616964087025 12892304307860712723065269)
                  ·
                    refine ⟨1208653528861941817787369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12892304307860712723065269 1208653528861941817787369)
                    ·
                      rfl

theorem cell23_7061533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 1, 1, 2, 5].length) (baseStart_7061533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7061533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7061533 prefixEnd_7061533 := by exact prefixLift 7061533
  have htrace : WordTrace (prefixWord ++ tailWord_7061533) baseStart_7061533 baseEnd_7061533 := by
    simpa [prefixWord, tailWord_7061533, baseEnd_7061533] using wordTrace_append hprefix tailTrace_7061533
  have hstable : (prefixWord ++ tailWord_7061533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7061533).length < 2 ^ (prefixWord ++ tailWord_7061533).sum := by decide
  have hdescent : baseEnd_7061533 < baseStart_7061533 := by decide
  rcases family_descends (prefixWord ++ tailWord_7061533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7061590 : List Nat := [5, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3]
def baseStart_7061590 : Nat := 118140960795 + 7061590 * 2 ^ 59
def prefixEnd_7061590 : Nat := 4983230072969 + 3 ^ 40 * 7061590 * 2
def baseEnd_7061590 : Nat := 3625989854983131730349345

theorem tailTrace_7061590 : CollatzResearch.WordTrace tailWord_7061590 prefixEnd_7061590 3625989854983131730349345 := by
  unfold tailWord_7061590
  simp only [CollatzResearch.WordTrace]
  refine ⟨16097334155442058025041889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 171704897658048618933780149 16097334155442058025041889)
  ·
    refine ⟨12073000616581543518781417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16097334155442058025041889 12073000616581543518781417)
    ·
      refine ⟨9054750462436157639086063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12073000616581543518781417 9054750462436157639086063)
      ·
        refine ⟨13582125693654236458629095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9054750462436157639086063 13582125693654236458629095)
        ·
          refine ⟨20373188540481354687943643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13582125693654236458629095 20373188540481354687943643)
          ·
            refine ⟨30559782810722032031915465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20373188540481354687943643 30559782810722032031915465)
            ·
              refine ⟨22919837108041524023936599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30559782810722032031915465 22919837108041524023936599)
              ·
                refine ⟨34379755662062286035904899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22919837108041524023936599 34379755662062286035904899)
                ·
                  refine ⟨51569633493093429053857349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34379755662062286035904899 51569633493093429053857349)
                  ·
                    refine ⟨9669306279955017947598253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51569633493093429053857349 9669306279955017947598253)
                    ·
                      refine ⟨3625989854983131730349345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9669306279955017947598253 3625989854983131730349345)
                      ·
                        rfl

theorem cell23_7061590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3].length) (baseStart_7061590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7061590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7061590 prefixEnd_7061590 := by exact prefixLift 7061590
  have htrace : WordTrace (prefixWord ++ tailWord_7061590) baseStart_7061590 baseEnd_7061590 := by
    simpa [prefixWord, tailWord_7061590, baseEnd_7061590] using wordTrace_append hprefix tailTrace_7061590
  have hstable : (prefixWord ++ tailWord_7061590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7061590).length < 2 ^ (prefixWord ++ tailWord_7061590).sum := by decide
  have hdescent : baseEnd_7061590 < baseStart_7061590 := by decide
  rcases family_descends (prefixWord ++ tailWord_7061590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7061597 : List Nat := [1, 4, 4, 1, 1, 1, 3, 3, 1, 4]
def baseStart_7061597 : Nat := 118140960795 + 7061597 * 2 ^ 59
def prefixEnd_7061597 : Nat := 4983230072969 + 3 ^ 40 * 7061597 * 2
def baseEnd_7061597 : Nat := 1208664483115904400987271

theorem tailTrace_7061597 : CollatzResearch.WordTrace tailWord_7061597 prefixEnd_7061597 1208664483115904400987271 := by
  unfold tailWord_7061597
  simp only [CollatzResearch.WordTrace]
  refine ⟨257557601798047568596175045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171705067865365045730783363 257557601798047568596175045)
  ·
    refine ⟨48292050337133919111782821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 257557601798047568596175045 48292050337133919111782821)
    ·
      refine ⟨9054759438212609833459279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48292050337133919111782821 9054759438212609833459279)
      ·
        refine ⟨13582139157318914750188919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9054759438212609833459279 13582139157318914750188919)
        ·
          refine ⟨20373208735978372125283379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13582139157318914750188919 20373208735978372125283379)
          ·
            refine ⟨30559813103967558187925069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20373208735978372125283379 30559813103967558187925069)
            ·
              refine ⟨11459929913987834320471901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30559813103967558187925069 11459929913987834320471901)
              ·
                refine ⟨4297473717745437870176963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11459929913987834320471901 4297473717745437870176963)
                ·
                  refine ⟨6446210576618156805265445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4297473717745437870176963 6446210576618156805265445)
                  ·
                    refine ⟨1208664483115904400987271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6446210576618156805265445 1208664483115904400987271)
                    ·
                      rfl

theorem cell23_7061597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 3, 3, 1, 4].length) (baseStart_7061597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7061597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7061597 prefixEnd_7061597 := by exact prefixLift 7061597
  have htrace : WordTrace (prefixWord ++ tailWord_7061597) baseStart_7061597 baseEnd_7061597 := by
    simpa [prefixWord, tailWord_7061597, baseEnd_7061597] using wordTrace_append hprefix tailTrace_7061597
  have hstable : (prefixWord ++ tailWord_7061597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7061597).length < 2 ^ (prefixWord ++ tailWord_7061597).sum := by decide
  have hdescent : baseEnd_7061597 < baseStart_7061597 := by decide
  rcases family_descends (prefixWord ++ tailWord_7061597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7061636 : List Nat := [2, 3, 2, 1, 2, 1, 2, 3, 1, 6]
def baseStart_7061636 : Nat := 118140960795 + 7061636 * 2 ^ 59
def prefixEnd_7061636 : Nat := 4983230072969 + 3 ^ 40 * 7061636 * 2
def baseEnd_7061636 : Nat := 1208671158364412850124711

theorem tailTrace_7061636 : CollatzResearch.WordTrace tailWord_7061636 prefixEnd_7061636 1208671158364412850124711 := by
  unfold tailWord_7061636
  simp only [CollatzResearch.WordTrace]
  refine ⟨128779512122453139128422381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171706016163270852171229841 128779512122453139128422381)
  ·
    refine ⟨48292317045919927173158393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128779512122453139128422381 48292317045919927173158393)
    ·
      refine ⟨36219237784439945379868795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48292317045919927173158393 36219237784439945379868795)
      ·
        refine ⟨54328856676659918069803193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36219237784439945379868795 54328856676659918069803193)
        ·
          refine ⟨40746642507494938552352395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54328856676659918069803193 40746642507494938552352395)
          ·
            refine ⟨61119963761242407828528593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40746642507494938552352395 61119963761242407828528593)
            ·
              refine ⟨45839972820931805871396445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61119963761242407828528593 45839972820931805871396445)
              ·
                refine ⟨17189989807849427201773667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45839972820931805871396445 17189989807849427201773667)
                ·
                  refine ⟨25784984711774140802660501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17189989807849427201773667 25784984711774140802660501)
                  ·
                    refine ⟨1208671158364412850124711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25784984711774140802660501 1208671158364412850124711)
                    ·
                      rfl

theorem cell23_7061636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 3, 1, 6].length) (baseStart_7061636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7061636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7061636 prefixEnd_7061636 := by exact prefixLift 7061636
  have htrace : WordTrace (prefixWord ++ tailWord_7061636) baseStart_7061636 baseEnd_7061636 := by
    simpa [prefixWord, tailWord_7061636, baseEnd_7061636] using wordTrace_append hprefix tailTrace_7061636
  have hstable : (prefixWord ++ tailWord_7061636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7061636).length < 2 ^ (prefixWord ++ tailWord_7061636).sum := by decide
  have hdescent : baseEnd_7061636 < baseStart_7061636 := by decide
  rcases family_descends (prefixWord ++ tailWord_7061636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7061640 : List Nat := [2, 1, 3, 4, 1, 3, 1, 2, 1, 5]
def baseStart_7061640 : Nat := 118140960795 + 7061640 * 2 ^ 59
def prefixEnd_7061640 : Nat := 4983230072969 + 3 ^ 40 * 7061640 * 2
def baseEnd_7061640 : Nat := 1208671843005285511574705

theorem tailTrace_7061640 : CollatzResearch.WordTrace tailWord_7061640 prefixEnd_7061640 1208671843005285511574705 := by
  unfold tailWord_7061640
  simp only [CollatzResearch.WordTrace]
  refine ⟨128779585068445893469995187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171706113424594524626660249 128779585068445893469995187)
  ·
    refine ⟨193169377602668840204992781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128779585068445893469995187 193169377602668840204992781)
    ·
      refine ⟨72438516601000815076872293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 193169377602668840204992781 72438516601000815076872293)
      ·
        refine ⟨13582221862687652826913555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72438516601000815076872293 13582221862687652826913555)
        ·
          refine ⟨20373332794031479240370333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13582221862687652826913555 20373332794031479240370333)
          ·
            refine ⟨7639999797761804715138875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20373332794031479240370333 7639999797761804715138875)
            ·
              refine ⟨11459999696642707072708313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7639999797761804715138875 11459999696642707072708313)
              ·
                refine ⟨8594999772482030304531235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11459999696642707072708313 8594999772482030304531235)
                ·
                  refine ⟨12892499658723045456796853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8594999772482030304531235 12892499658723045456796853)
                  ·
                    refine ⟨1208671843005285511574705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12892499658723045456796853 1208671843005285511574705)
                    ·
                      rfl

theorem cell23_7061640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 1, 2, 1, 5].length) (baseStart_7061640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7061640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7061640 prefixEnd_7061640 := by exact prefixLift 7061640
  have htrace : WordTrace (prefixWord ++ tailWord_7061640) baseStart_7061640 baseEnd_7061640 := by
    simpa [prefixWord, tailWord_7061640, baseEnd_7061640] using wordTrace_append hprefix tailTrace_7061640
  have hstable : (prefixWord ++ tailWord_7061640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7061640).length < 2 ^ (prefixWord ++ tailWord_7061640).sum := by decide
  have hdescent : baseEnd_7061640 < baseStart_7061640 := by decide
  rcases family_descends (prefixWord ++ tailWord_7061640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7061660 : List Nat := [2, 2, 3, 2, 1, 1, 5, 1, 1, 1, 4]
def baseStart_7061660 : Nat := 118140960795 + 7061660 * 2 ^ 59
def prefixEnd_7061660 : Nat := 4983230072969 + 3 ^ 40 * 7061660 * 2
def baseEnd_7061660 : Nat := 3626025798628946456474023

theorem tailTrace_7061660 : CollatzResearch.WordTrace tailWord_7061660 prefixEnd_7061660 3626025798628946456474023 := by
  unfold tailWord_7061660
  simp only [CollatzResearch.WordTrace]
  refine ⟨128779949798409665177859217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171706599731212886903812289 128779949798409665177859217)
  ·
    refine ⟨96584962348807248883394413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128779949798409665177859217 96584962348807248883394413)
    ·
      refine ⟨36219360880802718331272905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96584962348807248883394413 36219360880802718331272905)
      ·
        refine ⟨27164520660602038748454679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36219360880802718331272905 27164520660602038748454679)
        ·
          refine ⟨40746780990903058122682019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27164520660602038748454679 40746780990903058122682019)
          ·
            refine ⟨61120171486354587184023029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40746780990903058122682019 61120171486354587184023029)
            ·
              refine ⟨5730016076845742548502159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 61120171486354587184023029 5730016076845742548502159)
              ·
                refine ⟨8595024115268613822753239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5730016076845742548502159 8595024115268613822753239)
                ·
                  refine ⟨12892536172902920734129859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8595024115268613822753239 12892536172902920734129859)
                  ·
                    refine ⟨19338804259354381101194789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12892536172902920734129859 19338804259354381101194789)
                    ·
                      refine ⟨3626025798628946456474023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19338804259354381101194789 3626025798628946456474023)
                      ·
                        rfl

theorem cell23_7061660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 5, 1, 1, 1, 4].length) (baseStart_7061660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7061660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7061660 prefixEnd_7061660 := by exact prefixLift 7061660
  have htrace : WordTrace (prefixWord ++ tailWord_7061660) baseStart_7061660 baseEnd_7061660 := by
    simpa [prefixWord, tailWord_7061660, baseEnd_7061660] using wordTrace_append hprefix tailTrace_7061660
  have hstable : (prefixWord ++ tailWord_7061660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7061660).length < 2 ^ (prefixWord ++ tailWord_7061660).sum := by decide
  have hdescent : baseEnd_7061660 < baseStart_7061660 := by decide
  rcases family_descends (prefixWord ++ tailWord_7061660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7061663 : List Nat := [1, 1, 2, 6, 1, 1, 3, 1, 1, 1, 5]
def baseStart_7061663 : Nat := 118140960795 + 7061663 * 2 ^ 59
def prefixEnd_7061663 : Nat := 4983230072969 + 3 ^ 40 * 7061663 * 2
def baseEnd_7061663 : Nat := 3626027339070909944736509

theorem tailTrace_7061663 : CollatzResearch.WordTrace tailWord_7061663 prefixEnd_7061663 3626027339070909944736509 := by
  unfold tailWord_7061663
  simp only [CollatzResearch.WordTrace]
  refine ⟨257560009015808461868077643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171706672677205641245385095 257560009015808461868077643)
  ·
    refine ⟨386340013523712692802116465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257560009015808461868077643 386340013523712692802116465)
    ·
      refine ⟨289755010142784519601587349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 386340013523712692802116465 289755010142784519601587349)
      ·
        refine ⟨13582266100443024356324407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 289755010142784519601587349 13582266100443024356324407)
        ·
          refine ⟨20373399150664536534486611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13582266100443024356324407 20373399150664536534486611)
          ·
            refine ⟨30560098725996804801729917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20373399150664536534486611 30560098725996804801729917)
            ·
              refine ⟨11460037022248801800648719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30560098725996804801729917 11460037022248801800648719)
              ·
                refine ⟨17190055533373202700973079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11460037022248801800648719 17190055533373202700973079)
                ·
                  refine ⟨25785083300059804051459619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17190055533373202700973079 25785083300059804051459619)
                  ·
                    refine ⟨38677624950089706077189429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25785083300059804051459619 38677624950089706077189429)
                    ·
                      refine ⟨3626027339070909944736509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38677624950089706077189429 3626027339070909944736509)
                      ·
                        rfl

theorem cell23_7061663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 3, 1, 1, 1, 5].length) (baseStart_7061663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7061663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7061663 prefixEnd_7061663 := by exact prefixLift 7061663
  have htrace : WordTrace (prefixWord ++ tailWord_7061663) baseStart_7061663 baseEnd_7061663 := by
    simpa [prefixWord, tailWord_7061663, baseEnd_7061663] using wordTrace_append hprefix tailTrace_7061663
  have hstable : (prefixWord ++ tailWord_7061663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7061663).length < 2 ^ (prefixWord ++ tailWord_7061663).sum := by decide
  have hdescent : baseEnd_7061663 < baseStart_7061663 := by decide
  rcases family_descends (prefixWord ++ tailWord_7061663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7061666 : List Nat := [3, 3, 1, 3, 1, 12]
def baseStart_7061666 : Nat := 118140960795 + 7061666 * 2 ^ 59
def prefixEnd_7061666 : Nat := 4983230072969 + 3 ^ 40 * 7061666 * 2
def baseEnd_7061666 : Nat := 14921929545320466802465

theorem tailTrace_7061666 : CollatzResearch.WordTrace tailWord_7061666 prefixEnd_7061666 14921929545320466802465 := by
  unfold tailWord_7061666
  simp only [CollatzResearch.WordTrace]
  refine ⟨64390029608699398345109213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171706745623198395586957901 64390029608699398345109213)
  ·
    refine ⟨24146261103262274379415955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64390029608699398345109213 24146261103262274379415955)
    ·
      refine ⟨36219391654893411569123933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24146261103262274379415955 36219391654893411569123933)
      ·
        refine ⟨13582271870585029338421475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36219391654893411569123933 13582271870585029338421475)
        ·
          refine ⟨20373407805877544007632213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13582271870585029338421475 20373407805877544007632213)
          ·
            refine ⟨14921929545320466802465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 20373407805877544007632213 14921929545320466802465)
            ·
              rfl

theorem cell23_7061666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 12].length) (baseStart_7061666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7061666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7061666 prefixEnd_7061666 := by exact prefixLift 7061666
  have htrace : WordTrace (prefixWord ++ tailWord_7061666) baseStart_7061666 baseEnd_7061666 := by
    simpa [prefixWord, tailWord_7061666, baseEnd_7061666] using wordTrace_append hprefix tailTrace_7061666
  have hstable : (prefixWord ++ tailWord_7061666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7061666).length < 2 ^ (prefixWord ++ tailWord_7061666).sum := by decide
  have hdescent : baseEnd_7061666 < baseStart_7061666 := by decide
  rcases family_descends (prefixWord ++ tailWord_7061666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7061671 : List Nat := [1, 1, 6, 2, 2, 2, 2, 2, 1, 1, 3]
def baseStart_7061671 : Nat := 118140960795 + 7061671 * 2 ^ 59
def prefixEnd_7061671 : Nat := 4983230072969 + 3 ^ 40 * 7061671 * 2
def baseEnd_7061671 : Nat := 3626031446916145913436473

theorem tailTrace_7061671 : CollatzResearch.WordTrace tailWord_7061671 prefixEnd_7061671 3626031446916145913436473 := by
  unfold tailWord_7061671
  simp only [CollatzResearch.WordTrace]
  refine ⟨257560300799779479234368867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171706867199852986156245911 257560300799779479234368867)
  ·
    refine ⟨386340451199669218851553301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257560300799779479234368867 386340451199669218851553301)
    ·
      refine ⟨18109708649984494633666561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 386340451199669218851553301 18109708649984494633666561)
      ·
        refine ⟨13582281487488370975249921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18109708649984494633666561 13582281487488370975249921)
        ·
          refine ⟨10186711115616278231437441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13582281487488370975249921 10186711115616278231437441)
          ·
            refine ⟨7640033336712208673578081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10186711115616278231437441 7640033336712208673578081)
            ·
              refine ⟨5730025002534156505183561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7640033336712208673578081 5730025002534156505183561)
              ·
                refine ⟨4297518751900617378887671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5730025002534156505183561 4297518751900617378887671)
                ·
                  refine ⟨6446278127850926068331507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4297518751900617378887671 6446278127850926068331507)
                  ·
                    refine ⟨9669417191776389102497261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6446278127850926068331507 9669417191776389102497261)
                    ·
                      refine ⟨3626031446916145913436473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9669417191776389102497261 3626031446916145913436473)
                      ·
                        rfl

theorem cell23_7061671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 2, 2, 1, 1, 3].length) (baseStart_7061671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7061671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7061671 prefixEnd_7061671 := by exact prefixLift 7061671
  have htrace : WordTrace (prefixWord ++ tailWord_7061671) baseStart_7061671 baseEnd_7061671 := by
    simpa [prefixWord, tailWord_7061671, baseEnd_7061671] using wordTrace_append hprefix tailTrace_7061671
  have hstable : (prefixWord ++ tailWord_7061671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7061671).length < 2 ^ (prefixWord ++ tailWord_7061671).sum := by decide
  have hdescent : baseEnd_7061671 < baseStart_7061671 := by decide
  rcases family_descends (prefixWord ++ tailWord_7061671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7061693 : List Nat := [1, 4, 1, 2, 1, 1, 1, 2, 6, 1, 3]
def baseStart_7061693 : Nat := 118140960795 + 7061693 * 2 ^ 59
def prefixEnd_7061693 : Nat := 4983230072969 + 3 ^ 40 * 7061693 * 2
def baseEnd_7061693 : Nat := 3626042743490544827361371

theorem tailTrace_7061693 : CollatzResearch.WordTrace tailWord_7061693 prefixEnd_7061693 3626042743490544827361371 := by
  unfold tailWord_7061693
  simp only [CollatzResearch.WordTrace]
  refine ⟨257561103205699776991669733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171707402137133184661113155 257561103205699776991669733)
  ·
    refine ⟨48292706851068708185938075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 257561103205699776991669733 48292706851068708185938075)
    ·
      refine ⟨72439060276603062278907113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48292706851068708185938075 72439060276603062278907113)
      ·
        refine ⟨54329295207452296709180335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72439060276603062278907113 54329295207452296709180335)
        ·
          refine ⟨81493942811178445063770503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54329295207452296709180335 81493942811178445063770503)
          ·
            refine ⟨122240914216767667595655755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81493942811178445063770503 122240914216767667595655755)
            ·
              refine ⟨183361371325151501393483633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122240914216767667595655755 183361371325151501393483633)
              ·
                refine ⟨137521028493863626045112725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 183361371325151501393483633 137521028493863626045112725)
                ·
                  refine ⟨6446298210649857470864659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 137521028493863626045112725 6446298210649857470864659)
                  ·
                    refine ⟨9669447315974786206296989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6446298210649857470864659 9669447315974786206296989)
                    ·
                      refine ⟨3626042743490544827361371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9669447315974786206296989 3626042743490544827361371)
                      ·
                        rfl

theorem cell23_7061693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 2, 6, 1, 3].length) (baseStart_7061693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7061693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7061693 prefixEnd_7061693 := by exact prefixLift 7061693
  have htrace : WordTrace (prefixWord ++ tailWord_7061693) baseStart_7061693 baseEnd_7061693 := by
    simpa [prefixWord, tailWord_7061693, baseEnd_7061693] using wordTrace_append hprefix tailTrace_7061693
  have hstable : (prefixWord ++ tailWord_7061693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7061693).length < 2 ^ (prefixWord ++ tailWord_7061693).sum := by decide
  have hdescent : baseEnd_7061693 < baseStart_7061693 := by decide
  rcases family_descends (prefixWord ++ tailWord_7061693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7061706 : List Nat := [3, 1, 2, 1, 3, 1, 2, 1, 2, 2, 5]
def baseStart_7061706 : Nat := 118140960795 + 7061706 * 2 ^ 59
def prefixEnd_7061706 : Nat := 4983230072969 + 3 ^ 40 * 7061706 * 2
def baseEnd_7061706 : Nat := 3626049418739053276498811

theorem tailTrace_7061706 : CollatzResearch.WordTrace tailWord_7061706 prefixEnd_7061706 3626049418739053276498811 := by
  unfold tailWord_7061706
  simp only [CollatzResearch.WordTrace]
  refine ⟨64390394338663170052973243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171707718236435120141261981 64390394338663170052973243)
  ·
    refine ⟨96585591507994755079459865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64390394338663170052973243 96585591507994755079459865)
    ·
      refine ⟨72439193630996066309594899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96585591507994755079459865 72439193630996066309594899)
      ·
        refine ⟨108658790446494099464392349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72439193630996066309594899 108658790446494099464392349)
        ·
          refine ⟨40747046417435287299147131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108658790446494099464392349 40747046417435287299147131)
          ·
            refine ⟨61120569626152930948720697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40747046417435287299147131 61120569626152930948720697)
            ·
              refine ⟨45840427219614698211540523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61120569626152930948720697 45840427219614698211540523)
              ·
                refine ⟨68760640829422047317310785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45840427219614698211540523 68760640829422047317310785)
                ·
                  refine ⟨51570480622066535487983089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68760640829422047317310785 51570480622066535487983089)
                  ·
                    refine ⟨38677860466549901615987317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51570480622066535487983089 38677860466549901615987317)
                    ·
                      refine ⟨3626049418739053276498811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38677860466549901615987317 3626049418739053276498811)
                      ·
                        rfl

theorem cell23_7061706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 1, 2, 2, 5].length) (baseStart_7061706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7061706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7061706 prefixEnd_7061706 := by exact prefixLift 7061706
  have htrace : WordTrace (prefixWord ++ tailWord_7061706) baseStart_7061706 baseEnd_7061706 := by
    simpa [prefixWord, tailWord_7061706, baseEnd_7061706] using wordTrace_append hprefix tailTrace_7061706
  have hstable : (prefixWord ++ tailWord_7061706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7061706).length < 2 ^ (prefixWord ++ tailWord_7061706).sum := by decide
  have hdescent : baseEnd_7061706 < baseStart_7061706 := by decide
  rcases family_descends (prefixWord ++ tailWord_7061706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7061816 : List Nat := [2, 1, 2, 1, 3, 1, 2, 1, 2, 8]
def baseStart_7061816 : Nat := 118140960795 + 7061816 * 2 ^ 59
def prefixEnd_7061816 : Nat := 4983230072969 + 3 ^ 40 * 7061816 * 2
def baseEnd_7061816 : Nat := 1208701967203682615374435

theorem tailTrace_7061816 : CollatzResearch.WordTrace tailWord_7061816 prefixEnd_7061816 1208701967203682615374435 := by
  unfold tailWord_7061816
  simp only [CollatzResearch.WordTrace]
  refine ⟨128782794692127084499198651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171710392922836112665598201 128782794692127084499198651)
  ·
    refine ⟨193174192038190626748797977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128782794692127084499198651 193174192038190626748797977)
    ·
      refine ⟨144880644028642970061598483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193174192038190626748797977 144880644028642970061598483)
      ·
        refine ⟨217320966042964455092397725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144880644028642970061598483 217320966042964455092397725)
        ·
          refine ⟨81495362266111670659649147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 217320966042964455092397725 81495362266111670659649147)
          ·
            refine ⟨122243043399167505989473721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81495362266111670659649147 122243043399167505989473721)
            ·
              refine ⟨91682282549375629492105291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122243043399167505989473721 91682282549375629492105291)
              ·
                refine ⟨137523423824063444238157937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91682282549375629492105291 137523423824063444238157937)
                ·
                  refine ⟨103142567868047583178618453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 137523423824063444238157937 103142567868047583178618453)
                  ·
                    refine ⟨1208701967203682615374435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 103142567868047583178618453 1208701967203682615374435)
                    ·
                      rfl

theorem cell23_7061816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 1, 2, 8].length) (baseStart_7061816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7061816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7061816 prefixEnd_7061816 := by exact prefixLift 7061816
  have htrace : WordTrace (prefixWord ++ tailWord_7061816) baseStart_7061816 baseEnd_7061816 := by
    simpa [prefixWord, tailWord_7061816, baseEnd_7061816] using wordTrace_append hprefix tailTrace_7061816
  have hstable : (prefixWord ++ tailWord_7061816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7061816).length < 2 ^ (prefixWord ++ tailWord_7061816).sum := by decide
  have hdescent : baseEnd_7061816 < baseStart_7061816 := by decide
  rcases family_descends (prefixWord ++ tailWord_7061816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7061843 : List Nat := [1, 1, 1, 2, 1, 1, 4, 3, 4, 2, 3]
def baseStart_7061843 : Nat := 118140960795 + 7061843 * 2 ^ 59
def prefixEnd_7061843 : Nat := 4983230072969 + 3 ^ 40 * 7061843 * 2
def baseEnd_7061843 : Nat := 3626119765588719240485681

theorem tailTrace_7061843 : CollatzResearch.WordTrace tailWord_7061843 prefixEnd_7061843 3626119765588719240485681 := by
  unfold tailWord_7061843
  simp only [CollatzResearch.WordTrace]
  refine ⟨257566574155156352609630183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171711049436770901739753455 257566574155156352609630183)
  ·
    refine ⟨386349861232734528914445275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257566574155156352609630183 386349861232734528914445275)
    ·
      refine ⟨579524791849101793371667913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 386349861232734528914445275 579524791849101793371667913)
      ·
        refine ⟨434643593886826345028750935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 579524791849101793371667913 434643593886826345028750935)
        ·
          refine ⟨651965390830239517543126403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 434643593886826345028750935 651965390830239517543126403)
          ·
            refine ⟨977948086245359276314689605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 651965390830239517543126403 977948086245359276314689605)
            ·
              refine ⟨183365266171004864309004301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 977948086245359276314689605 183365266171004864309004301)
              ·
                refine ⟨68761974814126824115876613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 183365266171004864309004301 68761974814126824115876613)
                ·
                  refine ⟨12892870277648779521726865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 68761974814126824115876613 12892870277648779521726865)
                  ·
                    refine ⟨9669652708236584641295149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12892870277648779521726865 9669652708236584641295149)
                    ·
                      refine ⟨3626119765588719240485681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9669652708236584641295149 3626119765588719240485681)
                      ·
                        rfl

theorem cell23_7061843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 3, 4, 2, 3].length) (baseStart_7061843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7061843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7061843 prefixEnd_7061843 := by exact prefixLift 7061843
  have htrace : WordTrace (prefixWord ++ tailWord_7061843) baseStart_7061843 baseEnd_7061843 := by
    simpa [prefixWord, tailWord_7061843, baseEnd_7061843] using wordTrace_append hprefix tailTrace_7061843
  have hstable : (prefixWord ++ tailWord_7061843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7061843).length < 2 ^ (prefixWord ++ tailWord_7061843).sum := by decide
  have hdescent : baseEnd_7061843 < baseStart_7061843 := by decide
  rcases family_descends (prefixWord ++ tailWord_7061843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7061877 : List Nat := [1, 3, 4, 1, 2, 1, 3, 1, 2, 2, 3]
def baseStart_7061877 : Nat := 118140960795 + 7061877 * 2 ^ 59
def prefixEnd_7061877 : Nat := 4983230072969 + 3 ^ 40 * 7061877 * 2
def baseEnd_7061877 : Nat := 3626137223930972107460525

theorem tailTrace_7061877 : CollatzResearch.WordTrace tailWord_7061877 prefixEnd_7061877 3626137223930972107460525 := by
  unfold tailWord_7061877
  simp only [CollatzResearch.WordTrace]
  refine ⟨257567814237033176416367885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171711876158022117610911923 257567814237033176416367885)
  ·
    refine ⟨96587930338887441156137957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 257567814237033176416367885 96587930338887441156137957)
    ·
      refine ⟨18110236938541395216775867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 96587930338887441156137957 18110236938541395216775867)
      ·
        refine ⟨27165355407812092825163801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18110236938541395216775867 27165355407812092825163801)
        ·
          refine ⟨20374016555859069618872851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27165355407812092825163801 20374016555859069618872851)
          ·
            refine ⟨30561024833788604428309277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20374016555859069618872851 30561024833788604428309277)
            ·
              refine ⟨11460384312670726660615979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30561024833788604428309277 11460384312670726660615979)
              ·
                refine ⟨17190576469006089990923969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11460384312670726660615979 17190576469006089990923969)
                ·
                  refine ⟨12892932351754567493192977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17190576469006089990923969 12892932351754567493192977)
                  ·
                    refine ⟨9669699263815925619894733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12892932351754567493192977 9669699263815925619894733)
                    ·
                      refine ⟨3626137223930972107460525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9669699263815925619894733 3626137223930972107460525)
                      ·
                        rfl

theorem cell23_7061877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 3, 1, 2, 2, 3].length) (baseStart_7061877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7061877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7061877 prefixEnd_7061877 := by exact prefixLift 7061877
  have htrace : WordTrace (prefixWord ++ tailWord_7061877) baseStart_7061877 baseEnd_7061877 := by
    simpa [prefixWord, tailWord_7061877, baseEnd_7061877] using wordTrace_append hprefix tailTrace_7061877
  have hstable : (prefixWord ++ tailWord_7061877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7061877).length < 2 ^ (prefixWord ++ tailWord_7061877).sum := by decide
  have hdescent : baseEnd_7061877 < baseStart_7061877 := by decide
  rcases family_descends (prefixWord ++ tailWord_7061877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7061927 : List Nat := [1, 1, 6, 1, 1, 3, 2, 2, 1, 5]
def baseStart_7061927 : Nat := 118140960795 + 7061927 * 2 ^ 59
def prefixEnd_7061927 : Nat := 4983230072969 + 3 ^ 40 * 7061927 * 2
def baseEnd_7061927 : Nat := 1208720965987898970611765

theorem tailTrace_7061927 : CollatzResearch.WordTrace tailWord_7061927 prefixEnd_7061927 1208720965987898970611765 := by
  unfold tailWord_7061927
  simp only [CollatzResearch.WordTrace]
  refine ⟨257569637886852034955688035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171713091924568023303792023 257569637886852034955688035)
  ·
    refine ⟨386354456830278052433532053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257569637886852034955688035 386354456830278052433532053)
    ·
      refine ⟨18110365163919283707821815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 386354456830278052433532053 18110365163919283707821815)
      ·
        refine ⟨27165547745878925561732723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18110365163919283707821815 27165547745878925561732723)
        ·
          refine ⟨40748321618818388342599085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27165547745878925561732723 40748321618818388342599085)
          ·
            refine ⟨15280620607056895628474657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40748321618818388342599085 15280620607056895628474657)
            ·
              refine ⟨11460465455292671721355993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15280620607056895628474657 11460465455292671721355993)
              ·
                refine ⟨8595349091469503791016995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11460465455292671721355993 8595349091469503791016995)
                ·
                  refine ⟨12893023637204255686525493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8595349091469503791016995 12893023637204255686525493)
                  ·
                    refine ⟨1208720965987898970611765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12893023637204255686525493 1208720965987898970611765)
                    ·
                      rfl

theorem cell23_7061927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 2, 2, 1, 5].length) (baseStart_7061927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7061927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7061927 prefixEnd_7061927 := by exact prefixLift 7061927
  have htrace : WordTrace (prefixWord ++ tailWord_7061927) baseStart_7061927 baseEnd_7061927 := by
    simpa [prefixWord, tailWord_7061927, baseEnd_7061927] using wordTrace_append hprefix tailTrace_7061927
  have hstable : (prefixWord ++ tailWord_7061927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7061927).length < 2 ^ (prefixWord ++ tailWord_7061927).sum := by decide
  have hdescent : baseEnd_7061927 < baseStart_7061927 := by decide
  rcases family_descends (prefixWord ++ tailWord_7061927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7061950 : List Nat := [4, 2, 1, 1, 1, 1, 3, 3, 1, 1, 5]
def baseStart_7061950 : Nat := 118140960795 + 7061950 * 2 ^ 59
def prefixEnd_7061950 : Nat := 4983230072969 + 3 ^ 40 * 7061950 * 2
def baseEnd_7061950 : Nat := 3626174708018750321847689

theorem tailTrace_7061950 : CollatzResearch.WordTrace tailWord_7061950 prefixEnd_7061950 3626174708018750321847689 := by
  unfold tailWord_7061950
  simp only [CollatzResearch.WordTrace]
  refine ⟨32196309595721088735471913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 171713651177179139922516869 32196309595721088735471913)
  ·
    refine ⟨24147232196790816551603935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32196309595721088735471913 24147232196790816551603935)
    ·
      refine ⟨36220848295186224827405903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24147232196790816551603935 36220848295186224827405903)
      ·
        refine ⟨54331272442779337241108855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36220848295186224827405903 54331272442779337241108855)
        ·
          refine ⟨81496908664169005861663283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54331272442779337241108855 81496908664169005861663283)
          ·
            refine ⟨122245362996253508792494925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81496908664169005861663283 122245362996253508792494925)
            ·
              refine ⟨45842011123595065797185597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 122245362996253508792494925 45842011123595065797185597)
              ·
                refine ⟨17190754171348149673944599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45842011123595065797185597 17190754171348149673944599)
                ·
                  refine ⟨25786131257022224510916899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17190754171348149673944599 25786131257022224510916899)
                  ·
                    refine ⟨38679196885533336766375349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25786131257022224510916899 38679196885533336766375349)
                    ·
                      refine ⟨3626174708018750321847689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38679196885533336766375349 3626174708018750321847689)
                      ·
                        rfl

theorem cell23_7061950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 3, 1, 1, 5].length) (baseStart_7061950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7061950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7061950 prefixEnd_7061950 := by exact prefixLift 7061950
  have htrace : WordTrace (prefixWord ++ tailWord_7061950) baseStart_7061950 baseEnd_7061950 := by
    simpa [prefixWord, tailWord_7061950, baseEnd_7061950] using wordTrace_append hprefix tailTrace_7061950
  have hstable : (prefixWord ++ tailWord_7061950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7061950).length < 2 ^ (prefixWord ++ tailWord_7061950).sum := by decide
  have hdescent : baseEnd_7061950 < baseStart_7061950 := by decide
  rcases family_descends (prefixWord ++ tailWord_7061950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7061974 : List Nat := [5, 2, 1, 1, 1, 1, 3, 3, 2, 4]
def baseStart_7061974 : Nat := 118140960795 + 7061974 * 2 ^ 59
def prefixEnd_7061974 : Nat := 4983230072969 + 3 ^ 40 * 7061974 * 2
def baseEnd_7061974 : Nat := 1208729010518152742649193

theorem tailTrace_7061974 : CollatzResearch.WordTrace tailWord_7061974 prefixEnd_7061974 1208729010518152742649193 := by
  unfold tailWord_7061974
  simp only [CollatzResearch.WordTrace]
  refine ⟨16098209507355110123915561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 171714234745121174655099317 16098209507355110123915561)
  ·
    refine ⟨12073657130516332592936671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16098209507355110123915561 12073657130516332592936671)
    ·
      refine ⟨18110485695774498889405007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12073657130516332592936671 18110485695774498889405007)
      ·
        refine ⟨27165728543661748334107511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18110485695774498889405007 27165728543661748334107511)
        ·
          refine ⟨40748592815492622501161267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27165728543661748334107511 40748592815492622501161267)
          ·
            refine ⟨61122889223238933751741901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40748592815492622501161267 61122889223238933751741901)
            ·
              refine ⟨22921083458714600156903213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61122889223238933751741901 22921083458714600156903213)
              ·
                refine ⟨8595406297017975058838705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22921083458714600156903213 8595406297017975058838705)
                ·
                  refine ⟨6446554722763481294129029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8595406297017975058838705 6446554722763481294129029)
                  ·
                    refine ⟨1208729010518152742649193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6446554722763481294129029 1208729010518152742649193)
                    ·
                      rfl

theorem cell23_7061974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 3, 2, 4].length) (baseStart_7061974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7061974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7061974 prefixEnd_7061974 := by exact prefixLift 7061974
  have htrace : WordTrace (prefixWord ++ tailWord_7061974) baseStart_7061974 baseEnd_7061974 := by
    simpa [prefixWord, tailWord_7061974, baseEnd_7061974] using wordTrace_append hprefix tailTrace_7061974
  have hstable : (prefixWord ++ tailWord_7061974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7061974).length < 2 ^ (prefixWord ++ tailWord_7061974).sum := by decide
  have hdescent : baseEnd_7061974 < baseStart_7061974 := by decide
  rcases family_descends (prefixWord ++ tailWord_7061974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7061993 : List Nat := [1, 2, 1, 1, 1, 2, 1, 5, 2, 2, 5]
def baseStart_7061993 : Nat := 118140960795 + 7061993 * 2 ^ 59
def prefixEnd_7061993 : Nat := 4983230072969 + 3 ^ 40 * 7061993 * 2
def baseEnd_7061993 : Nat := 3626196787686893653609991

theorem tailTrace_7061993 : CollatzResearch.WordTrace tailWord_7061993 prefixEnd_7061993 3626196787686893653609991 := by
  unfold tailWord_7061993
  simp only [CollatzResearch.WordTrace]
  refine ⟨257572045104612928227590633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171714696736408618818393755 257572045104612928227590633)
  ·
    refine ⟨193179033828459696170692975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257572045104612928227590633 193179033828459696170692975)
    ·
      refine ⟨289768550742689544256039463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193179033828459696170692975 289768550742689544256039463)
      ·
        refine ⟨434652826114034316384059195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 289768550742689544256039463 434652826114034316384059195)
        ·
          refine ⟨651979239171051474576088793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 434652826114034316384059195 651979239171051474576088793)
          ·
            refine ⟨488984429378288605932066595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 651979239171051474576088793 488984429378288605932066595)
            ·
              refine ⟨733476644067432908898099893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 488984429378288605932066595 733476644067432908898099893)
              ·
                refine ⟨68763435381321835209196865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 733476644067432908898099893 68763435381321835209196865)
                ·
                  refine ⟨51572576535991376406897649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68763435381321835209196865 51572576535991376406897649)
                  ·
                    refine ⟨38679432401993532305173237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51572576535991376406897649 38679432401993532305173237)
                    ·
                      refine ⟨3626196787686893653609991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38679432401993532305173237 3626196787686893653609991)
                      ·
                        rfl

theorem cell23_7061993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 5, 2, 2, 5].length) (baseStart_7061993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7061993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7061993 prefixEnd_7061993 := by exact prefixLift 7061993
  have htrace : WordTrace (prefixWord ++ tailWord_7061993) baseStart_7061993 baseEnd_7061993 := by
    simpa [prefixWord, tailWord_7061993, baseEnd_7061993] using wordTrace_append hprefix tailTrace_7061993
  have hstable : (prefixWord ++ tailWord_7061993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7061993).length < 2 ^ (prefixWord ++ tailWord_7061993).sum := by decide
  have hdescent : baseEnd_7061993 < baseStart_7061993 := by decide
  rcases family_descends (prefixWord ++ tailWord_7061993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7061997 : List Nat := [1, 5, 1, 3, 1, 1, 1, 1, 3, 3, 3]
def baseStart_7061997 : Nat := 118140960795 + 7061997 * 2 ^ 59
def prefixEnd_7061997 : Nat := 4983230072969 + 3 ^ 40 * 7061997 * 2
def baseEnd_7061997 : Nat := 3626198841609511637959973

theorem tailTrace_7061997 : CollatzResearch.WordTrace tailWord_7061997 prefixEnd_7061997 3626198841609511637959973 := by
  unfold tailWord_7061997
  simp only [CollatzResearch.WordTrace]
  refine ⟨257572190996598436910736245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171714793997732291273824163 257572190996598436910736245)
  ·
    refine ⟨24147392905931103460381523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 257572190996598436910736245 24147392905931103460381523)
    ·
      refine ⟨36221089358896655190572285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24147392905931103460381523 36221089358896655190572285)
      ·
        refine ⟨13582908509586245696464607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36221089358896655190572285 13582908509586245696464607)
        ·
          refine ⟨20374362764379368544696911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13582908509586245696464607 20374362764379368544696911)
          ·
            refine ⟨30561544146569052817045367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20374362764379368544696911 30561544146569052817045367)
            ·
              refine ⟨45842316219853579225568051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30561544146569052817045367 45842316219853579225568051)
              ·
                refine ⟨68763474329780368838352077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45842316219853579225568051 68763474329780368838352077)
                ·
                  refine ⟨25786302873667638314382029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68763474329780368838352077 25786302873667638314382029)
                  ·
                    refine ⟨9669863577625364367893261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25786302873667638314382029 9669863577625364367893261)
                    ·
                      refine ⟨3626198841609511637959973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9669863577625364367893261 3626198841609511637959973)
                      ·
                        rfl

theorem cell23_7061997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 1, 3, 3, 3].length) (baseStart_7061997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7061997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7061997 prefixEnd_7061997 := by exact prefixLift 7061997
  have htrace : WordTrace (prefixWord ++ tailWord_7061997) baseStart_7061997 baseEnd_7061997 := by
    simpa [prefixWord, tailWord_7061997, baseEnd_7061997] using wordTrace_append hprefix tailTrace_7061997
  have hstable : (prefixWord ++ tailWord_7061997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7061997).length < 2 ^ (prefixWord ++ tailWord_7061997).sum := by decide
  have hdescent : baseEnd_7061997 < baseStart_7061997 := by decide
  rcases family_descends (prefixWord ++ tailWord_7061997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7062030 : List Nat := [4, 1, 1, 2, 3, 1, 1, 1, 1, 8]
def baseStart_7062030 : Nat := 118140960795 + 7062030 * 2 ^ 59
def prefixEnd_7062030 : Nat := 4983230072969 + 3 ^ 40 * 7062030 * 2
def baseEnd_7062030 : Nat := 1208738595490370002949107

theorem tailTrace_7062030 : CollatzResearch.WordTrace tailWord_7062030 prefixEnd_7062030 1208738595490370002949107 := by
  unfold tailWord_7062030
  simp only [CollatzResearch.WordTrace]
  refine ⟨32196674325684860443335943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 171715596403652589031125029 32196674325684860443335943)
  ·
    refine ⟨48295011488527290665003915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32196674325684860443335943 48295011488527290665003915)
    ·
      refine ⟨72442517232790935997505873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48295011488527290665003915 72442517232790935997505873)
      ·
        refine ⟨54331887924593201998129405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72442517232790935997505873 54331887924593201998129405)
        ·
          refine ⟨20374457971722450749298527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54331887924593201998129405 20374457971722450749298527)
          ·
            refine ⟨30561686957583676123947791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20374457971722450749298527 30561686957583676123947791)
            ·
              refine ⟨45842530436375514185921687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30561686957583676123947791 45842530436375514185921687)
              ·
                refine ⟨68763795654563271278882531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45842530436375514185921687 68763795654563271278882531)
                ·
                  refine ⟨103145693481844906918323797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68763795654563271278882531 103145693481844906918323797)
                  ·
                    refine ⟨1208738595490370002949107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 103145693481844906918323797 1208738595490370002949107)
                    ·
                      rfl

theorem cell23_7062030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 1, 1, 8].length) (baseStart_7062030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7062030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7062030 prefixEnd_7062030 := by exact prefixLift 7062030
  have htrace : WordTrace (prefixWord ++ tailWord_7062030) baseStart_7062030 baseEnd_7062030 := by
    simpa [prefixWord, tailWord_7062030, baseEnd_7062030] using wordTrace_append hprefix tailTrace_7062030
  have hstable : (prefixWord ++ tailWord_7062030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7062030).length < 2 ^ (prefixWord ++ tailWord_7062030).sum := by decide
  have hdescent : baseEnd_7062030 < baseStart_7062030 := by decide
  rcases family_descends (prefixWord ++ tailWord_7062030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7062050 : List Nat := [3, 3, 1, 1, 1, 1, 1, 1, 3, 4, 4]
def baseStart_7062050 : Nat := 118140960795 + 7062050 * 2 ^ 59
def prefixEnd_7062050 : Nat := 4983230072969 + 3 ^ 40 * 7062050 * 2
def baseEnd_7062050 : Nat := 3626226056084199930597229

theorem tailTrace_7062050 : CollatzResearch.WordTrace tailWord_7062050 prefixEnd_7062050 3626226056084199930597229 := by
  unfold tailWord_7062050
  simp only [CollatzResearch.WordTrace]
  refine ⟨64393531016351606740603901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171716082710270951308277069 64393531016351606740603901)
  ·
    refine ⟨24147574131131852527726463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64393531016351606740603901 24147574131131852527726463)
    ·
      refine ⟨36221361196697778791589695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24147574131131852527726463 36221361196697778791589695)
      ·
        refine ⟨54332041795046668187384543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36221361196697778791589695 54332041795046668187384543)
        ·
          refine ⟨81498062692570002281076815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54332041795046668187384543 81498062692570002281076815)
          ·
            refine ⟨122247094038855003421615223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81498062692570002281076815 122247094038855003421615223)
            ·
              refine ⟨183370641058282505132422835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122247094038855003421615223 183370641058282505132422835)
              ·
                refine ⟨275055961587423757698634253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 183370641058282505132422835 275055961587423757698634253)
                ·
                  refine ⟨103145985595283909136987845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 275055961587423757698634253 103145985595283909136987845)
                  ·
                    refine ⟨19339872299115732963185221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 103145985595283909136987845 19339872299115732963185221)
                    ·
                      refine ⟨3626226056084199930597229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19339872299115732963185221 3626226056084199930597229)
                      ·
                        rfl

theorem cell23_7062050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 1, 3, 4, 4].length) (baseStart_7062050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7062050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7062050 prefixEnd_7062050 := by exact prefixLift 7062050
  have htrace : WordTrace (prefixWord ++ tailWord_7062050) baseStart_7062050 baseEnd_7062050 := by
    simpa [prefixWord, tailWord_7062050, baseEnd_7062050] using wordTrace_append hprefix tailTrace_7062050
  have hstable : (prefixWord ++ tailWord_7062050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7062050).length < 2 ^ (prefixWord ++ tailWord_7062050).sum := by decide
  have hdescent : baseEnd_7062050 < baseStart_7062050 := by decide
  rcases family_descends (prefixWord ++ tailWord_7062050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7062058 : List Nat := [3, 1, 4, 1, 1, 4, 2, 1, 1, 3, 2]
def baseStart_7062058 : Nat := 118140960795 + 7062058 * 2 ^ 59
def prefixEnd_7062058 : Nat := 4983230072969 + 3 ^ 40 * 7062058 * 2
def baseEnd_7062058 : Nat := 3626230163929435899297193

theorem tailTrace_7062058 : CollatzResearch.WordTrace tailWord_7062058 prefixEnd_7062058 3626230163929435899297193 := by
  unfold tailWord_7062058
  simp only [CollatzResearch.WordTrace]
  refine ⟨64393603962344361082176707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171716277232918296219137885 64393603962344361082176707)
  ·
    refine ⟨96590405943516541623265061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64393603962344361082176707 96590405943516541623265061)
    ·
      refine ⟨18110701114409351554362199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 96590405943516541623265061 18110701114409351554362199)
      ·
        refine ⟨27166051671614027331543299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18110701114409351554362199 27166051671614027331543299)
        ·
          refine ⟨40749077507421040997314949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27166051671614027331543299 40749077507421040997314949)
          ·
            refine ⟨7640452032641445186996553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40749077507421040997314949 7640452032641445186996553)
            ·
              refine ⟨5730339024481083890247415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7640452032641445186996553 5730339024481083890247415)
              ·
                refine ⟨8595508536721625835371123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5730339024481083890247415 8595508536721625835371123)
                ·
                  refine ⟨12893262805082438753056685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8595508536721625835371123 12893262805082438753056685)
                  ·
                    refine ⟨4834973551905914532396257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12893262805082438753056685 4834973551905914532396257)
                    ·
                      refine ⟨3626230163929435899297193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4834973551905914532396257 3626230163929435899297193)
                      ·
                        rfl

theorem cell23_7062058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 2, 1, 1, 3, 2].length) (baseStart_7062058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7062058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7062058 prefixEnd_7062058 := by exact prefixLift 7062058
  have htrace : WordTrace (prefixWord ++ tailWord_7062058) baseStart_7062058 baseEnd_7062058 := by
    simpa [prefixWord, tailWord_7062058, baseEnd_7062058] using wordTrace_append hprefix tailTrace_7062058
  have hstable : (prefixWord ++ tailWord_7062058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7062058).length < 2 ^ (prefixWord ++ tailWord_7062058).sum := by decide
  have hdescent : baseEnd_7062058 < baseStart_7062058 := by decide
  rcases family_descends (prefixWord ++ tailWord_7062058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7062077 : List Nat := [1, 4, 1, 3, 2, 2, 2, 1, 7]
def baseStart_7062077 : Nat := 118140960795 + 7062077 * 2 ^ 59
def prefixEnd_7062077 : Nat := 4983230072969 + 3 ^ 40 * 7062077 * 2
def baseEnd_7062077 : Nat := 402915546673541258328845

theorem tailTrace_7062077 : CollatzResearch.WordTrace tailWord_7062077 prefixEnd_7062077 402915546673541258328845 := by
  unfold tailWord_7062077
  simp only [CollatzResearch.WordTrace]
  refine ⟨257575108836308610573648485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171716739224205740382432323 257575108836308610573648485)
  ·
    refine ⟨48295332906807864482559091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 257575108836308610573648485 48295332906807864482559091)
    ·
      refine ⟨72442999360211796723838637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48295332906807864482559091 72442999360211796723838637)
      ·
        refine ⟨27166124760079423771439489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72442999360211796723838637 27166124760079423771439489)
        ·
          refine ⟨20374593570059567828579617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27166124760079423771439489 20374593570059567828579617)
          ·
            refine ⟨15280945177544675871434713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20374593570059567828579617 15280945177544675871434713)
            ·
              refine ⟨11460708883158506903576035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15280945177544675871434713 11460708883158506903576035)
              ·
                refine ⟨17191063324737760355364053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11460708883158506903576035 17191063324737760355364053)
                ·
                  refine ⟨402915546673541258328845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17191063324737760355364053 402915546673541258328845)
                  ·
                    rfl

theorem cell23_7062077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 2, 1, 7].length) (baseStart_7062077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7062077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7062077 prefixEnd_7062077 := by exact prefixLift 7062077
  have htrace : WordTrace (prefixWord ++ tailWord_7062077) baseStart_7062077 baseEnd_7062077 := by
    simpa [prefixWord, tailWord_7062077, baseEnd_7062077] using wordTrace_append hprefix tailTrace_7062077
  have hstable : (prefixWord ++ tailWord_7062077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7062077).length < 2 ^ (prefixWord ++ tailWord_7062077).sum := by decide
  have hdescent : baseEnd_7062077 < baseStart_7062077 := by decide
  rcases family_descends (prefixWord ++ tailWord_7062077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7062087 : List Nat := [1, 1, 4, 1, 4, 1, 2, 1, 2, 3, 3]
def baseStart_7062087 : Nat := 118140960795 + 7062087 * 2 ^ 59
def prefixEnd_7062087 : Nat := 4983230072969 + 3 ^ 40 * 7062087 * 2
def baseEnd_7062087 : Nat := 3626245054868416285834559

theorem tailTrace_7062087 : CollatzResearch.WordTrace tailWord_7062087 prefixEnd_7062087 3626245054868416285834559 := by
  unfold tailWord_7062087
  simp only [CollatzResearch.WordTrace]
  refine ⟨257575473566272382281512515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171716982377514921521008343 257575473566272382281512515)
  ·
    refine ⟨386363210349408573422268773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257575473566272382281512515 386363210349408573422268773)
    ·
      refine ⟨72443101940514107516675395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 386363210349408573422268773 72443101940514107516675395)
      ·
        refine ⟨108664652910771161275013093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72443101940514107516675395 108664652910771161275013093)
        ·
          refine ⟨20374622420769592739064955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 108664652910771161275013093 20374622420769592739064955)
          ·
            refine ⟨30561933631154389108597433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20374622420769592739064955 30561933631154389108597433)
            ·
              refine ⟨22921450223365791831448075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30561933631154389108597433 22921450223365791831448075)
              ·
                refine ⟨34382175335048687747172113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22921450223365791831448075 34382175335048687747172113)
                ·
                  refine ⟨25786631501286515810379085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34382175335048687747172113 25786631501286515810379085)
                  ·
                    refine ⟨9669986812982443428892157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25786631501286515810379085 9669986812982443428892157)
                    ·
                      refine ⟨3626245054868416285834559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9669986812982443428892157 3626245054868416285834559)
                      ·
                        rfl

theorem cell23_7062087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 1, 2, 3, 3].length) (baseStart_7062087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7062087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7062087 prefixEnd_7062087 := by exact prefixLift 7062087
  have htrace : WordTrace (prefixWord ++ tailWord_7062087) baseStart_7062087 baseEnd_7062087 := by
    simpa [prefixWord, tailWord_7062087, baseEnd_7062087] using wordTrace_append hprefix tailTrace_7062087
  have hstable : (prefixWord ++ tailWord_7062087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7062087).length < 2 ^ (prefixWord ++ tailWord_7062087).sum := by decide
  have hdescent : baseEnd_7062087 < baseStart_7062087 := by decide
  rcases family_descends (prefixWord ++ tailWord_7062087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7062090 : List Nat := [3, 1, 2, 1, 1, 4, 1, 2, 1, 7]
def baseStart_7062090 : Nat := 118140960795 + 7062090 * 2 ^ 59
def prefixEnd_7062090 : Nat := 4983230072969 + 3 ^ 40 * 7062090 * 2
def baseEnd_7062090 : Nat := 1208748865103459924699015

theorem tailTrace_7062090 : CollatzResearch.WordTrace tailWord_7062090 prefixEnd_7062090 1208748865103459924699015 := by
  unfold tailWord_7062090
  simp only [CollatzResearch.WordTrace]
  refine ⟨64393895746315378448467931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171717055323507675862581149 64393895746315378448467931)
  ·
    refine ⟨96590843619473067672701897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64393895746315378448467931 96590843619473067672701897)
    ·
      refine ⟨72443132714604800754526423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96590843619473067672701897 72443132714604800754526423)
      ·
        refine ⟨108664699071907201131789635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72443132714604800754526423 108664699071907201131789635)
        ·
          refine ⟨162997048607860801697684453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108664699071907201131789635 162997048607860801697684453)
          ·
            refine ⟨30561946613973900318315835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 162997048607860801697684453 30561946613973900318315835)
            ·
              refine ⟨45842919920960850477473753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30561946613973900318315835 45842919920960850477473753)
              ·
                refine ⟨34382189940720637858105315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45842919920960850477473753 34382189940720637858105315)
                ·
                  refine ⟨51573284911080956787157973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34382189940720637858105315 51573284911080956787157973)
                  ·
                    refine ⟨1208748865103459924699015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51573284911080956787157973 1208748865103459924699015)
                    ·
                      rfl

theorem cell23_7062090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 2, 1, 7].length) (baseStart_7062090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7062090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7062090 prefixEnd_7062090 := by exact prefixLift 7062090
  have htrace : WordTrace (prefixWord ++ tailWord_7062090) baseStart_7062090 baseEnd_7062090 := by
    simpa [prefixWord, tailWord_7062090, baseEnd_7062090] using wordTrace_append hprefix tailTrace_7062090
  have hstable : (prefixWord ++ tailWord_7062090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7062090).length < 2 ^ (prefixWord ++ tailWord_7062090).sum := by decide
  have hdescent : baseEnd_7062090 < baseStart_7062090 := by decide
  rcases family_descends (prefixWord ++ tailWord_7062090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7062127 : List Nat := [1, 1, 2, 1, 3, 2, 2, 1, 4, 4, 2]
def baseStart_7062127 : Nat := 118140960795 + 7062127 * 2 ^ 59
def prefixEnd_7062127 : Nat := 4983230072969 + 3 ^ 40 * 7062127 * 2
def baseEnd_7062127 : Nat := 3626265594094596129334375

theorem tailTrace_7062127 : CollatzResearch.WordTrace tailWord_7062127 prefixEnd_7062127 3626265594094596129334375 := by
  unfold tailWord_7062127
  simp only [CollatzResearch.WordTrace]
  refine ⟨257576932486127469112968635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171717954990751646075312423 257576932486127469112968635)
  ·
    refine ⟨386365398729191203669452953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257576932486127469112968635 386365398729191203669452953)
    ·
      refine ⟨289774049046893402752089715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 386365398729191203669452953 289774049046893402752089715)
      ·
        refine ⟨434661073570340104128134573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 289774049046893402752089715 434661073570340104128134573)
        ·
          refine ⟨162997902588877539048050465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 434661073570340104128134573 162997902588877539048050465)
          ·
            refine ⟨122248426941658154286037849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162997902588877539048050465 122248426941658154286037849)
            ·
              refine ⟨91686320206243615714528387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122248426941658154286037849 91686320206243615714528387)
              ·
                refine ⟨137529480309365423571792581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91686320206243615714528387 137529480309365423571792581)
                ·
                  refine ⟨25786777558006016919711109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 137529480309365423571792581 25786777558006016919711109)
                  ·
                    refine ⟨4835020792126128172445833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25786777558006016919711109 4835020792126128172445833)
                    ·
                      refine ⟨3626265594094596129334375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4835020792126128172445833 3626265594094596129334375)
                      ·
                        rfl

theorem cell23_7062127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 1, 4, 4, 2].length) (baseStart_7062127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7062127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7062127 prefixEnd_7062127 := by exact prefixLift 7062127
  have htrace : WordTrace (prefixWord ++ tailWord_7062127) baseStart_7062127 baseEnd_7062127 := by
    simpa [prefixWord, tailWord_7062127, baseEnd_7062127] using wordTrace_append hprefix tailTrace_7062127
  have hstable : (prefixWord ++ tailWord_7062127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7062127).length < 2 ^ (prefixWord ++ tailWord_7062127).sum := by decide
  have hdescent : baseEnd_7062127 < baseStart_7062127 := by decide
  rcases family_descends (prefixWord ++ tailWord_7062127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7062134 : List Nat := [5, 1, 1, 2, 3, 1, 1, 1, 1, 2, 5]
def baseStart_7062134 : Nat := 118140960795 + 7062134 * 2 ^ 59
def prefixEnd_7062134 : Nat := 4983230072969 + 3 ^ 40 * 7062134 * 2
def baseEnd_7062134 : Nat := 3626269188459177601946843

theorem tailTrace_7062134 : CollatzResearch.WordTrace tailWord_7062134 prefixEnd_7062134 3626269188459177601946843 := by
  unfold tailWord_7062134
  simp only [CollatzResearch.WordTrace]
  refine ⟨16098574237318881831779591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 171718125198068072872315637 16098574237318881831779591)
  ·
    refine ⟨24147861355978322747669387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16098574237318881831779591 24147861355978322747669387)
    ·
      refine ⟨36221792033967484121504081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24147861355978322747669387 36221792033967484121504081)
      ·
        refine ⟨27166344025475613091128061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36221792033967484121504081 27166344025475613091128061)
        ·
          refine ⟨10187379009553354909173023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27166344025475613091128061 10187379009553354909173023)
          ·
            refine ⟨15281068514330032363759535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10187379009553354909173023 15281068514330032363759535)
            ·
              refine ⟨22921602771495048545639303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15281068514330032363759535 22921602771495048545639303)
              ·
                refine ⟨34382404157242572818458955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22921602771495048545639303 34382404157242572818458955)
                ·
                  refine ⟨51573606235863859227688433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34382404157242572818458955 51573606235863859227688433)
                  ·
                    refine ⟨38680204676897894420766325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51573606235863859227688433 38680204676897894420766325)
                    ·
                      refine ⟨3626269188459177601946843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38680204676897894420766325 3626269188459177601946843)
                      ·
                        rfl

theorem cell23_7062134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 1, 1, 2, 5].length) (baseStart_7062134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7062134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7062134 prefixEnd_7062134 := by exact prefixLift 7062134
  have htrace : WordTrace (prefixWord ++ tailWord_7062134) baseStart_7062134 baseEnd_7062134 := by
    simpa [prefixWord, tailWord_7062134, baseEnd_7062134] using wordTrace_append hprefix tailTrace_7062134
  have hstable : (prefixWord ++ tailWord_7062134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7062134).length < 2 ^ (prefixWord ++ tailWord_7062134).sum := by decide
  have hdescent : baseEnd_7062134 < baseStart_7062134 := by decide
  rcases family_descends (prefixWord ++ tailWord_7062134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7062140 : List Nat := [2, 2, 2, 1, 1, 2, 2, 2, 2, 1, 6]
def baseStart_7062140 : Nat := 118140960795 + 7062140 * 2 ^ 59
def prefixEnd_7062140 : Nat := 4983230072969 + 3 ^ 40 * 7062140 * 2
def baseEnd_7062140 : Nat := 3626272269343104578471815

theorem tailTrace_7062140 : CollatzResearch.WordTrace tailWord_7062140 prefixEnd_7062140 3626272269343104578471815 := by
  unfold tailWord_7062140
  simp only [CollatzResearch.WordTrace]
  refine ⟨128788703317540186166595937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171718271090053581555461249 128788703317540186166595937)
  ·
    refine ⟨96591527488155139624946953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128788703317540186166595937 96591527488155139624946953)
    ·
      refine ⟨72443645616116354718710215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96591527488155139624946953 72443645616116354718710215)
      ·
        refine ⟨108665468424174532078065323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72443645616116354718710215 108665468424174532078065323)
        ·
          refine ⟨162998202636261798117097985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108665468424174532078065323 162998202636261798117097985)
          ·
            refine ⟨122248651977196348587823489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162998202636261798117097985 122248651977196348587823489)
            ·
              refine ⟨91686488982897261440867617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122248651977196348587823489 91686488982897261440867617)
              ·
                refine ⟨68764866737172946080650713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91686488982897261440867617 68764866737172946080650713)
                ·
                  refine ⟨51573650052879709560488035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68764866737172946080650713 51573650052879709560488035)
                  ·
                    refine ⟨77360475079319564340732053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51573650052879709560488035 77360475079319564340732053)
                    ·
                      refine ⟨3626272269343104578471815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 77360475079319564340732053 3626272269343104578471815)
                      ·
                        rfl

theorem cell23_7062140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 2, 2, 1, 6].length) (baseStart_7062140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7062140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7062140 prefixEnd_7062140 := by exact prefixLift 7062140
  have htrace : WordTrace (prefixWord ++ tailWord_7062140) baseStart_7062140 baseEnd_7062140 := by
    simpa [prefixWord, tailWord_7062140, baseEnd_7062140] using wordTrace_append hprefix tailTrace_7062140
  have hstable : (prefixWord ++ tailWord_7062140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7062140).length < 2 ^ (prefixWord ++ tailWord_7062140).sum := by decide
  have hdescent : baseEnd_7062140 < baseStart_7062140 := by decide
  rcases family_descends (prefixWord ++ tailWord_7062140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7062194 : List Nat := [3, 2, 1, 1, 1, 2, 1, 5, 3, 1, 3]
def baseStart_7062194 : Nat := 118140960795 + 7062194 * 2 ^ 59
def prefixEnd_7062194 : Nat := 4983230072969 + 3 ^ 40 * 7062194 * 2
def baseEnd_7062194 : Nat := 3626299997298447367196567

theorem tailTrace_7062194 : CollatzResearch.WordTrace tailWord_7062194 prefixEnd_7062194 3626299997298447367196567 := by
  unfold tailWord_7062194
  simp only [CollatzResearch.WordTrace]
  refine ⟨64394844044221184888914409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171719584117923159703771757 64394844044221184888914409)
  ·
    refine ⟨48296133033165888666685807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64394844044221184888914409 48296133033165888666685807)
    ·
      refine ⟨72444199549748833000028711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48296133033165888666685807 72444199549748833000028711)
      ·
        refine ⟨108666299324623249500043067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72444199549748833000028711 108666299324623249500043067)
        ·
          refine ⟨162999448986934874250064601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108666299324623249500043067 162999448986934874250064601)
          ·
            refine ⟨122249586740201155687548451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162999448986934874250064601 122249586740201155687548451)
            ·
              refine ⟨183374380110301733531322677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122249586740201155687548451 183374380110301733531322677)
              ·
                refine ⟨17191348135340787518561501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 183374380110301733531322677 17191348135340787518561501)
                ·
                  refine ⟨6446755550752795319460563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17191348135340787518561501 6446755550752795319460563)
                  ·
                    refine ⟨9670133326129192979190845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6446755550752795319460563 9670133326129192979190845)
                    ·
                      refine ⟨3626299997298447367196567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9670133326129192979190845 3626299997298447367196567)
                      ·
                        rfl

theorem cell23_7062194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 5, 3, 1, 3].length) (baseStart_7062194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7062194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7062194 prefixEnd_7062194 := by exact prefixLift 7062194
  have htrace : WordTrace (prefixWord ++ tailWord_7062194) baseStart_7062194 baseEnd_7062194 := by
    simpa [prefixWord, tailWord_7062194, baseEnd_7062194] using wordTrace_append hprefix tailTrace_7062194
  have hstable : (prefixWord ++ tailWord_7062194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7062194).length < 2 ^ (prefixWord ++ tailWord_7062194).sum := by decide
  have hdescent : baseEnd_7062194 < baseStart_7062194 := by decide
  rcases family_descends (prefixWord ++ tailWord_7062194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7062204 : List Nat := [2, 2, 2, 3, 1, 1, 2, 2, 1, 5, 2]
def baseStart_7062204 : Nat := 118140960795 + 7062204 * 2 ^ 59
def prefixEnd_7062204 : Nat := 4983230072969 + 3 ^ 40 * 7062204 * 2
def baseEnd_7062204 : Nat := 3626305132104992328071521

theorem tailTrace_7062204 : CollatzResearch.WordTrace tailWord_7062204 prefixEnd_7062204 3626305132104992328071521 := by
  unfold tailWord_7062204
  simp only [CollatzResearch.WordTrace]
  refine ⟨128789870453424255631760833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171719827271232340842347777 128789870453424255631760833)
  ·
    refine ⟨96592402840068191723820625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128789870453424255631760833 96592402840068191723820625)
    ·
      refine ⟨72444302130051143792865469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96592402840068191723820625 72444302130051143792865469)
      ·
        refine ⟨27166613298769178922324551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72444302130051143792865469 27166613298769178922324551)
        ·
          refine ⟨40749919948153768383486827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27166613298769178922324551 40749919948153768383486827)
          ·
            refine ⟨61124879922230652575230241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40749919948153768383486827 61124879922230652575230241)
            ·
              refine ⟨45843659941672989431422681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61124879922230652575230241 45843659941672989431422681)
              ·
                refine ⟨34382744956254742073567011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45843659941672989431422681 34382744956254742073567011)
                ·
                  refine ⟨51574117434382113110350517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34382744956254742073567011 51574117434382113110350517)
                  ·
                    refine ⟨4835073509473323104095361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51574117434382113110350517 4835073509473323104095361)
                    ·
                      refine ⟨3626305132104992328071521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4835073509473323104095361 3626305132104992328071521)
                      ·
                        rfl

theorem cell23_7062204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 2, 1, 5, 2].length) (baseStart_7062204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7062204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7062204 prefixEnd_7062204 := by exact prefixLift 7062204
  have htrace : WordTrace (prefixWord ++ tailWord_7062204) baseStart_7062204 baseEnd_7062204 := by
    simpa [prefixWord, tailWord_7062204, baseEnd_7062204] using wordTrace_append hprefix tailTrace_7062204
  have hstable : (prefixWord ++ tailWord_7062204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7062204).length < 2 ^ (prefixWord ++ tailWord_7062204).sum := by decide
  have hdescent : baseEnd_7062204 < baseStart_7062204 := by decide
  rcases family_descends (prefixWord ++ tailWord_7062204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7062231 : List Nat := [1, 1, 3, 2, 1, 6, 2, 1, 1, 5]
def baseStart_7062231 : Nat := 118140960795 + 7062231 * 2 ^ 59
def prefixEnd_7062231 : Nat := 4983230072969 + 3 ^ 40 * 7062231 * 2
def baseEnd_7062231 : Nat := 1208772998694221240811299

theorem tailTrace_7062231 : CollatzResearch.WordTrace tailWord_7062231 prefixEnd_7062231 1208772998694221240811299 := by
  unfold tailWord_7062231
  simp only [CollatzResearch.WordTrace]
  refine ⟨257580725677750694874754547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171720483785167129916503031 257580725677750694874754547)
  ·
    refine ⟨386371088516626042312131821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257580725677750694874754547 386371088516626042312131821)
    ·
      refine ⟨144889158193734765867049433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 386371088516626042312131821 144889158193734765867049433)
      ·
        refine ⟨108666868645301074400287075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144889158193734765867049433 108666868645301074400287075)
        ·
          refine ⟨163000302967951611600430613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108666868645301074400287075 163000302967951611600430613)
          ·
            refine ⟨7640639201622731793770185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 163000302967951611600430613 7640639201622731793770185)
            ·
              refine ⟨5730479401217048845327639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7640639201622731793770185 5730479401217048845327639)
              ·
                refine ⟨8595719101825573267991459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5730479401217048845327639 8595719101825573267991459)
                ·
                  refine ⟨12893578652738359901987189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8595719101825573267991459 12893578652738359901987189)
                  ·
                    refine ⟨1208772998694221240811299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12893578652738359901987189 1208772998694221240811299)
                    ·
                      rfl

theorem cell23_7062231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 2, 1, 1, 5].length) (baseStart_7062231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7062231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7062231 prefixEnd_7062231 := by exact prefixLift 7062231
  have htrace : WordTrace (prefixWord ++ tailWord_7062231) baseStart_7062231 baseEnd_7062231 := by
    simpa [prefixWord, tailWord_7062231, baseEnd_7062231] using wordTrace_append hprefix tailTrace_7062231
  have hstable : (prefixWord ++ tailWord_7062231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7062231).length < 2 ^ (prefixWord ++ tailWord_7062231).sum := by decide
  have hdescent : baseEnd_7062231 < baseStart_7062231 := by decide
  rcases family_descends (prefixWord ++ tailWord_7062231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7062234 : List Nat := [3, 1, 1, 2, 2, 2, 3, 3, 1, 1, 4]
def baseStart_7062234 : Nat := 118140960795 + 7062234 * 2 ^ 59
def prefixEnd_7062234 : Nat := 4983230072969 + 3 ^ 40 * 7062234 * 2
def baseEnd_7062234 : Nat := 3626320536524627210696383

theorem tailTrace_7062234 : CollatzResearch.WordTrace tailWord_7062234 prefixEnd_7062234 3626320536524627210696383 := by
  unfold tailWord_7062234
  simp only [CollatzResearch.WordTrace]
  refine ⟨64395208774184956596778439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171720556731159884258075837 64395208774184956596778439)
  ·
    refine ⟨96592813161277434895167659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64395208774184956596778439 96592813161277434895167659)
    ·
      refine ⟨144889219741916152342751489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96592813161277434895167659 144889219741916152342751489)
      ·
        refine ⟨108666914806437114257063617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144889219741916152342751489 108666914806437114257063617)
        ·
          refine ⟨81500186104827835692797713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108666914806437114257063617 81500186104827835692797713)
          ·
            refine ⟨61125139578620876769598285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81500186104827835692797713 61125139578620876769598285)
            ·
              refine ⟨22921927341982828788599357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61125139578620876769598285 22921927341982828788599357)
              ·
                refine ⟨8595722753243560795724759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22921927341982828788599357 8595722753243560795724759)
                ·
                  refine ⟨12893584129865341193587139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8595722753243560795724759 12893584129865341193587139)
                  ·
                    refine ⟨19340376194798011790380709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12893584129865341193587139 19340376194798011790380709)
                    ·
                      refine ⟨3626320536524627210696383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19340376194798011790380709 3626320536524627210696383)
                      ·
                        rfl

theorem cell23_7062234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 3, 1, 1, 4].length) (baseStart_7062234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7062234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7062234 prefixEnd_7062234 := by exact prefixLift 7062234
  have htrace : WordTrace (prefixWord ++ tailWord_7062234) baseStart_7062234 baseEnd_7062234 := by
    simpa [prefixWord, tailWord_7062234, baseEnd_7062234] using wordTrace_append hprefix tailTrace_7062234
  have hstable : (prefixWord ++ tailWord_7062234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7062234).length < 2 ^ (prefixWord ++ tailWord_7062234).sum := by decide
  have hdescent : baseEnd_7062234 < baseStart_7062234 := by decide
  rcases family_descends (prefixWord ++ tailWord_7062234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7062244 : List Nat := [2, 3, 1, 1, 1, 5, 1, 1, 4, 4]
def baseStart_7062244 : Nat := 118140960795 + 7062244 * 2 ^ 59
def prefixEnd_7062244 : Nat := 4983230072969 + 3 ^ 40 * 7062244 * 2
def baseEnd_7062244 : Nat := 1208775223777057390523779

theorem tailTrace_7062244 : CollatzResearch.WordTrace tailWord_7062244 prefixEnd_7062244 1208775223777057390523779 := by
  unfold tailWord_7062244
  simp only [CollatzResearch.WordTrace]
  refine ⟨128790599913351799047488893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171720799884469065396651857 128790599913351799047488893)
  ·
    refine ⟨48296474967506924642808335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128790599913351799047488893 48296474967506924642808335)
    ·
      refine ⟨72444712451260386964212503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48296474967506924642808335 72444712451260386964212503)
      ·
        refine ⟨108667068676890580446318755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72444712451260386964212503 108667068676890580446318755)
        ·
          refine ⟨163000603015335870669478133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108667068676890580446318755 163000603015335870669478133)
          ·
            refine ⟨15281306532687737875263575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 163000603015335870669478133 15281306532687737875263575)
            ·
              refine ⟨22921959799031606812895363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15281306532687737875263575 22921959799031606812895363)
              ·
                refine ⟨34382939698547410219343045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22921959799031606812895363 34382939698547410219343045)
                ·
                  refine ⟨6446801193477639416126821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34382939698547410219343045 6446801193477639416126821)
                  ·
                    refine ⟨1208775223777057390523779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6446801193477639416126821 1208775223777057390523779)
                    ·
                      rfl

theorem cell23_7062244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 1, 4, 4].length) (baseStart_7062244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7062244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7062244 prefixEnd_7062244 := by exact prefixLift 7062244
  have htrace : WordTrace (prefixWord ++ tailWord_7062244) baseStart_7062244 baseEnd_7062244 := by
    simpa [prefixWord, tailWord_7062244, baseEnd_7062244] using wordTrace_append hprefix tailTrace_7062244
  have hstable : (prefixWord ++ tailWord_7062244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7062244).length < 2 ^ (prefixWord ++ tailWord_7062244).sum := by decide
  have hdescent : baseEnd_7062244 < baseStart_7062244 := by decide
  rcases family_descends (prefixWord ++ tailWord_7062244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7062254 : List Nat := [4, 1, 2, 1, 1, 4, 1, 2, 1, 1, 5]
def baseStart_7062254 : Nat := 118140960795 + 7062254 * 2 ^ 59
def prefixEnd_7062254 : Nat := 4983230072969 + 3 ^ 40 * 7062254 * 2
def baseEnd_7062254 : Nat := 3626330806137717132446291

theorem tailTrace_7062254 : CollatzResearch.WordTrace tailWord_7062254 prefixEnd_7062254 3626330806137717132446291 := by
  unfold tailWord_7062254
  simp only [CollatzResearch.WordTrace]
  refine ⟨32197695569583421225355227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 171721043037778246535227877 32197695569583421225355227)
  ·
    refine ⟨48296543354375131838032841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32197695569583421225355227 48296543354375131838032841)
    ·
      refine ⟨36222407515781348878524631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48296543354375131838032841 36222407515781348878524631)
      ·
        refine ⟨54333611273672023317786947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36222407515781348878524631 54333611273672023317786947)
        ·
          refine ⟨81500416910508034976680421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54333611273672023317786947 81500416910508034976680421)
          ·
            refine ⟨15281328170720256558127579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 81500416910508034976680421 15281328170720256558127579)
            ·
              refine ⟨22921992256080384837191369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15281328170720256558127579 22921992256080384837191369)
              ·
                refine ⟨17191494192060288627893527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22921992256080384837191369 17191494192060288627893527)
                ·
                  refine ⟨25787241288090432941840291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17191494192060288627893527 25787241288090432941840291)
                  ·
                    refine ⟨38680861932135649412760437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25787241288090432941840291 38680861932135649412760437)
                    ·
                      refine ⟨3626330806137717132446291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38680861932135649412760437 3626330806137717132446291)
                      ·
                        rfl

theorem cell23_7062254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 2, 1, 1, 5].length) (baseStart_7062254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7062254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7062254 prefixEnd_7062254 := by exact prefixLift 7062254
  have htrace : WordTrace (prefixWord ++ tailWord_7062254) baseStart_7062254 baseEnd_7062254 := by
    simpa [prefixWord, tailWord_7062254, baseEnd_7062254] using wordTrace_append hprefix tailTrace_7062254
  have hstable : (prefixWord ++ tailWord_7062254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7062254).length < 2 ^ (prefixWord ++ tailWord_7062254).sum := by decide
  have hdescent : baseEnd_7062254 < baseStart_7062254 := by decide
  rcases family_descends (prefixWord ++ tailWord_7062254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7062274 : List Nat := [3, 4, 1, 1, 1, 3, 1, 9]
def baseStart_7062274 : Nat := 118140960795 + 7062274 * 2 ^ 59
def prefixEnd_7062274 : Nat := 4983230072969 + 3 ^ 40 * 7062274 * 2
def baseEnd_7062274 : Nat := 134308928731511372377637

theorem tailTrace_7062274 : CollatzResearch.WordTrace tailWord_7062274 prefixEnd_7062274 134308928731511372377637 := by
  unfold tailWord_7062274
  simp only [CollatzResearch.WordTrace]
  refine ⟨64395573504148728304642469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171721529344396608812379917 64395573504148728304642469)
  ·
    refine ⟨12074170032027886557120463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64395573504148728304642469 12074170032027886557120463)
    ·
      refine ⟨18111255048041829835680695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12074170032027886557120463 18111255048041829835680695)
      ·
        refine ⟨27166882572062744753521043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18111255048041829835680695 27166882572062744753521043)
        ·
          refine ⟨40750323858094117130281565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27166882572062744753521043 40750323858094117130281565)
          ·
            refine ⟨15281371446785293923855587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40750323858094117130281565 15281371446785293923855587)
            ·
              refine ⟨22922057170177940885783381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15281371446785293923855587 22922057170177940885783381)
              ·
                refine ⟨134308928731511372377637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 22922057170177940885783381 134308928731511372377637)
                ·
                  rfl

theorem cell23_7062274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 9].length) (baseStart_7062274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7062274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7062274 prefixEnd_7062274 := by exact prefixLift 7062274
  have htrace : WordTrace (prefixWord ++ tailWord_7062274) baseStart_7062274 baseEnd_7062274 := by
    simpa [prefixWord, tailWord_7062274, baseEnd_7062274] using wordTrace_append hprefix tailTrace_7062274
  have hstable : (prefixWord ++ tailWord_7062274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7062274).length < 2 ^ (prefixWord ++ tailWord_7062274).sum := by decide
  have hdescent : baseEnd_7062274 < baseStart_7062274 := by decide
  rcases family_descends (prefixWord ++ tailWord_7062274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7062307 : List Nat := [1, 1, 1, 4, 2, 1, 1, 3, 2, 3, 4]
def baseStart_7062307 : Nat := 118140960795 + 7062307 * 2 ^ 59
def prefixEnd_7062307 : Nat := 4983230072969 + 3 ^ 40 * 7062307 * 2
def baseEnd_7062307 : Nat := 3626358020612405425083547

theorem tailTrace_7062307 : CollatzResearch.WordTrace tailWord_7062307 prefixEnd_7062307 3626358020612405425083547 := by
  unfold tailWord_7062307
  simp only [CollatzResearch.WordTrace]
  refine ⟨257583497625475359854521175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171722331750316906569680783 257583497625475359854521175)
  ·
    refine ⟨386375246438213039781781763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257583497625475359854521175 386375246438213039781781763)
    ·
      refine ⟨579562869657319559672672645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 386375246438213039781781763 579562869657319559672672645)
      ·
        refine ⟨108668038060747417438626121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 579562869657319559672672645 108668038060747417438626121)
        ·
          refine ⟨81501028545560563078969591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108668038060747417438626121 81501028545560563078969591)
          ·
            refine ⟨122251542818340844618454387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81501028545560563078969591 122251542818340844618454387)
            ·
              refine ⟨183377314227511266927681581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122251542818340844618454387 183377314227511266927681581)
              ·
                refine ⟨68766492835316725097880593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 183377314227511266927681581 68766492835316725097880593)
                ·
                  refine ⟨51574869626487543823410445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68766492835316725097880593 51574869626487543823410445)
                  ·
                    refine ⟨19340576109932828933778917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51574869626487543823410445 19340576109932828933778917)
                    ·
                      refine ⟨3626358020612405425083547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19340576109932828933778917 3626358020612405425083547)
                      ·
                        rfl

theorem cell23_7062307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 3, 2, 3, 4].length) (baseStart_7062307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7062307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7062307 prefixEnd_7062307 := by exact prefixLift 7062307
  have htrace : WordTrace (prefixWord ++ tailWord_7062307) baseStart_7062307 baseEnd_7062307 := by
    simpa [prefixWord, tailWord_7062307, baseEnd_7062307] using wordTrace_append hprefix tailTrace_7062307
  have hstable : (prefixWord ++ tailWord_7062307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7062307).length < 2 ^ (prefixWord ++ tailWord_7062307).sum := by decide
  have hdescent : baseEnd_7062307 < baseStart_7062307 := by decide
  rcases family_descends (prefixWord ++ tailWord_7062307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
