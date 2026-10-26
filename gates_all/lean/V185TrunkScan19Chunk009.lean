import V185TrunkScan19Chunk008

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental

namespace V185TrunkScan19Incremental

def tailWord_90762 : List Nat := [3, 1, 2, 3, 3, 7]
def baseStart_90762 : Nat := 118140960795 + 90762 * 2 ^ 59
def prefixEnd_90762 : Nat := 4983230072969 + 3 ^ 40 * 90762 * 2
def baseEnd_90762 : Nat := 3068611105414263503381

theorem tailTrace_90762 : CollatzResearch.WordTrace tailWord_90762 prefixEnd_90762 3068611105414263503381 := by
  unfold tailWord_90762
  simp only [CollatzResearch.WordTrace]
  refine ⟨827590524298062440154635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2206908064794833173745693 827590524298062440154635)
  ·
    refine ⟨1241385786447093660231953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 827590524298062440154635 1241385786447093660231953)
    ·
      refine ⟨931039339835320245173965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1241385786447093660231953 931039339835320245173965)
      ·
        refine ⟨349139752438245091940237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 931039339835320245173965 349139752438245091940237)
        ·
          refine ⟨130927407164341909477589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 349139752438245091940237 130927407164341909477589)
          ·
            refine ⟨3068611105414263503381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 130927407164341909477589 3068611105414263503381)
            ·
              rfl

theorem cell19_90762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 7].length) (baseStart_90762 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_90762 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_90762 prefixEnd_90762 := by exact prefixLift 90762
  have htrace : WordTrace (prefixWord ++ tailWord_90762) baseStart_90762 baseEnd_90762 := by
    simpa [prefixWord, tailWord_90762, baseEnd_90762] using wordTrace_append hprefix tailTrace_90762
  have hstable : (prefixWord ++ tailWord_90762).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90762).length < 2 ^ (prefixWord ++ tailWord_90762).sum := by decide
  have hdescent : baseEnd_90762 < baseStart_90762 := by decide
  rcases family_descends (prefixWord ++ tailWord_90762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90781 : List Nat := [1, 4, 2, 1, 1, 1, 5, 4]
def baseStart_90781 : Nat := 118140960795 + 90781 * 2 ^ 59
def prefixEnd_90781 : Nat := 4983230072969 + 3 ^ 40 * 90781 * 2
def baseEnd_90781 : Nat := 27623281360541957108155

theorem tailTrace_90781 : CollatzResearch.WordTrace tailWord_90781 prefixEnd_90781 27623281360541957108155 := by
  unfold tailWord_90781
  simp only [CollatzResearch.WordTrace]
  refine ⟨3311055084123416005560197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2207370056082277337040131 3311055084123416005560197)
  ·
    refine ⟨620822828273140501042537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3311055084123416005560197 620822828273140501042537)
    ·
      refine ⟨465617121204855375781903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 620822828273140501042537 465617121204855375781903)
      ·
        refine ⟨698425681807283063672855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 465617121204855375781903 698425681807283063672855)
        ·
          refine ⟨1047638522710924595509283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 698425681807283063672855 1047638522710924595509283)
          ·
            refine ⟨1571457784066386893263925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1047638522710924595509283 1571457784066386893263925)
            ·
              refine ⟨147324167256223771243493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1571457784066386893263925 147324167256223771243493)
              ·
                refine ⟨27623281360541957108155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 147324167256223771243493 27623281360541957108155)
                ·
                  rfl

theorem cell19_90781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 5, 4].length) (baseStart_90781 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_90781 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_90781 prefixEnd_90781 := by exact prefixLift 90781
  have htrace : WordTrace (prefixWord ++ tailWord_90781) baseStart_90781 baseEnd_90781 := by
    simpa [prefixWord, tailWord_90781, baseEnd_90781] using wordTrace_append hprefix tailTrace_90781
  have hstable : (prefixWord ++ tailWord_90781).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90781).length < 2 ^ (prefixWord ++ tailWord_90781).sum := by decide
  have hdescent : baseEnd_90781 < baseStart_90781 := by decide
  rcases family_descends (prefixWord ++ tailWord_90781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90794 : List Nat := [3, 1, 5, 2, 1, 1, 3, 3]
def baseStart_90794 : Nat := 118140960795 + 90794 * 2 ^ 59
def prefixEnd_90794 : Nat := 4983230072969 + 3 ^ 40 * 90794 * 2
def baseEnd_90794 : Nat := 27627237063361778819231

theorem tailTrace_90794 : CollatzResearch.WordTrace tailWord_90794 prefixEnd_90794 27627237063361778819231 := by
  unfold tailWord_90794
  simp only [CollatzResearch.WordTrace]
  refine ⟨827882308269079806445859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2207686155384212817188957 827882308269079806445859)
  ·
    refine ⟨1241823462403619709668789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 827882308269079806445859 1241823462403619709668789)
    ·
      refine ⟨116420949600339347781449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1241823462403619709668789 116420949600339347781449)
      ·
        refine ⟨87315712200254510836087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116420949600339347781449 87315712200254510836087)
        ·
          refine ⟨130973568300381766254131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87315712200254510836087 130973568300381766254131)
          ·
            refine ⟨196460352450572649381197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130973568300381766254131 196460352450572649381197)
            ·
              refine ⟨73672632168964743517949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 196460352450572649381197 73672632168964743517949)
              ·
                refine ⟨27627237063361778819231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73672632168964743517949 27627237063361778819231)
                ·
                  rfl

theorem cell19_90794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 3, 3].length) (baseStart_90794 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_90794 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_90794 prefixEnd_90794 := by exact prefixLift 90794
  have htrace : WordTrace (prefixWord ++ tailWord_90794) baseStart_90794 baseEnd_90794 := by
    simpa [prefixWord, tailWord_90794, baseEnd_90794] using wordTrace_append hprefix tailTrace_90794
  have hstable : (prefixWord ++ tailWord_90794).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90794).length < 2 ^ (prefixWord ++ tailWord_90794).sum := by decide
  have hdescent : baseEnd_90794 < baseStart_90794 := by decide
  rcases family_descends (prefixWord ++ tailWord_90794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90857 : List Nat := [1, 2, 1, 1, 1, 2, 8, 3]
def baseStart_90857 : Nat := 118140960795 + 90857 * 2 ^ 59
def prefixEnd_90857 : Nat := 4983230072969 + 3 ^ 40 * 90857 * 2
def baseEnd_90857 : Nat := 27646407007796299419059

theorem tailTrace_90857 : CollatzResearch.WordTrace tailWord_90857 prefixEnd_90857 27646407007796299419059 := by
  unfold tailWord_90857
  simp only [CollatzResearch.WordTrace]
  refine ⟨3313827031848080985326825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2209218021232053990217883 3313827031848080985326825)
  ·
    refine ⟨2485370273886060738995119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3313827031848080985326825 2485370273886060738995119)
    ·
      refine ⟨3728055410829091108492679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2485370273886060738995119 3728055410829091108492679)
      ·
        refine ⟨5592083116243636662739019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3728055410829091108492679 5592083116243636662739019)
        ·
          refine ⟨8388124674365454994108529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5592083116243636662739019 8388124674365454994108529)
          ·
            refine ⟨6291093505774091245581397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8388124674365454994108529 6291093505774091245581397)
            ·
              refine ⟨73723752020790131784157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 6291093505774091245581397 73723752020790131784157)
              ·
                refine ⟨27646407007796299419059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73723752020790131784157 27646407007796299419059)
                ·
                  rfl

theorem cell19_90857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 8, 3].length) (baseStart_90857 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_90857 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_90857 prefixEnd_90857 := by exact prefixLift 90857
  have htrace : WordTrace (prefixWord ++ tailWord_90857) baseStart_90857 baseEnd_90857 := by
    simpa [prefixWord, tailWord_90857, baseEnd_90857] using wordTrace_append hprefix tailTrace_90857
  have hstable : (prefixWord ++ tailWord_90857).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90857).length < 2 ^ (prefixWord ++ tailWord_90857).sum := by decide
  have hdescent : baseEnd_90857 < baseStart_90857 := by decide
  rcases family_descends (prefixWord ++ tailWord_90857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90876 : List Nat := [2, 2, 2, 1, 3, 4, 5]
def baseStart_90876 : Nat := 118140960795 + 90876 * 2 ^ 59
def prefixEnd_90876 : Nat := 4983230072969 + 3 ^ 40 * 90876 * 2
def baseEnd_90876 : Nat := 9217396139869961665595

theorem tailTrace_90876 : CollatzResearch.WordTrace tailWord_90876 prefixEnd_90876 9217396139869961665595 := by
  unfold tailWord_90876
  simp only [CollatzResearch.WordTrace]
  refine ⟨1657260009389623615134241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2209680012519498153512321 1657260009389623615134241)
  ·
    refine ⟨1242945007042217711350681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1657260009389623615134241 1242945007042217711350681)
    ·
      refine ⟨932208755281663283513011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1242945007042217711350681 932208755281663283513011)
      ·
        refine ⟨1398313132922494925269517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 932208755281663283513011 1398313132922494925269517)
        ·
          refine ⟨524367424845935596976069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1398313132922494925269517 524367424845935596976069)
          ·
            refine ⟨98318892158612924433013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 524367424845935596976069 98318892158612924433013)
            ·
              refine ⟨9217396139869961665595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 98318892158612924433013 9217396139869961665595)
              ·
                rfl

theorem cell19_90876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 5].length) (baseStart_90876 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_90876 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_90876 prefixEnd_90876 := by exact prefixLift 90876
  have htrace : WordTrace (prefixWord ++ tailWord_90876) baseStart_90876 baseEnd_90876 := by
    simpa [prefixWord, tailWord_90876, baseEnd_90876] using wordTrace_append hprefix tailTrace_90876
  have hstable : (prefixWord ++ tailWord_90876).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90876).length < 2 ^ (prefixWord ++ tailWord_90876).sum := by decide
  have hdescent : baseEnd_90876 < baseStart_90876 := by decide
  rcases family_descends (prefixWord ++ tailWord_90876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90897 : List Nat := [1, 2, 2, 1, 1, 3, 3, 6]
def baseStart_90897 : Nat := 118140960795 + 90897 * 2 ^ 59
def prefixEnd_90897 : Nat := 4983230072969 + 3 ^ 40 * 90897 * 2
def baseEnd_90897 : Nat := 27658578401088058530061

theorem tailTrace_90897 : CollatzResearch.WordTrace tailWord_90897 prefixEnd_90897 27658578401088058530061 := by
  unfold tailWord_90897
  simp only [CollatzResearch.WordTrace]
  refine ⟨3315285951703167816782945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2210190634468778544521963 3315285951703167816782945)
  ·
    refine ⟨2486464463777375862587209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3315285951703167816782945 2486464463777375862587209)
    ·
      refine ⟨1864848347833031896940407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2486464463777375862587209 1864848347833031896940407)
      ·
        refine ⟨2797272521749547845410611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1864848347833031896940407 2797272521749547845410611)
        ·
          refine ⟨4195908782624321768115917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2797272521749547845410611 4195908782624321768115917)
          ·
            refine ⟨1573465793484120663043469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4195908782624321768115917 1573465793484120663043469)
            ·
              refine ⟨590049672556545248641301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1573465793484120663043469 590049672556545248641301)
              ·
                refine ⟨27658578401088058530061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 590049672556545248641301 27658578401088058530061)
                ·
                  rfl

theorem cell19_90897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 6].length) (baseStart_90897 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_90897 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_90897 prefixEnd_90897 := by exact prefixLift 90897
  have htrace : WordTrace (prefixWord ++ tailWord_90897) baseStart_90897 baseEnd_90897 := by
    simpa [prefixWord, tailWord_90897, baseEnd_90897] using wordTrace_append hprefix tailTrace_90897
  have hstable : (prefixWord ++ tailWord_90897).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90897).length < 2 ^ (prefixWord ++ tailWord_90897).sum := by decide
  have hdescent : baseEnd_90897 < baseStart_90897 := by decide
  rcases family_descends (prefixWord ++ tailWord_90897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90914 : List Nat := [3, 3, 1, 1, 2, 2, 2, 5]
def baseStart_90914 : Nat := 118140960795 + 90914 * 2 ^ 59
def prefixEnd_90914 : Nat := 4983230072969 + 3 ^ 40 * 90914 * 2
def baseEnd_90914 : Nat := 27663751243237056152237

theorem tailTrace_90914 : CollatzResearch.WordTrace tailWord_90914 prefixEnd_90914 27663751243237056152237 := by
  unfold tailWord_90914
  simp only [CollatzResearch.WordTrace]
  refine ⟨828976498160394930037949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2210603995094386480101197 828976498160394930037949)
  ·
    refine ⟨310866186810148098764231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 828976498160394930037949 310866186810148098764231)
    ·
      refine ⟨466299280215222148146347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 310866186810148098764231 466299280215222148146347)
      ·
        refine ⟨699448920322833222219521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 466299280215222148146347 699448920322833222219521)
        ·
          refine ⟨524586690242124916664641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 699448920322833222219521 524586690242124916664641)
          ·
            refine ⟨393440017681593687498481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 524586690242124916664641 393440017681593687498481)
            ·
              refine ⟨295080013261195265623861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 393440017681593687498481 295080013261195265623861)
              ·
                refine ⟨27663751243237056152237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 295080013261195265623861 27663751243237056152237)
                ·
                  rfl

theorem cell19_90914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 5].length) (baseStart_90914 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_90914 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_90914 prefixEnd_90914 := by exact prefixLift 90914
  have htrace : WordTrace (prefixWord ++ tailWord_90914) baseStart_90914 baseEnd_90914 := by
    simpa [prefixWord, tailWord_90914, baseEnd_90914] using wordTrace_append hprefix tailTrace_90914
  have hstable : (prefixWord ++ tailWord_90914).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90914).length < 2 ^ (prefixWord ++ tailWord_90914).sum := by decide
  have hdescent : baseEnd_90914 < baseStart_90914 := by decide
  rcases family_descends (prefixWord ++ tailWord_90914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90954 : List Nat := [3, 1, 2, 1, 1, 1, 2, 8]
def baseStart_90954 : Nat := 118140960795 + 90954 * 2 ^ 59
def prefixEnd_90954 : Nat := 4983230072969 + 3 ^ 40 * 90954 * 2
def baseEnd_90954 : Nat := 27675922636528815263239

theorem tailTrace_90954 : CollatzResearch.WordTrace tailWord_90954 prefixEnd_90954 27675922636528815263239 := by
  unfold tailWord_90954
  simp only [CollatzResearch.WordTrace]
  refine ⟨829341228124166637901979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2211576608331111034405277 829341228124166637901979)
  ·
    refine ⟨1244011842186249956852969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 829341228124166637901979 1244011842186249956852969)
    ·
      refine ⟨933008881639687467639727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1244011842186249956852969 933008881639687467639727)
      ·
        refine ⟨1399513322459531201459591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 933008881639687467639727 1399513322459531201459591)
        ·
          refine ⟨2099269983689296802189387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1399513322459531201459591 2099269983689296802189387)
          ·
            refine ⟨3148904975533945203284081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2099269983689296802189387 3148904975533945203284081)
            ·
              refine ⟨2361678731650458902463061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3148904975533945203284081 2361678731650458902463061)
              ·
                refine ⟨27675922636528815263239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2361678731650458902463061 27675922636528815263239)
                ·
                  rfl

theorem cell19_90954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 8].length) (baseStart_90954 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_90954 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_90954 prefixEnd_90954 := by exact prefixLift 90954
  have htrace : WordTrace (prefixWord ++ tailWord_90954) baseStart_90954 baseEnd_90954 := by
    simpa [prefixWord, tailWord_90954, baseEnd_90954] using wordTrace_append hprefix tailTrace_90954
  have hstable : (prefixWord ++ tailWord_90954).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90954).length < 2 ^ (prefixWord ++ tailWord_90954).sum := by decide
  have hdescent : baseEnd_90954 < baseStart_90954 := by decide
  rcases family_descends (prefixWord ++ tailWord_90954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91011 : List Nat := [1, 1, 1, 3, 4, 1, 2, 6]
def baseStart_91011 : Nat := 118140960795 + 91011 * 2 ^ 59
def prefixEnd_91011 : Nat := 4983230072969 + 3 ^ 40 * 91011 * 2
def baseEnd_91011 : Nat := 27693266871969571996417

theorem tailTrace_91011 : CollatzResearch.WordTrace tailWord_91011 prefixEnd_91011 27693266871969571996417 := by
  unfold tailWord_91011
  simp only [CollatzResearch.WordTrace]
  refine ⟨3319443873290165286432887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2212962582193443524288591 3319443873290165286432887)
  ·
    refine ⟨4979165809935247929649331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3319443873290165286432887 4979165809935247929649331)
    ·
      refine ⟨7468748714902871894473997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4979165809935247929649331 7468748714902871894473997)
      ·
        refine ⟨2800780768088576960427749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7468748714902871894473997 2800780768088576960427749)
        ·
          refine ⟨525146394016608180080203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2800780768088576960427749 525146394016608180080203)
          ·
            refine ⟨787719591024912270120305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 525146394016608180080203 787719591024912270120305)
            ·
              refine ⟨590789693268684202590229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 787719591024912270120305 590789693268684202590229)
              ·
                refine ⟨27693266871969571996417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 590789693268684202590229 27693266871969571996417)
                ·
                  rfl

theorem cell19_91011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 6].length) (baseStart_91011 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_91011 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_91011 prefixEnd_91011 := by exact prefixLift 91011
  have htrace : WordTrace (prefixWord ++ tailWord_91011) baseStart_91011 baseEnd_91011 := by
    simpa [prefixWord, tailWord_91011, baseEnd_91011] using wordTrace_append hprefix tailTrace_91011
  have hstable : (prefixWord ++ tailWord_91011).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91011).length < 2 ^ (prefixWord ++ tailWord_91011).sum := by decide
  have hdescent : baseEnd_91011 < baseStart_91011 := by decide
  rcases family_descends (prefixWord ++ tailWord_91011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91026 : List Nat := [3, 2, 3, 2, 2, 1, 1, 5]
def baseStart_91026 : Nat := 118140960795 + 91026 * 2 ^ 59
def prefixEnd_91026 : Nat := 4983230072969 + 3 ^ 40 * 91026 * 2
def baseEnd_91026 : Nat := 27697831144453981663043

theorem tailTrace_91026 : CollatzResearch.WordTrace tailWord_91026 prefixEnd_91026 27697831144453981663043 := by
  unfold tailWord_91026
  simp only [CollatzResearch.WordTrace]
  refine ⟨829997742058955712057233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2213327312157215232152621 829997742058955712057233)
  ·
    refine ⟨622498306544216784042925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 829997742058955712057233 622498306544216784042925)
    ·
      refine ⟨233436864954081294016097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 622498306544216784042925 233436864954081294016097)
      ·
        refine ⟨175077648715560970512073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 233436864954081294016097 175077648715560970512073)
        ·
          refine ⟨131308236536670727884055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 175077648715560970512073 131308236536670727884055)
          ·
            refine ⟨196962354805006091826083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131308236536670727884055 196962354805006091826083)
            ·
              refine ⟨295443532207509137739125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 196962354805006091826083 295443532207509137739125)
              ·
                refine ⟨27697831144453981663043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 295443532207509137739125 27697831144453981663043)
                ·
                  rfl

theorem cell19_91026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 5].length) (baseStart_91026 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_91026 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_91026 prefixEnd_91026 := by exact prefixLift 91026
  have htrace : WordTrace (prefixWord ++ tailWord_91026) baseStart_91026 baseEnd_91026 := by
    simpa [prefixWord, tailWord_91026, baseEnd_91026] using wordTrace_append hprefix tailTrace_91026
  have hstable : (prefixWord ++ tailWord_91026).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91026).length < 2 ^ (prefixWord ++ tailWord_91026).sum := by decide
  have hdescent : baseEnd_91026 < baseStart_91026 := by decide
  rcases family_descends (prefixWord ++ tailWord_91026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91028 : List Nat := [2, 4, 2, 1, 1, 1, 3, 5]
def baseStart_91028 : Nat := 118140960795 + 91028 * 2 ^ 59
def prefixEnd_91028 : Nat := 4983230072969 + 3 ^ 40 * 91028 * 2
def baseEnd_91028 : Nat := 27698439714118569618593

theorem tailTrace_91028 : CollatzResearch.WordTrace tailWord_91028 prefixEnd_91028 27698439714118569618593 := by
  unfold tailWord_91028
  simp only [CollatzResearch.WordTrace]
  refine ⟨1660031957114288594900869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2213375942819051459867825 1660031957114288594900869)
  ·
    refine ⟨311255991958929111543913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1660031957114288594900869 311255991958929111543913)
    ·
      refine ⟨233441993969196833657935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 311255991958929111543913 233441993969196833657935)
      ·
        refine ⟨350162990953795250486903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 233441993969196833657935 350162990953795250486903)
        ·
          refine ⟨525244486430692875730355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 350162990953795250486903 525244486430692875730355)
          ·
            refine ⟨787866729646039313595533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 525244486430692875730355 787866729646039313595533)
            ·
              refine ⟨295450023617264742598325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 787866729646039313595533 295450023617264742598325)
              ·
                refine ⟨27698439714118569618593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 295450023617264742598325 27698439714118569618593)
                ·
                  rfl

theorem cell19_91028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 5].length) (baseStart_91028 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_91028 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_91028 prefixEnd_91028 := by exact prefixLift 91028
  have htrace : WordTrace (prefixWord ++ tailWord_91028) baseStart_91028 baseEnd_91028 := by
    simpa [prefixWord, tailWord_91028, baseEnd_91028] using wordTrace_append hprefix tailTrace_91028
  have hstable : (prefixWord ++ tailWord_91028).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91028).length < 2 ^ (prefixWord ++ tailWord_91028).sum := by decide
  have hdescent : baseEnd_91028 < baseStart_91028 := by decide
  rcases family_descends (prefixWord ++ tailWord_91028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91087 : List Nat := [1, 1, 2, 1, 1, 6, 2, 5]
def baseStart_91087 : Nat := 118140960795 + 91087 * 2 ^ 59
def prefixEnd_91087 : Nat := 4983230072969 + 3 ^ 40 * 91087 * 2
def baseEnd_91087 : Nat := 27716392519223914307321

theorem tailTrace_91087 : CollatzResearch.WordTrace tailWord_91087 prefixEnd_91087 27716392519223914307321 := by
  unfold tailWord_91087
  simp only [CollatzResearch.WordTrace]
  refine ⟨3322215821014830266199515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2214810547343220177466343 3322215821014830266199515)
  ·
    refine ⟨4983323731522245399299273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3322215821014830266199515 4983323731522245399299273)
    ·
      refine ⟨3737492798641684049474455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4983323731522245399299273 3737492798641684049474455)
      ·
        refine ⟨5606239197962526074211683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3737492798641684049474455 5606239197962526074211683)
        ·
          refine ⟨8409358796943789111317525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5606239197962526074211683 8409358796943789111317525)
          ·
            refine ⟨394188693606740114593009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 8409358796943789111317525 394188693606740114593009)
            ·
              refine ⟨295641520205055085944757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 394188693606740114593009 295641520205055085944757)
              ·
                refine ⟨27716392519223914307321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 295641520205055085944757 27716392519223914307321)
                ·
                  rfl

theorem cell19_91087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 5].length) (baseStart_91087 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_91087 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_91087 prefixEnd_91087 := by exact prefixLift 91087
  have htrace : WordTrace (prefixWord ++ tailWord_91087) baseStart_91087 baseEnd_91087 := by
    simpa [prefixWord, tailWord_91087, baseEnd_91087] using wordTrace_append hprefix tailTrace_91087
  have hstable : (prefixWord ++ tailWord_91087).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91087).length < 2 ^ (prefixWord ++ tailWord_91087).sum := by decide
  have hdescent : baseEnd_91087 < baseStart_91087 := by decide
  rcases family_descends (prefixWord ++ tailWord_91087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91197 : List Nat := [1, 4, 1, 3, 1, 4, 2, 3]
def baseStart_91197 : Nat := 118140960795 + 91197 * 2 ^ 59
def prefixEnd_91197 : Nat := 4983230072969 + 3 ^ 40 * 91197 * 2
def baseEnd_91197 : Nat := 27749863850776251862577

theorem tailTrace_91197 : CollatzResearch.WordTrace tailWord_91197 prefixEnd_91197 27749863850776251862577 := by
  unfold tailWord_91197
  simp only [CollatzResearch.WordTrace]
  refine ⟨3326227850616319052703845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2217485233744212701802563 3326227850616319052703845)
  ·
    refine ⟨623667721990559822381971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3326227850616319052703845 623667721990559822381971)
    ·
      refine ⟨935501582985839733572957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 623667721990559822381971 935501582985839733572957)
      ·
        refine ⟨350813093619689900089859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 935501582985839733572957 350813093619689900089859)
        ·
          refine ⟨526219640429534850134789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 350813093619689900089859 526219640429534850134789)
          ·
            refine ⟨98666182580537784400273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 526219640429534850134789 98666182580537784400273)
            ·
              refine ⟨73999636935403338300205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98666182580537784400273 73999636935403338300205)
              ·
                refine ⟨27749863850776251862577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73999636935403338300205 27749863850776251862577)
                ·
                  rfl

theorem cell19_91197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 2, 3].length) (baseStart_91197 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_91197 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_91197 prefixEnd_91197 := by exact prefixLift 91197
  have htrace : WordTrace (prefixWord ++ tailWord_91197) baseStart_91197 baseEnd_91197 := by
    simpa [prefixWord, tailWord_91197, baseEnd_91197] using wordTrace_append hprefix tailTrace_91197
  have hstable : (prefixWord ++ tailWord_91197).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91197).length < 2 ^ (prefixWord ++ tailWord_91197).sum := by decide
  have hdescent : baseEnd_91197 < baseStart_91197 := by decide
  rcases family_descends (prefixWord ++ tailWord_91197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91218 : List Nat := [3, 2, 2, 1, 3, 3, 5]
def baseStart_91218 : Nat := 118140960795 + 91218 * 2 ^ 59
def prefixEnd_91218 : Nat := 4983230072969 + 3 ^ 40 * 91218 * 2
def baseEnd_91218 : Nat := 9252084610751475131951

theorem tailTrace_91218 : CollatzResearch.WordTrace tailWord_91218 prefixEnd_91218 9252084610751475131951 := by
  unfold tailWord_91218
  simp only [CollatzResearch.WordTrace]
  refine ⟨831748445885059909804577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2217995855693493092812205 831748445885059909804577)
  ·
    refine ⟨623811334413794932353433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 831748445885059909804577 623811334413794932353433)
    ·
      refine ⟨467858500810346199265075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 623811334413794932353433 467858500810346199265075)
      ·
        refine ⟨701787751215519298897613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 467858500810346199265075 701787751215519298897613)
        ·
          refine ⟨263170406705819737086605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 701787751215519298897613 263170406705819737086605)
          ·
            refine ⟨98688902514682401407477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 263170406705819737086605 98688902514682401407477)
            ·
              refine ⟨9252084610751475131951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 98688902514682401407477 9252084610751475131951)
              ·
                rfl

theorem cell19_91218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 5].length) (baseStart_91218 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_91218 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_91218 prefixEnd_91218 := by exact prefixLift 91218
  have htrace : WordTrace (prefixWord ++ tailWord_91218) baseStart_91218 baseEnd_91218 := by
    simpa [prefixWord, tailWord_91218, baseEnd_91218] using wordTrace_append hprefix tailTrace_91218
  have hstable : (prefixWord ++ tailWord_91218).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91218).length < 2 ^ (prefixWord ++ tailWord_91218).sum := by decide
  have hdescent : baseEnd_91218 < baseStart_91218 := by decide
  rcases family_descends (prefixWord ++ tailWord_91218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91220 : List Nat := [2, 4, 1, 1, 1, 1, 9]
def baseStart_91220 : Nat := 118140960795 + 91220 * 2 ^ 59
def prefixEnd_91220 : Nat := 4983230072969 + 3 ^ 40 * 91220 * 2
def baseEnd_91220 : Nat := 9252287467306337783801

theorem tailTrace_91220 : CollatzResearch.WordTrace tailWord_91220 prefixEnd_91220 9252287467306337783801 := by
  unfold tailWord_91220
  simp only [CollatzResearch.WordTrace]
  refine ⟨1663533364766496990395557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2218044486355329320527409 1663533364766496990395557)
  ·
    refine ⟨311912505893718185699167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1663533364766496990395557 311912505893718185699167)
    ·
      refine ⟨467868758840577278548751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 311912505893718185699167 467868758840577278548751)
      ·
        refine ⟨701803138260865917823127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 467868758840577278548751 701803138260865917823127)
        ·
          refine ⟨1052704707391298876734691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 701803138260865917823127 1052704707391298876734691)
          ·
            refine ⟨1579057061086948315102037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1052704707391298876734691 1579057061086948315102037)
            ·
              refine ⟨9252287467306337783801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1579057061086948315102037 9252287467306337783801)
              ·
                rfl

theorem cell19_91220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 9].length) (baseStart_91220 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_91220 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_91220 prefixEnd_91220 := by exact prefixLift 91220
  have htrace : WordTrace (prefixWord ++ tailWord_91220) baseStart_91220 baseEnd_91220 := by
    simpa [prefixWord, tailWord_91220, baseEnd_91220] using wordTrace_append hprefix tailTrace_91220
  have hstable : (prefixWord ++ tailWord_91220).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91220).length < 2 ^ (prefixWord ++ tailWord_91220).sum := by decide
  have hdescent : baseEnd_91220 < baseStart_91220 := by decide
  rcases family_descends (prefixWord ++ tailWord_91220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91239 : List Nat := [1, 1, 5, 1, 1, 3, 1, 6]
def baseStart_91239 : Nat := 118140960795 + 91239 * 2 ^ 59
def prefixEnd_91239 : Nat := 4983230072969 + 3 ^ 40 * 91239 * 2
def baseEnd_91239 : Nat := 27762643813732598929129

theorem tailTrace_91239 : CollatzResearch.WordTrace tailWord_91239 prefixEnd_91239 27762643813732598929129 := by
  unfold tailWord_91239
  simp only [CollatzResearch.WordTrace]
  refine ⟨3327759716464160225732771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2218506477642773483821847 3327759716464160225732771)
  ·
    refine ⟨4991639574696240338599157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3327759716464160225732771 4991639574696240338599157)
    ·
      refine ⟨467966210127772531743671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4991639574696240338599157 467966210127772531743671)
      ·
        refine ⟨701949315191658797615507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 467966210127772531743671 701949315191658797615507)
        ·
          refine ⟨1052923972787488196423261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 701949315191658797615507 1052923972787488196423261)
          ·
            refine ⟨394846489795308073658723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1052923972787488196423261 394846489795308073658723)
            ·
              refine ⟨592269734692962110488085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 394846489795308073658723 592269734692962110488085)
              ·
                refine ⟨27762643813732598929129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 592269734692962110488085 27762643813732598929129)
                ·
                  rfl

theorem cell19_91239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 6].length) (baseStart_91239 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_91239 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_91239 prefixEnd_91239 := by exact prefixLift 91239
  have htrace : WordTrace (prefixWord ++ tailWord_91239) baseStart_91239 baseEnd_91239 := by
    simpa [prefixWord, tailWord_91239, baseEnd_91239] using wordTrace_append hprefix tailTrace_91239
  have hstable : (prefixWord ++ tailWord_91239).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91239).length < 2 ^ (prefixWord ++ tailWord_91239).sum := by decide
  have hdescent : baseEnd_91239 < baseStart_91239 := by decide
  rcases family_descends (prefixWord ++ tailWord_91239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91332 : List Nat := [2, 3, 3, 1, 3, 1, 6]
def baseStart_91332 : Nat := 118140960795 + 91332 * 2 ^ 59
def prefixEnd_91332 : Nat := 4983230072969 + 3 ^ 40 * 91332 * 2
def baseEnd_91332 : Nat := 9263647434378646287403

theorem tailTrace_91332 : CollatzResearch.WordTrace tailWord_91332 prefixEnd_91332 9263647434378646287403 := by
  unfold tailWord_91332
  simp only [CollatzResearch.WordTrace]
  refine ⟨1665575852563618554434125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2220767803418158072578833 1665575852563618554434125)
  ·
    refine ⟨624590944711356957912797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1665575852563618554434125 624590944711356957912797)
    ·
      refine ⟨234221604266758859217299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 624590944711356957912797 234221604266758859217299)
      ·
        refine ⟨351332406400138288825949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234221604266758859217299 351332406400138288825949)
        ·
          refine ⟨131749652400051858309731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 351332406400138288825949 131749652400051858309731)
          ·
            refine ⟨197624478600077787464597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131749652400051858309731 197624478600077787464597)
            ·
              refine ⟨9263647434378646287403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 197624478600077787464597 9263647434378646287403)
              ·
                rfl

theorem cell19_91332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 6].length) (baseStart_91332 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_91332 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_91332 prefixEnd_91332 := by exact prefixLift 91332
  have htrace : WordTrace (prefixWord ++ tailWord_91332) baseStart_91332 baseEnd_91332 := by
    simpa [prefixWord, tailWord_91332, baseEnd_91332] using wordTrace_append hprefix tailTrace_91332
  have hstable : (prefixWord ++ tailWord_91332).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91332).length < 2 ^ (prefixWord ++ tailWord_91332).sum := by decide
  have hdescent : baseEnd_91332 < baseStart_91332 := by decide
  rcases family_descends (prefixWord ++ tailWord_91332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91370 : List Nat := [3, 1, 3, 1, 1, 3, 4, 3]
def baseStart_91370 : Nat := 118140960795 + 91370 * 2 ^ 59
def prefixEnd_91370 : Nat := 4983230072969 + 3 ^ 40 * 91370 * 2
def baseEnd_91370 : Nat := 27802505126763110017661

theorem tailTrace_91370 : CollatzResearch.WordTrace tailWord_91370 prefixEnd_91370 27802505126763110017661 := by
  unfold tailWord_91370
  simp only [CollatzResearch.WordTrace]
  refine ⟨833134419747392399687891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2221691785993046399167709 833134419747392399687891)
  ·
    refine ⟨1249701629621088599531837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 833134419747392399687891 1249701629621088599531837)
    ·
      refine ⟨468638111107908224824439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1249701629621088599531837 468638111107908224824439)
      ·
        refine ⟨702957166661862337236659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 468638111107908224824439 702957166661862337236659)
        ·
          refine ⟨1054435749992793505854989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 702957166661862337236659 1054435749992793505854989)
          ·
            refine ⟨395413406247297564695621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1054435749992793505854989 395413406247297564695621)
            ·
              refine ⟨74140013671368293380429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 395413406247297564695621 74140013671368293380429)
              ·
                refine ⟨27802505126763110017661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74140013671368293380429 27802505126763110017661)
                ·
                  rfl

theorem cell19_91370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 4, 3].length) (baseStart_91370 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_91370 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_91370 prefixEnd_91370 := by exact prefixLift 91370
  have htrace : WordTrace (prefixWord ++ tailWord_91370) baseStart_91370 baseEnd_91370 := by
    simpa [prefixWord, tailWord_91370, baseEnd_91370] using wordTrace_append hprefix tailTrace_91370
  have hstable : (prefixWord ++ tailWord_91370).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91370).length < 2 ^ (prefixWord ++ tailWord_91370).sum := by decide
  have hdescent : baseEnd_91370 < baseStart_91370 := by decide
  rcases family_descends (prefixWord ++ tailWord_91370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91372 : List Nat := [2, 2, 1, 1, 2, 5, 1, 5]
def baseStart_91372 : Nat := 118140960795 + 91372 * 2 ^ 59
def prefixEnd_91372 : Nat := 4983230072969 + 3 ^ 40 * 91372 * 2
def baseEnd_91372 : Nat := 27803113696427697973211

theorem tailTrace_91372 : CollatzResearch.WordTrace tailWord_91372 prefixEnd_91372 27803113696427697973211 := by
  unfold tailWord_91372
  simp only [CollatzResearch.WordTrace]
  refine ⟨1666305312491161970162185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2221740416654882626882913 1666305312491161970162185)
  ·
    refine ⟨1249728984368371477621639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1666305312491161970162185 1249728984368371477621639)
    ·
      refine ⟨1874593476552557216432459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1249728984368371477621639 1874593476552557216432459)
      ·
        refine ⟨2811890214828835824648689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1874593476552557216432459 2811890214828835824648689)
        ·
          refine ⟨2108917661121626868486517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2811890214828835824648689 2108917661121626868486517)
          ·
            refine ⟨197711030730152518920611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2108917661121626868486517 197711030730152518920611)
            ·
              refine ⟨296566546095228778380917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 197711030730152518920611 296566546095228778380917)
              ·
                refine ⟨27803113696427697973211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 296566546095228778380917 27803113696427697973211)
                ·
                  rfl

theorem cell19_91372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 5].length) (baseStart_91372 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_91372 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_91372 prefixEnd_91372 := by exact prefixLift 91372
  have htrace : WordTrace (prefixWord ++ tailWord_91372) baseStart_91372 baseEnd_91372 := by
    simpa [prefixWord, tailWord_91372, baseEnd_91372] using wordTrace_append hprefix tailTrace_91372
  have hstable : (prefixWord ++ tailWord_91372).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91372).length < 2 ^ (prefixWord ++ tailWord_91372).sum := by decide
  have hdescent : baseEnd_91372 < baseStart_91372 := by decide
  rcases family_descends (prefixWord ++ tailWord_91372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91391 : List Nat := [1, 1, 2, 2, 1, 7, 5]
def baseStart_91391 : Nat := 118140960795 + 91391 * 2 ^ 59
def prefixEnd_91391 : Nat := 4983230072969 + 3 ^ 40 * 91391 * 2
def baseEnd_91391 : Nat := 9269631702747094516979

theorem tailTrace_91391 : CollatzResearch.WordTrace tailWord_91391 prefixEnd_91391 9269631702747094516979 := by
  unfold tailWord_91391
  simp only [CollatzResearch.WordTrace]
  refine ⟨3333303611913490185266027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2222202407942326790177351 3333303611913490185266027)
  ·
    refine ⟨4999955417870235277899041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3333303611913490185266027 4999955417870235277899041)
    ·
      refine ⟨3749966563402676458424281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4999955417870235277899041 3749966563402676458424281)
      ·
        refine ⟨2812474922552007343818211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3749966563402676458424281 2812474922552007343818211)
        ·
          refine ⟨4218712383828011015727317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2812474922552007343818211 4218712383828011015727317)
          ·
            refine ⟨98876071495969008181109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 4218712383828011015727317 98876071495969008181109)
            ·
              refine ⟨9269631702747094516979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 98876071495969008181109 9269631702747094516979)
              ·
                rfl

theorem cell19_91391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 5].length) (baseStart_91391 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_91391 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_91391 prefixEnd_91391 := by exact prefixLift 91391
  have htrace : WordTrace (prefixWord ++ tailWord_91391) baseStart_91391 baseEnd_91391 := by
    simpa [prefixWord, tailWord_91391, baseEnd_91391] using wordTrace_append hprefix tailTrace_91391
  have hstable : (prefixWord ++ tailWord_91391).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91391).length < 2 ^ (prefixWord ++ tailWord_91391).sum := by decide
  have hdescent : baseEnd_91391 < baseStart_91391 := by decide
  rcases family_descends (prefixWord ++ tailWord_91391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91429 : List Nat := [1, 3, 1, 2, 4, 1, 2, 5]
def baseStart_91429 : Nat := 118140960795 + 91429 * 2 ^ 59
def prefixEnd_91429 : Nat := 4983230072969 + 3 ^ 40 * 91429 * 2
def baseEnd_91429 : Nat := 27820457931868454706389

theorem tailTrace_91429 : CollatzResearch.WordTrace tailWord_91429 prefixEnd_91429 27820457931868454706389 := by
  unfold tailWord_91429
  simp only [CollatzResearch.WordTrace]
  refine ⟨3334689585775822675149341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2223126390517215116766227 3334689585775822675149341)
  ·
    refine ⟨1250508594665933503181003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3334689585775822675149341 1250508594665933503181003)
    ·
      refine ⟨1875762891998900254771505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1250508594665933503181003 1875762891998900254771505)
      ·
        refine ⟨1406822168999175191078629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1875762891998900254771505 1406822168999175191078629)
        ·
          refine ⟨263779156687345348327243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1406822168999175191078629 263779156687345348327243)
          ·
            refine ⟨395668735031018022490865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 263779156687345348327243 395668735031018022490865)
            ·
              refine ⟨296751551273263516868149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 395668735031018022490865 296751551273263516868149)
              ·
                refine ⟨27820457931868454706389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 296751551273263516868149 27820457931868454706389)
                ·
                  rfl

theorem cell19_91429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 5].length) (baseStart_91429 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_91429 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_91429 prefixEnd_91429 := by exact prefixLift 91429
  have htrace : WordTrace (prefixWord ++ tailWord_91429) baseStart_91429 baseEnd_91429 := by
    simpa [prefixWord, tailWord_91429, baseEnd_91429] using wordTrace_append hprefix tailTrace_91429
  have hstable : (prefixWord ++ tailWord_91429).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91429).length < 2 ^ (prefixWord ++ tailWord_91429).sum := by decide
  have hdescent : baseEnd_91429 < baseStart_91429 := by decide
  rcases family_descends (prefixWord ++ tailWord_91429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91446 : List Nat := [5, 1, 2, 3, 8]
def baseStart_91446 : Nat := 118140960795 + 91446 * 2 ^ 59
def prefixEnd_91446 : Nat := 4983230072969 + 3 ^ 40 * 91446 * 2
def baseEnd_91446 : Nat := 1030578917556201938095

theorem tailTrace_91446 : CollatzResearch.WordTrace tailWord_91446 prefixEnd_91446 1030578917556201938095 := by
  unfold tailWord_91446
  simp only [CollatzResearch.WordTrace]
  refine ⟨208456851669639661157387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2223539751142823052345461 208456851669639661157387)
  ·
    refine ⟨312685277504459491736081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208456851669639661157387 312685277504459491736081)
    ·
      refine ⟨234513958128344618802061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 312685277504459491736081 234513958128344618802061)
      ·
        refine ⟨87942734298129232050773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 234513958128344618802061 87942734298129232050773)
        ·
          refine ⟨1030578917556201938095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 87942734298129232050773 1030578917556201938095)
          ·
            rfl

theorem cell19_91446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 8].length) (baseStart_91446 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_91446 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_91446 prefixEnd_91446 := by exact prefixLift 91446
  have htrace : WordTrace (prefixWord ++ tailWord_91446) baseStart_91446 baseEnd_91446 := by
    simpa [prefixWord, tailWord_91446, baseEnd_91446] using wordTrace_append hprefix tailTrace_91446
  have hstable : (prefixWord ++ tailWord_91446).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91446).length < 2 ^ (prefixWord ++ tailWord_91446).sum := by decide
  have hdescent : baseEnd_91446 < baseStart_91446 := by decide
  rcases family_descends (prefixWord ++ tailWord_91446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91564 : List Nat := [2, 2, 1, 1, 1, 1, 11]
def baseStart_91564 : Nat := 118140960795 + 91564 * 2 ^ 59
def prefixEnd_91564 : Nat := 4983230072969 + 3 ^ 40 * 91564 * 2
def baseEnd_91564 : Nat := 9287178794742713902007

theorem tailTrace_91564 : CollatzResearch.WordTrace tailWord_91564 prefixEnd_91564 9287178794742713902007 := by
  unfold tailWord_91564
  simp only [CollatzResearch.WordTrace]
  refine ⟨1669806720143370365656873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2226408960191160487542497 1669806720143370365656873)
  ·
    refine ⟨1252355040107527774242655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1669806720143370365656873 1252355040107527774242655)
    ·
      refine ⟨1878532560161291661363983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1252355040107527774242655 1878532560161291661363983)
      ·
        refine ⟨2817798840241937492045975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1878532560161291661363983 2817798840241937492045975)
        ·
          refine ⟨4226698260362906238068963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2817798840241937492045975 4226698260362906238068963)
          ·
            refine ⟨6340047390544359357103445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4226698260362906238068963 6340047390544359357103445)
            ·
              refine ⟨9287178794742713902007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 6340047390544359357103445 9287178794742713902007)
              ·
                rfl

theorem cell19_91564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 11].length) (baseStart_91564 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_91564 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_91564 prefixEnd_91564 := by exact prefixLift 91564
  have htrace : WordTrace (prefixWord ++ tailWord_91564) baseStart_91564 baseEnd_91564 := by
    simpa [prefixWord, tailWord_91564, baseEnd_91564] using wordTrace_append hprefix tailTrace_91564
  have hstable : (prefixWord ++ tailWord_91564).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91564).length < 2 ^ (prefixWord ++ tailWord_91564).sum := by decide
  have hdescent : baseEnd_91564 < baseStart_91564 := by decide
  rcases family_descends (prefixWord ++ tailWord_91564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91581 : List Nat := [1, 4, 1, 2, 2, 1, 4, 4]
def baseStart_91581 : Nat := 118140960795 + 91581 * 2 ^ 59
def prefixEnd_91581 : Nat := 4983230072969 + 3 ^ 40 * 91581 * 2
def baseEnd_91581 : Nat := 27866709226377139328197

theorem tailTrace_91581 : CollatzResearch.WordTrace tailWord_91581 prefixEnd_91581 27866709226377139328197 := by
  unfold tailWord_91581
  simp only [CollatzResearch.WordTrace]
  refine ⟨3340233481225152634682597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2226822320816768423121731 3340233481225152634682597)
  ·
    refine ⟨626293777729716119002987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3340233481225152634682597 626293777729716119002987)
    ·
      refine ⟨939440666594574178504481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 626293777729716119002987 939440666594574178504481)
      ·
        refine ⟨704580499945930633878361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 939440666594574178504481 704580499945930633878361)
        ·
          refine ⟨528435374959447975408771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 704580499945930633878361 528435374959447975408771)
          ·
            refine ⟨792653062439171963113157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 528435374959447975408771 792653062439171963113157)
            ·
              refine ⟨148622449207344743083717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 792653062439171963113157 148622449207344743083717)
              ·
                refine ⟨27866709226377139328197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 148622449207344743083717 27866709226377139328197)
                ·
                  rfl

theorem cell19_91581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 4, 4].length) (baseStart_91581 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_91581 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_91581 prefixEnd_91581 := by exact prefixLift 91581
  have htrace : WordTrace (prefixWord ++ tailWord_91581) baseStart_91581 baseEnd_91581 := by
    simpa [prefixWord, tailWord_91581, baseEnd_91581] using wordTrace_append hprefix tailTrace_91581
  have hstable : (prefixWord ++ tailWord_91581).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91581).length < 2 ^ (prefixWord ++ tailWord_91581).sum := by decide
  have hdescent : baseEnd_91581 < baseStart_91581 := by decide
  rcases family_descends (prefixWord ++ tailWord_91581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91655 : List Nat := [1, 1, 4, 3, 2, 2, 3, 3]
def baseStart_91655 : Nat := 118140960795 + 91655 * 2 ^ 59
def prefixEnd_91655 : Nat := 4983230072969 + 3 ^ 40 * 91655 * 2
def baseEnd_91655 : Nat := 27889226303966893683551

theorem tailTrace_91655 : CollatzResearch.WordTrace tailWord_91655 prefixEnd_91655 27889226303966893683551 := by
  unfold tailWord_91655
  simp only [CollatzResearch.WordTrace]
  refine ⟨3342932482957063272876419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2228621655304708848584279 3342932482957063272876419)
  ·
    refine ⟨5014398724435594909314629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3342932482957063272876419 5014398724435594909314629)
    ·
      refine ⟨940199760831674045496493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5014398724435594909314629 940199760831674045496493)
      ·
        refine ⟨352574910311877767061185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 940199760831674045496493 352574910311877767061185)
        ·
          refine ⟨264431182733908325295889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 352574910311877767061185 264431182733908325295889)
          ·
            refine ⟨198323387050431243971917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 264431182733908325295889 198323387050431243971917)
            ·
              refine ⟨74371270143911716489469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 198323387050431243971917 74371270143911716489469)
              ·
                refine ⟨27889226303966893683551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74371270143911716489469 27889226303966893683551)
                ·
                  rfl

theorem cell19_91655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 3, 3].length) (baseStart_91655 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_91655 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_91655 prefixEnd_91655 := by exact prefixLift 91655
  have htrace : WordTrace (prefixWord ++ tailWord_91655) baseStart_91655 baseEnd_91655 := by
    simpa [prefixWord, tailWord_91655, baseEnd_91655] using wordTrace_append hprefix tailTrace_91655
  have hstable : (prefixWord ++ tailWord_91655).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91655).length < 2 ^ (prefixWord ++ tailWord_91655).sum := by decide
  have hdescent : baseEnd_91655 < baseStart_91655 := by decide
  rcases family_descends (prefixWord ++ tailWord_91655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91657 : List Nat := [1, 2, 1, 1, 3, 1, 7, 3]
def baseStart_91657 : Nat := 118140960795 + 91657 * 2 ^ 59
def prefixEnd_91657 : Nat := 4983230072969 + 3 ^ 40 * 91657 * 2
def baseEnd_91657 : Nat := 27889834873631481639101

theorem tailTrace_91657 : CollatzResearch.WordTrace tailWord_91657 prefixEnd_91657 27889834873631481639101 := by
  unfold tailWord_91657
  simp only [CollatzResearch.WordTrace]
  refine ⟨3343005428949817614449225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2228670285966545076299483 3343005428949817614449225)
  ·
    refine ⟨2507254071712363210836919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3343005428949817614449225 2507254071712363210836919)
    ·
      refine ⟨3760881107568544816255379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2507254071712363210836919 3760881107568544816255379)
      ·
        refine ⟨5641321661352817224383069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3760881107568544816255379 5641321661352817224383069)
        ·
          refine ⟨2115495623007306459143651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5641321661352817224383069 2115495623007306459143651)
          ·
            refine ⟨3173243434510959688715477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2115495623007306459143651 3173243434510959688715477)
            ·
              refine ⟨74372892996350617704269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 3173243434510959688715477 74372892996350617704269)
              ·
                refine ⟨27889834873631481639101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74372892996350617704269 27889834873631481639101)
                ·
                  rfl

theorem cell19_91657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 7, 3].length) (baseStart_91657 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_91657 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_91657 prefixEnd_91657 := by exact prefixLift 91657
  have htrace : WordTrace (prefixWord ++ tailWord_91657) baseStart_91657 baseEnd_91657 := by
    simpa [prefixWord, tailWord_91657, baseEnd_91657] using wordTrace_append hprefix tailTrace_91657
  have hstable : (prefixWord ++ tailWord_91657).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91657).length < 2 ^ (prefixWord ++ tailWord_91657).sum := by decide
  have hdescent : baseEnd_91657 < baseStart_91657 := by decide
  rcases family_descends (prefixWord ++ tailWord_91657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91697 : List Nat := [1, 2, 2, 3, 1, 1, 1, 8]
def baseStart_91697 : Nat := 118140960795 + 91697 * 2 ^ 59
def prefixEnd_91697 : Nat := 4983230072969 + 3 ^ 40 * 91697 * 2
def baseEnd_91697 : Nat := 27902006266923240750103

theorem tailTrace_91697 : CollatzResearch.WordTrace tailWord_91697 prefixEnd_91697 27902006266923240750103 := by
  unfold tailWord_91697
  simp only [CollatzResearch.WordTrace]
  refine ⟨3344464348804904445905345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2229642899203269630603563 3344464348804904445905345)
  ·
    refine ⟨2508348261603678334429009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3344464348804904445905345 2508348261603678334429009)
    ·
      refine ⟨1881261196202758750821757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2508348261603678334429009 1881261196202758750821757)
      ·
        refine ⟨705472948576034531558159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1881261196202758750821757 705472948576034531558159)
        ·
          refine ⟨1058209422864051797337239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 705472948576034531558159 1058209422864051797337239)
          ·
            refine ⟨1587314134296077696005859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1058209422864051797337239 1587314134296077696005859)
            ·
              refine ⟨2380971201444116544008789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1587314134296077696005859 2380971201444116544008789)
              ·
                refine ⟨27902006266923240750103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2380971201444116544008789 27902006266923240750103)
                ·
                  rfl

theorem cell19_91697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 8].length) (baseStart_91697 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_91697 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_91697 prefixEnd_91697 := by exact prefixLift 91697
  have htrace : WordTrace (prefixWord ++ tailWord_91697) baseStart_91697 baseEnd_91697 := by
    simpa [prefixWord, tailWord_91697, baseEnd_91697] using wordTrace_append hprefix tailTrace_91697
  have hstable : (prefixWord ++ tailWord_91697).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91697).length < 2 ^ (prefixWord ++ tailWord_91697).sum := by decide
  have hdescent : baseEnd_91697 < baseStart_91697 := by decide
  rcases family_descends (prefixWord ++ tailWord_91697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91735 : List Nat := [1, 1, 3, 2, 2, 3, 7]
def baseStart_91735 : Nat := 118140960795 + 91735 * 2 ^ 59
def prefixEnd_91735 : Nat := 4983230072969 + 3 ^ 40 * 91735 * 2
def baseEnd_91735 : Nat := 9304523030183470635185

theorem tailTrace_91735 : CollatzResearch.WordTrace tailWord_91735 prefixEnd_91735 9304523030183470635185 := by
  unfold tailWord_91735
  simp only [CollatzResearch.WordTrace]
  refine ⟨3345850322667236935788659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2230566881778157957192439 3345850322667236935788659)
  ·
    refine ⟨5018775484000855403682989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3345850322667236935788659 5018775484000855403682989)
    ·
      refine ⟨1882040806500320776381121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5018775484000855403682989 1882040806500320776381121)
      ·
        refine ⟨1411530604875240582285841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1882040806500320776381121 1411530604875240582285841)
        ·
          refine ⟨1058647953656430436714381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1411530604875240582285841 1058647953656430436714381)
          ·
            refine ⟨396992982621161413767893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1058647953656430436714381 396992982621161413767893)
            ·
              refine ⟨9304523030183470635185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 396992982621161413767893 9304523030183470635185)
              ·
                rfl

theorem cell19_91735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 7].length) (baseStart_91735 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_91735 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_91735 prefixEnd_91735 := by exact prefixLift 91735
  have htrace : WordTrace (prefixWord ++ tailWord_91735) baseStart_91735 baseEnd_91735 := by
    simpa [prefixWord, tailWord_91735, baseEnd_91735] using wordTrace_append hprefix tailTrace_91735
  have hstable : (prefixWord ++ tailWord_91735).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91735).length < 2 ^ (prefixWord ++ tailWord_91735).sum := by decide
  have hdescent : baseEnd_91735 < baseStart_91735 := by decide
  rcases family_descends (prefixWord ++ tailWord_91735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91752 : List Nat := [2, 1, 4, 3, 1, 1, 1, 6]
def baseStart_91752 : Nat := 118140960795 + 91752 * 2 ^ 59
def prefixEnd_91752 : Nat := 4983230072969 + 3 ^ 40 * 91752 * 2
def baseEnd_91752 : Nat := 27918741932699409527731

theorem tailTrace_91752 : CollatzResearch.WordTrace tailWord_91752 prefixEnd_91752 27918741932699409527731 := by
  unfold tailWord_91752
  simp only [CollatzResearch.WordTrace]
  refine ⟨1673235181802824419578755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2230980242403765892771673 1673235181802824419578755)
  ·
    refine ⟨2509852772704236629368133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1673235181802824419578755 2509852772704236629368133)
    ·
      refine ⟨470597394882044368006525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2509852772704236629368133 470597394882044368006525)
      ·
        refine ⟨176474023080766638002447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 470597394882044368006525 176474023080766638002447)
        ·
          refine ⟨264711034621149957003671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176474023080766638002447 264711034621149957003671)
          ·
            refine ⟨397066551931724935505507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 264711034621149957003671 397066551931724935505507)
            ·
              refine ⟨595599827897587403258261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 397066551931724935505507 595599827897587403258261)
              ·
                refine ⟨27918741932699409527731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 595599827897587403258261 27918741932699409527731)
                ·
                  rfl

theorem cell19_91752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 6].length) (baseStart_91752 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_91752 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_91752 prefixEnd_91752 := by exact prefixLift 91752
  have htrace : WordTrace (prefixWord ++ tailWord_91752) baseStart_91752 baseEnd_91752 := by
    simpa [prefixWord, tailWord_91752, baseEnd_91752] using wordTrace_append hprefix tailTrace_91752
  have hstable : (prefixWord ++ tailWord_91752).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91752).length < 2 ^ (prefixWord ++ tailWord_91752).sum := by decide
  have hdescent : baseEnd_91752 < baseStart_91752 := by decide
  rcases family_descends (prefixWord ++ tailWord_91752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91809 : List Nat := [1, 2, 3, 3, 2, 1, 3, 4]
def baseStart_91809 : Nat := 118140960795 + 91809 * 2 ^ 59
def prefixEnd_91809 : Nat := 4983230072969 + 3 ^ 40 * 91809 * 2
def baseEnd_91809 : Nat := 27936086168140166260909

theorem tailTrace_91809 : CollatzResearch.WordTrace tailWord_91809 prefixEnd_91809 27936086168140166260909 := by
  unfold tailWord_91809
  simp only [CollatzResearch.WordTrace]
  refine ⟨3348549324399147573982481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2232366216266098382654987 3348549324399147573982481)
  ·
    refine ⟨2511411993299360680486861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3348549324399147573982481 2511411993299360680486861)
    ·
      refine ⟨941779497487260255182573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2511411993299360680486861 941779497487260255182573)
      ·
        refine ⟨353167311557722595693465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 941779497487260255182573 353167311557722595693465)
        ·
          refine ⟨264875483668291946770099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 353167311557722595693465 264875483668291946770099)
          ·
            refine ⟨397313225502437920155149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 264875483668291946770099 397313225502437920155149)
            ·
              refine ⟨148992459563414220058181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 397313225502437920155149 148992459563414220058181)
              ·
                refine ⟨27936086168140166260909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 148992459563414220058181 27936086168140166260909)
                ·
                  rfl

theorem cell19_91809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 3, 4].length) (baseStart_91809 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_91809 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_91809 prefixEnd_91809 := by exact prefixLift 91809
  have htrace : WordTrace (prefixWord ++ tailWord_91809) baseStart_91809 baseEnd_91809 := by
    simpa [prefixWord, tailWord_91809, baseEnd_91809] using wordTrace_append hprefix tailTrace_91809
  have hstable : (prefixWord ++ tailWord_91809).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91809).length < 2 ^ (prefixWord ++ tailWord_91809).sum := by decide
  have hdescent : baseEnd_91809 < baseStart_91809 := by decide
  rcases family_descends (prefixWord ++ tailWord_91809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91879 : List Nat := [1, 1, 5, 4, 2, 1, 2, 3]
def baseStart_91879 : Nat := 118140960795 + 91879 * 2 ^ 59
def prefixEnd_91879 : Nat := 4983230072969 + 3 ^ 40 * 91879 * 2
def baseEnd_91879 : Nat := 27957386106400744705163

theorem tailTrace_91879 : CollatzResearch.WordTrace tailWord_91879 prefixEnd_91879 27957386106400744705163 := by
  unfold tailWord_91879
  simp only [CollatzResearch.WordTrace]
  refine ⟨3351102434145549529030691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2234068289430366352687127 3351102434145549529030691)
  ·
    refine ⟨5026653651218324293546037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3351102434145549529030691 5026653651218324293546037)
    ·
      refine ⟨471248779801717902519941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5026653651218324293546037 471248779801717902519941)
      ·
        refine ⟨88359146212822106722489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 471248779801717902519941 88359146212822106722489)
        ·
          refine ⟨66269359659616580041867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88359146212822106722489 66269359659616580041867)
          ·
            refine ⟨99404039489424870062801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66269359659616580041867 99404039489424870062801)
            ·
              refine ⟨74553029617068652547101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99404039489424870062801 74553029617068652547101)
              ·
                refine ⟨27957386106400744705163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74553029617068652547101 27957386106400744705163)
                ·
                  rfl

theorem cell19_91879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 2, 3].length) (baseStart_91879 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_91879 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_91879 prefixEnd_91879 := by exact prefixLift 91879
  have htrace : WordTrace (prefixWord ++ tailWord_91879) baseStart_91879 baseEnd_91879 := by
    simpa [prefixWord, tailWord_91879, baseEnd_91879] using wordTrace_append hprefix tailTrace_91879
  have hstable : (prefixWord ++ tailWord_91879).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91879).length < 2 ^ (prefixWord ++ tailWord_91879).sum := by decide
  have hdescent : baseEnd_91879 < baseStart_91879 := by decide
  rcases family_descends (prefixWord ++ tailWord_91879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91885 : List Nat := [1, 5, 1, 2, 1, 3, 1, 5]
def baseStart_91885 : Nat := 118140960795 + 91885 * 2 ^ 59
def prefixEnd_91885 : Nat := 4983230072969 + 3 ^ 40 * 91885 * 2
def baseEnd_91885 : Nat := 27959211815394508571813

theorem tailTrace_91885 : CollatzResearch.WordTrace tailWord_91885 prefixEnd_91885 27959211815394508571813 := by
  unfold tailWord_91885
  simp only [CollatzResearch.WordTrace]
  refine ⟨3351321272123812553749109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2234214181415875035832739 3351321272123812553749109)
  ·
    refine ⟨314186369261607426913979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3351321272123812553749109 314186369261607426913979)
    ·
      refine ⟨471279553892411140370969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 314186369261607426913979 471279553892411140370969)
      ·
        refine ⟨353459665419308355278227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 471279553892411140370969 353459665419308355278227)
        ·
          refine ⟨530189498128962532917341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 353459665419308355278227 530189498128962532917341)
          ·
            refine ⟨198821061798360949844003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 530189498128962532917341 198821061798360949844003)
            ·
              refine ⟨298231592697541424766005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 198821061798360949844003 298231592697541424766005)
              ·
                refine ⟨27959211815394508571813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 298231592697541424766005 27959211815394508571813)
                ·
                  rfl

theorem cell19_91885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 5].length) (baseStart_91885 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_91885 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_91885 prefixEnd_91885 := by exact prefixLift 91885
  have htrace : WordTrace (prefixWord ++ tailWord_91885) baseStart_91885 baseEnd_91885 := by
    simpa [prefixWord, tailWord_91885, baseEnd_91885] using wordTrace_append hprefix tailTrace_91885
  have hstable : (prefixWord ++ tailWord_91885).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91885).length < 2 ^ (prefixWord ++ tailWord_91885).sum := by decide
  have hdescent : baseEnd_91885 < baseStart_91885 := by decide
  rcases family_descends (prefixWord ++ tailWord_91885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91887 : List Nat := [1, 1, 2, 1, 5, 1, 3, 5]
def baseStart_91887 : Nat := 118140960795 + 91887 * 2 ^ 59
def prefixEnd_91887 : Nat := 4983230072969 + 3 ^ 40 * 91887 * 2
def baseEnd_91887 : Nat := 27959820385059096527363

theorem tailTrace_91887 : CollatzResearch.WordTrace tailWord_91887 prefixEnd_91887 27959820385059096527363 := by
  unfold tailWord_91887
  simp only [CollatzResearch.WordTrace]
  refine ⟨3351394218116566895321915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2234262812077711263547943 3351394218116566895321915)
  ·
    refine ⟨5027091327174850342982873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3351394218116566895321915 5027091327174850342982873)
    ·
      refine ⟨3770318495381137757237155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5027091327174850342982873 3770318495381137757237155)
      ·
        refine ⟨5655477743071706635855733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3770318495381137757237155 5655477743071706635855733)
        ·
          refine ⟨530201038412972497111475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5655477743071706635855733 530201038412972497111475)
          ·
            refine ⟨795301557619458745667213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 530201038412972497111475 795301557619458745667213)
            ·
              refine ⟨298238084107297029625205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 795301557619458745667213 298238084107297029625205)
              ·
                refine ⟨27959820385059096527363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 298238084107297029625205 27959820385059096527363)
                ·
                  rfl

theorem cell19_91887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 5].length) (baseStart_91887 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_91887 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_91887 prefixEnd_91887 := by exact prefixLift 91887
  have htrace : WordTrace (prefixWord ++ tailWord_91887) baseStart_91887 baseEnd_91887 := by
    simpa [prefixWord, tailWord_91887, baseEnd_91887] using wordTrace_append hprefix tailTrace_91887
  have hstable : (prefixWord ++ tailWord_91887).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91887).length < 2 ^ (prefixWord ++ tailWord_91887).sum := by decide
  have hdescent : baseEnd_91887 < baseStart_91887 := by decide
  rcases family_descends (prefixWord ++ tailWord_91887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91902 : List Nat := [4, 2, 2, 1, 3, 2, 5]
def baseStart_91902 : Nat := 118140960795 + 91902 * 2 ^ 59
def prefixEnd_91902 : Nat := 4983230072969 + 3 ^ 40 * 91902 * 2
def baseEnd_91902 : Nat := 9321461552514502064663

theorem tailTrace_91902 : CollatzResearch.WordTrace tailWord_91902 prefixEnd_91902 9321461552514502064663 := by
  unfold tailWord_91902
  simp only [CollatzResearch.WordTrace]
  refine ⟨418992664132778057139745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2234627542041482971411973 418992664132778057139745)
  ·
    refine ⟨314244498099583542854809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 418992664132778057139745 314244498099583542854809)
    ·
      refine ⟨235683373574687657141107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 314244498099583542854809 235683373574687657141107)
      ·
        refine ⟨353525060362031485711661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235683373574687657141107 353525060362031485711661)
        ·
          refine ⟨132571897635761807141873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 353525060362031485711661 132571897635761807141873)
          ·
            refine ⟨99428923226821355356405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132571897635761807141873 99428923226821355356405)
            ·
              refine ⟨9321461552514502064663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 99428923226821355356405 9321461552514502064663)
              ·
                rfl

theorem cell19_91902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 5].length) (baseStart_91902 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_91902 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_91902 prefixEnd_91902 := by exact prefixLift 91902
  have htrace : WordTrace (prefixWord ++ tailWord_91902) baseStart_91902 baseEnd_91902 := by
    simpa [prefixWord, tailWord_91902, baseEnd_91902] using wordTrace_append hprefix tailTrace_91902
  have hstable : (prefixWord ++ tailWord_91902).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91902).length < 2 ^ (prefixWord ++ tailWord_91902).sum := by decide
  have hdescent : baseEnd_91902 < baseStart_91902 := by decide
  rcases family_descends (prefixWord ++ tailWord_91902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91925 : List Nat := [1, 3, 2, 1, 2, 3, 1, 6]
def baseStart_91925 : Nat := 118140960795 + 91925 * 2 ^ 59
def prefixEnd_91925 : Nat := 4983230072969 + 3 ^ 40 * 91925 * 2
def baseEnd_91925 : Nat := 27971383208686267682815

theorem tailTrace_91925 : CollatzResearch.WordTrace tailWord_91925 prefixEnd_91925 27971383208686267682815 := by
  unfold tailWord_91925
  simp only [CollatzResearch.WordTrace]
  refine ⟨3352780191978899385205229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2235186794652599590136819 3352780191978899385205229)
  ·
    refine ⟨1257292571992087269451961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3352780191978899385205229 1257292571992087269451961)
    ·
      refine ⟨942969428994065452088971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1257292571992087269451961 942969428994065452088971)
      ·
        refine ⟨1414454143491098178133457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 942969428994065452088971 1414454143491098178133457)
        ·
          refine ⟨1060840607618323633600093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1414454143491098178133457 1060840607618323633600093)
          ·
            refine ⟨397815227856871362600035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1060840607618323633600093 397815227856871362600035)
            ·
              refine ⟨596722841785307043900053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 397815227856871362600035 596722841785307043900053)
              ·
                refine ⟨27971383208686267682815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 596722841785307043900053 27971383208686267682815)
                ·
                  rfl

theorem cell19_91925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 6].length) (baseStart_91925 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_91925 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_91925 prefixEnd_91925 := by exact prefixLift 91925
  have htrace : WordTrace (prefixWord ++ tailWord_91925) baseStart_91925 baseEnd_91925 := by
    simpa [prefixWord, tailWord_91925, baseEnd_91925] using wordTrace_append hprefix tailTrace_91925
  have hstable : (prefixWord ++ tailWord_91925).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91925).length < 2 ^ (prefixWord ++ tailWord_91925).sum := by decide
  have hdescent : baseEnd_91925 < baseStart_91925 := by decide
  rcases family_descends (prefixWord ++ tailWord_91925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91961 : List Nat := [1, 2, 1, 7, 1, 7]
def baseStart_91961 : Nat := 118140960795 + 91961 * 2 ^ 59
def prefixEnd_91961 : Nat := 4983230072969 + 3 ^ 40 * 91961 * 2
def baseEnd_91961 : Nat := 3109148606960983431413

theorem tailTrace_91961 : CollatzResearch.WordTrace tailWord_91961 prefixEnd_91961 3109148606960983431413 := by
  unfold tailWord_91961
  simp only [CollatzResearch.WordTrace]
  refine ⟨3354093219848477533515737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2236062146565651689010491 3354093219848477533515737)
  ·
    refine ⟨2515569914886358150136803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3354093219848477533515737 2515569914886358150136803)
    ·
      refine ⟨3773354872329537225205205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2515569914886358150136803 3773354872329537225205205)
      ·
        refine ⟨88438004820223528715747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 3773354872329537225205205 88438004820223528715747)
        ·
          refine ⟨132657007230335293073621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88438004820223528715747 132657007230335293073621)
          ·
            refine ⟨3109148606960983431413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 132657007230335293073621 3109148606960983431413)
            ·
              rfl

theorem cell19_91961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 7].length) (baseStart_91961 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_91961 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_91961 prefixEnd_91961 := by exact prefixLift 91961
  have htrace : WordTrace (prefixWord ++ tailWord_91961) baseStart_91961 baseEnd_91961 := by
    simpa [prefixWord, tailWord_91961, baseEnd_91961] using wordTrace_append hprefix tailTrace_91961
  have hstable : (prefixWord ++ tailWord_91961).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91961).length < 2 ^ (prefixWord ++ tailWord_91961).sum := by decide
  have hdescent : baseEnd_91961 < baseStart_91961 := by decide
  rcases family_descends (prefixWord ++ tailWord_91961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91999 : List Nat := [1, 1, 2, 3, 1, 5, 3, 3]
def baseStart_91999 : Nat := 118140960795 + 91999 * 2 ^ 59
def prefixEnd_91999 : Nat := 4983230072969 + 3 ^ 40 * 91999 * 2
def baseEnd_91999 : Nat := 27993900286276022038169

theorem tailTrace_91999 : CollatzResearch.WordTrace tailWord_91999 prefixEnd_91999 27993900286276022038169 := by
  unfold tailWord_91999
  simp only [CollatzResearch.WordTrace]
  refine ⟨3355479193710810023399051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2236986129140540015599367 3355479193710810023399051)
  ·
    refine ⟨5033218790566215035098577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3355479193710810023399051 5033218790566215035098577)
    ·
      refine ⟨3774914092924661276323933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5033218790566215035098577 3774914092924661276323933)
      ·
        refine ⟨1415592784846747978621475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3774914092924661276323933 1415592784846747978621475)
        ·
          refine ⟨2123389177270121967932213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1415592784846747978621475 2123389177270121967932213)
          ·
            refine ⟨199067735369073934493645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2123389177270121967932213 199067735369073934493645)
            ·
              refine ⟨74650400763402725435117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 199067735369073934493645 74650400763402725435117)
              ·
                refine ⟨27993900286276022038169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74650400763402725435117 27993900286276022038169)
                ·
                  rfl

theorem cell19_91999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 3, 3].length) (baseStart_91999 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_91999 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_91999 prefixEnd_91999 := by exact prefixLift 91999
  have htrace : WordTrace (prefixWord ++ tailWord_91999) baseStart_91999 baseEnd_91999 := by
    simpa [prefixWord, tailWord_91999, baseEnd_91999] using wordTrace_append hprefix tailTrace_91999
  have hstable : (prefixWord ++ tailWord_91999).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91999).length < 2 ^ (prefixWord ++ tailWord_91999).sum := by decide
  have hdescent : baseEnd_91999 < baseStart_91999 := by decide
  rcases family_descends (prefixWord ++ tailWord_91999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92092 : List Nat := [2, 2, 2, 5, 1, 1, 2, 4]
def baseStart_92092 : Nat := 118140960795 + 92092 * 2 ^ 59
def prefixEnd_92092 : Nat := 4983230072969 + 3 ^ 40 * 92092 * 2
def baseEnd_92092 : Nat := 28022198775679361971249

theorem tailTrace_92092 : CollatzResearch.WordTrace tailWord_92092 prefixEnd_92092 28022198775679361971249 := by
  unfold tailWord_92092
  simp only [CollatzResearch.WordTrace]
  refine ⟨1679435591186943453267265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2239247454915924604356353 1679435591186943453267265)
  ·
    refine ⟨1259576693390207589950449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1679435591186943453267265 1259576693390207589950449)
    ·
      refine ⟨944682520042655692462837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1259576693390207589950449 944682520042655692462837)
      ·
        refine ⟨88563986253998971168391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 944682520042655692462837 88563986253998971168391)
        ·
          refine ⟨132845979380998456752587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88563986253998971168391 132845979380998456752587)
          ·
            refine ⟨199268969071497685128881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132845979380998456752587 199268969071497685128881)
            ·
              refine ⟨149451726803623263846661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 199268969071497685128881 149451726803623263846661)
              ·
                refine ⟨28022198775679361971249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 149451726803623263846661 28022198775679361971249)
                ·
                  rfl

theorem cell19_92092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 2, 4].length) (baseStart_92092 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_92092 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_92092 prefixEnd_92092 := by exact prefixLift 92092
  have htrace : WordTrace (prefixWord ++ tailWord_92092) baseStart_92092 baseEnd_92092 := by
    simpa [prefixWord, tailWord_92092, baseEnd_92092] using wordTrace_append hprefix tailTrace_92092
  have hstable : (prefixWord ++ tailWord_92092).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92092).length < 2 ^ (prefixWord ++ tailWord_92092).sum := by decide
  have hdescent : baseEnd_92092 < baseStart_92092 := by decide
  rcases family_descends (prefixWord ++ tailWord_92092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92094 : List Nat := [4, 2, 1, 1, 1, 4, 2, 4]
def baseStart_92094 : Nat := 118140960795 + 92094 * 2 ^ 59
def prefixEnd_92094 : Nat := 4983230072969 + 3 ^ 40 * 92094 * 2
def baseEnd_92094 : Nat := 28022807345343949926799

theorem tailTrace_92094 : CollatzResearch.WordTrace tailWord_92094 prefixEnd_92094 28022807345343949926799 := by
  unfold tailWord_92094
  simp only [CollatzResearch.WordTrace]
  refine ⟨419868016045830156013417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2239296085577760832071557 419868016045830156013417)
  ·
    refine ⟨314901012034372617010063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 419868016045830156013417 314901012034372617010063)
    ·
      refine ⟨472351518051558925515095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 314901012034372617010063 472351518051558925515095)
      ·
        refine ⟨708527277077338388272643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 472351518051558925515095 708527277077338388272643)
        ·
          refine ⟨1062790915616007582408965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 708527277077338388272643 1062790915616007582408965)
          ·
            refine ⟨199273296678001421701681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1062790915616007582408965 199273296678001421701681)
            ·
              refine ⟨149454972508501066276261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 199273296678001421701681 149454972508501066276261)
              ·
                refine ⟨28022807345343949926799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 149454972508501066276261 28022807345343949926799)
                ·
                  rfl

theorem cell19_92094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 2, 4].length) (baseStart_92094 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_92094 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_92094 prefixEnd_92094 := by exact prefixLift 92094
  have htrace : WordTrace (prefixWord ++ tailWord_92094) baseStart_92094 baseEnd_92094 := by
    simpa [prefixWord, tailWord_92094, baseEnd_92094] using wordTrace_append hprefix tailTrace_92094
  have hstable : (prefixWord ++ tailWord_92094).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92094).length < 2 ^ (prefixWord ++ tailWord_92094).sum := by decide
  have hdescent : baseEnd_92094 < baseStart_92094 := by decide
  rcases family_descends (prefixWord ++ tailWord_92094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92096 : List Nat := [2, 1, 1, 2, 3, 2, 4, 4]
def baseStart_92096 : Nat := 118140960795 + 92096 * 2 ^ 59
def prefixEnd_92096 : Nat := 4983230072969 + 3 ^ 40 * 92096 * 2
def baseEnd_92096 : Nat := 28023415915008537882349

theorem tailTrace_92096 : CollatzResearch.WordTrace tailWord_92096 prefixEnd_92096 28023415915008537882349 := by
  unfold tailWord_92096
  simp only [CollatzResearch.WordTrace]
  refine ⟨1679508537179697794840071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2239344716239597059786761 1679508537179697794840071)
  ·
    refine ⟨2519262805769546692260107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1679508537179697794840071 2519262805769546692260107)
    ·
      refine ⟨3778894208654320038390161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2519262805769546692260107 3778894208654320038390161)
      ·
        refine ⟨2834170656490740028792621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3778894208654320038390161 2834170656490740028792621)
        ·
          refine ⟨1062813996184027510797233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2834170656490740028792621 1062813996184027510797233)
          ·
            refine ⟨797110497138020633097925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1062813996184027510797233 797110497138020633097925)
            ·
              refine ⟨149458218213378868705861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 797110497138020633097925 149458218213378868705861)
              ·
                refine ⟨28023415915008537882349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 149458218213378868705861 28023415915008537882349)
                ·
                  rfl

theorem cell19_92096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 4, 4].length) (baseStart_92096 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_92096 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_92096 prefixEnd_92096 := by exact prefixLift 92096
  have htrace : WordTrace (prefixWord ++ tailWord_92096) baseStart_92096 baseEnd_92096 := by
    simpa [prefixWord, tailWord_92096, baseEnd_92096] using wordTrace_append hprefix tailTrace_92096
  have hstable : (prefixWord ++ tailWord_92096).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92096).length < 2 ^ (prefixWord ++ tailWord_92096).sum := by decide
  have hdescent : baseEnd_92096 < baseStart_92096 := by decide
  rcases family_descends (prefixWord ++ tailWord_92096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92130 : List Nat := [3, 3, 3, 1, 3, 6]
def baseStart_92130 : Nat := 118140960795 + 92130 * 2 ^ 59
def prefixEnd_92130 : Nat := 4983230072969 + 3 ^ 40 * 92130 * 2
def baseEnd_92130 : Nat := 3114862399922948125189

theorem tailTrace_92130 : CollatzResearch.WordTrace tailWord_92130 prefixEnd_92130 3114862399922948125189 := by
  unfold tailWord_92130
  simp only [CollatzResearch.WordTrace]
  refine ⟨840064289059054849104461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2240171437490812930945229 840064289059054849104461)
  ·
    refine ⟨315024108397145568414173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 840064289059054849104461 315024108397145568414173)
    ·
      refine ⟨118134040648929588155315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 315024108397145568414173 118134040648929588155315)
      ·
        refine ⟨177201060973394382232973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118134040648929588155315 177201060973394382232973)
        ·
          refine ⟨66450397865022893337365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 177201060973394382232973 66450397865022893337365)
          ·
            refine ⟨3114862399922948125189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 66450397865022893337365 3114862399922948125189)
            ·
              rfl

theorem cell19_92130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 6].length) (baseStart_92130 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_92130 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_92130 prefixEnd_92130 := by exact prefixLift 92130
  have htrace : WordTrace (prefixWord ++ tailWord_92130) baseStart_92130 baseEnd_92130 := by
    simpa [prefixWord, tailWord_92130, baseEnd_92130] using wordTrace_append hprefix tailTrace_92130
  have hstable : (prefixWord ++ tailWord_92130).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92130).length < 2 ^ (prefixWord ++ tailWord_92130).sum := by decide
  have hdescent : baseEnd_92130 < baseStart_92130 := by decide
  rcases family_descends (prefixWord ++ tailWord_92130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92153 : List Nat := [1, 2, 1, 3, 1, 4, 3, 4]
def baseStart_92153 : Nat := 118140960795 + 92153 * 2 ^ 59
def prefixEnd_92153 : Nat := 4983230072969 + 3 ^ 40 * 92153 * 2
def baseEnd_92153 : Nat := 28040760150449294615527

theorem tailTrace_92153 : CollatzResearch.WordTrace tailWord_92153 prefixEnd_92153 28040760150449294615527 := by
  unfold tailWord_92153
  simp only [CollatzResearch.WordTrace]
  refine ⟨3361096035152894324505113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2240730690101929549670075 3361096035152894324505113)
  ·
    refine ⟨2520822026364670743378835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3361096035152894324505113 2520822026364670743378835)
    ·
      refine ⟨3781233039547006115068253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2520822026364670743378835 3781233039547006115068253)
      ·
        refine ⟨1417962389830127293150595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3781233039547006115068253 1417962389830127293150595)
        ·
          refine ⟨2126943584745190939725893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1417962389830127293150595 2126943584745190939725893)
          ·
            refine ⟨398801922139723301198605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2126943584745190939725893 398801922139723301198605)
            ·
              refine ⟨149550720802396237949477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 398801922139723301198605 149550720802396237949477)
              ·
                refine ⟨28040760150449294615527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 149550720802396237949477 28040760150449294615527)
                ·
                  rfl

theorem cell19_92153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 3, 4].length) (baseStart_92153 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_92153 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_92153 prefixEnd_92153 := by exact prefixLift 92153
  have htrace : WordTrace (prefixWord ++ tailWord_92153) baseStart_92153 baseEnd_92153 := by
    simpa [prefixWord, tailWord_92153, baseEnd_92153] using wordTrace_append hprefix tailTrace_92153
  have hstable : (prefixWord ++ tailWord_92153).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92153).length < 2 ^ (prefixWord ++ tailWord_92153).sum := by decide
  have hdescent : baseEnd_92153 < baseStart_92153 := by decide
  rcases family_descends (prefixWord ++ tailWord_92153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92225 : List Nat := [1, 2, 5, 1, 2, 3, 2, 3]
def baseStart_92225 : Nat := 118140960795 + 92225 * 2 ^ 59
def prefixEnd_92225 : Nat := 4983230072969 + 3 ^ 40 * 92225 * 2
def baseEnd_92225 : Nat := 28062668658374461015331

theorem tailTrace_92225 : CollatzResearch.WordTrace tailWord_92225 prefixEnd_92225 28062668658374461015331 := by
  unfold tailWord_92225
  simp only [CollatzResearch.WordTrace]
  refine ⟨3363722090892050621126129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2242481393928033747417419 3363722090892050621126129)
  ·
    refine ⟨2522791568169037965844597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3363722090892050621126129 2522791568169037965844597)
    ·
      refine ⟨236511709515847309297931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2522791568169037965844597 236511709515847309297931)
      ·
        refine ⟨354767564273770963946897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 236511709515847309297931 354767564273770963946897)
        ·
          refine ⟨266075673205328222960173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 354767564273770963946897 266075673205328222960173)
          ·
            refine ⟨99778377451998083610065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 266075673205328222960173 99778377451998083610065)
            ·
              refine ⟨74833783088998562707549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99778377451998083610065 74833783088998562707549)
              ·
                refine ⟨28062668658374461015331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74833783088998562707549 28062668658374461015331)
                ·
                  rfl

theorem cell19_92225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 2, 3].length) (baseStart_92225 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_92225 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_92225 prefixEnd_92225 := by exact prefixLift 92225
  have htrace : WordTrace (prefixWord ++ tailWord_92225) baseStart_92225 baseEnd_92225 := by
    simpa [prefixWord, tailWord_92225, baseEnd_92225] using wordTrace_append hprefix tailTrace_92225
  have hstable : (prefixWord ++ tailWord_92225).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92225).length < 2 ^ (prefixWord ++ tailWord_92225).sum := by decide
  have hdescent : baseEnd_92225 < baseStart_92225 := by decide
  rcases family_descends (prefixWord ++ tailWord_92225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92248 : List Nat := [2, 1, 2, 2, 1, 6, 5]
def baseStart_92248 : Nat := 118140960795 + 92248 * 2 ^ 59
def prefixEnd_92248 : Nat := 4983230072969 + 3 ^ 40 * 92248 * 2
def baseEnd_92248 : Nat := 9356555736505740834719

theorem tailTrace_92248 : CollatzResearch.WordTrace tailWord_92248 prefixEnd_92248 9356555736505740834719 := by
  unfold tailWord_92248
  simp only [CollatzResearch.WordTrace]
  refine ⟨1682280484904362774606699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2243040646539150366142265 1682280484904362774606699)
  ·
    refine ⟨2523420727356544161910049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1682280484904362774606699 2523420727356544161910049)
    ·
      refine ⟨1892565545517408121432537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2523420727356544161910049 1892565545517408121432537)
      ·
        refine ⟨1419424159138056091074403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1892565545517408121432537 1419424159138056091074403)
        ·
          refine ⟨2129136238707084136611605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1419424159138056091074403 2129136238707084136611605)
          ·
            refine ⟨99803261189394568903669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 2129136238707084136611605 99803261189394568903669)
            ·
              refine ⟨9356555736505740834719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 99803261189394568903669 9356555736505740834719)
              ·
                rfl

theorem cell19_92248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 5].length) (baseStart_92248 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_92248 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_92248 prefixEnd_92248 := by exact prefixLift 92248
  have htrace : WordTrace (prefixWord ++ tailWord_92248) baseStart_92248 baseEnd_92248 := by
    simpa [prefixWord, tailWord_92248, baseEnd_92248] using wordTrace_append hprefix tailTrace_92248
  have hstable : (prefixWord ++ tailWord_92248).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92248).length < 2 ^ (prefixWord ++ tailWord_92248).sum := by decide
  have hdescent : baseEnd_92248 < baseStart_92248 := by decide
  rcases family_descends (prefixWord ++ tailWord_92248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92318 : List Nat := [4, 3, 1, 1, 4, 1, 1, 4]
def baseStart_92318 : Nat := 118140960795 + 92318 * 2 ^ 59
def prefixEnd_92318 : Nat := 4983230072969 + 3 ^ 40 * 92318 * 2
def baseEnd_92318 : Nat := 28090967147777800948411

theorem tailTrace_92318 : CollatzResearch.WordTrace tailWord_92318 prefixEnd_92318 28090967147777800948411 := by
  unfold tailWord_92318
  simp only [CollatzResearch.WordTrace]
  refine ⟨420889259944390938032701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2244742719703418336174405 420889259944390938032701)
  ·
    refine ⟨157833472479146601762263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 420889259944390938032701 157833472479146601762263)
    ·
      refine ⟨236750208718719902643395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157833472479146601762263 236750208718719902643395)
      ·
        refine ⟨355125313078079853965093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 236750208718719902643395 355125313078079853965093)
        ·
          refine ⟨66585996202139972618455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 355125313078079853965093 66585996202139972618455)
          ·
            refine ⟨99878994303209958927683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66585996202139972618455 99878994303209958927683)
            ·
              refine ⟨149818491454814938391525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99878994303209958927683 149818491454814938391525)
              ·
                refine ⟨28090967147777800948411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 149818491454814938391525 28090967147777800948411)
                ·
                  rfl

theorem cell19_92318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 1, 4].length) (baseStart_92318 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_92318 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_92318 prefixEnd_92318 := by exact prefixLift 92318
  have htrace : WordTrace (prefixWord ++ tailWord_92318) baseStart_92318 baseEnd_92318 := by
    simpa [prefixWord, tailWord_92318, baseEnd_92318] using wordTrace_append hprefix tailTrace_92318
  have hstable : (prefixWord ++ tailWord_92318).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92318).length < 2 ^ (prefixWord ++ tailWord_92318).sum := by decide
  have hdescent : baseEnd_92318 < baseStart_92318 := by decide
  rcases family_descends (prefixWord ++ tailWord_92318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92322 : List Nat := [3, 3, 1, 3, 1, 1, 3, 4]
def baseStart_92322 : Nat := 118140960795 + 92322 * 2 ^ 59
def prefixEnd_92322 : Nat := 4983230072969 + 3 ^ 40 * 92322 * 2
def baseEnd_92322 : Nat := 28092184287106976859511

theorem tailTrace_92322 : CollatzResearch.WordTrace tailWord_92322 prefixEnd_92322 28092184287106976859511 := by
  unfold tailWord_92322
  simp only [CollatzResearch.WordTrace]
  refine ⟨841814992885159046851805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2244839981027090791604813 841814992885159046851805)
  ·
    refine ⟨315680622331934642569427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 841814992885159046851805 315680622331934642569427)
    ·
      refine ⟨473520933497901963854141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 315680622331934642569427 473520933497901963854141)
      ·
        refine ⟨177570350061713236445303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 473520933497901963854141 177570350061713236445303)
        ·
          refine ⟨266355525092569854667955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177570350061713236445303 266355525092569854667955)
          ·
            refine ⟨399533287638854782001933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 266355525092569854667955 399533287638854782001933)
            ·
              refine ⟨149824982864570543250725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 399533287638854782001933 149824982864570543250725)
              ·
                refine ⟨28092184287106976859511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 149824982864570543250725 28092184287106976859511)
                ·
                  rfl

theorem cell19_92322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 3, 4].length) (baseStart_92322 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_92322 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_92322 prefixEnd_92322 := by exact prefixLift 92322
  have htrace : WordTrace (prefixWord ++ tailWord_92322) baseStart_92322 baseEnd_92322 := by
    simpa [prefixWord, tailWord_92322, baseEnd_92322] using wordTrace_append hprefix tailTrace_92322
  have hstable : (prefixWord ++ tailWord_92322).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92322).length < 2 ^ (prefixWord ++ tailWord_92322).sum := by decide
  have hdescent : baseEnd_92322 < baseStart_92322 := by decide
  rcases family_descends (prefixWord ++ tailWord_92322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92383 : List Nat := [1, 1, 2, 3, 2, 1, 1, 8]
def baseStart_92383 : Nat := 118140960795 + 92383 * 2 ^ 59
def prefixEnd_92383 : Nat := 4983230072969 + 3 ^ 40 * 92383 * 2
def baseEnd_92383 : Nat := 28110745661876909503789

theorem tailTrace_92383 : CollatzResearch.WordTrace tailWord_92383 prefixEnd_92383 28110745661876909503789 := by
  unfold tailWord_92383
  simp only [CollatzResearch.WordTrace]
  refine ⟨3369484824319643605377803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2246323216213095736918535 3369484824319643605377803)
  ·
    refine ⟨5054227236479465408066705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3369484824319643605377803 5054227236479465408066705)
    ·
      refine ⟨3790670427359599056050029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5054227236479465408066705 3790670427359599056050029)
      ·
        refine ⟨1421501410259849646018761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3790670427359599056050029 1421501410259849646018761)
        ·
          refine ⟨1066126057694887234514071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1421501410259849646018761 1066126057694887234514071)
          ·
            refine ⟨1599189086542330851771107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1066126057694887234514071 1599189086542330851771107)
            ·
              refine ⟨2398783629813496277656661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1599189086542330851771107 2398783629813496277656661)
              ·
                refine ⟨28110745661876909503789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2398783629813496277656661 28110745661876909503789)
                ·
                  rfl

theorem cell19_92383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 8].length) (baseStart_92383 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_92383 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_92383 prefixEnd_92383 := by exact prefixLift 92383
  have htrace : WordTrace (prefixWord ++ tailWord_92383) baseStart_92383 baseEnd_92383 := by
    simpa [prefixWord, tailWord_92383, baseEnd_92383] using wordTrace_append hprefix tailTrace_92383
  have hstable : (prefixWord ++ tailWord_92383).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92383).length < 2 ^ (prefixWord ++ tailWord_92383).sum := by decide
  have hdescent : baseEnd_92383 < baseStart_92383 := by decide
  rcases family_descends (prefixWord ++ tailWord_92383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92512 : List Nat := [2, 1, 1, 3, 5, 1, 3, 3]
def baseStart_92512 : Nat := 118140960795 + 92512 * 2 ^ 59
def prefixEnd_92512 : Nat := 4983230072969 + 3 ^ 40 * 92512 * 2
def baseEnd_92512 : Nat := 28149998405242832636771

theorem tailTrace_92512 : CollatzResearch.WordTrace tailWord_92512 prefixEnd_92512 28149998405242832636771 := by
  unfold tailWord_92512
  simp only [CollatzResearch.WordTrace]
  refine ⟨1687094920426149318411895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2249459893901532424549193 1687094920426149318411895)
  ·
    refine ⟨2530642380639223977617843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1687094920426149318411895 2530642380639223977617843)
    ·
      refine ⟨3795963570958835966426765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2530642380639223977617843 3795963570958835966426765)
      ·
        refine ⟨1423486339109563487410037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3795963570958835966426765 1423486339109563487410037)
        ·
          refine ⟨133451844291521576944691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1423486339109563487410037 133451844291521576944691)
          ·
            refine ⟨200177766437282365417037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133451844291521576944691 200177766437282365417037)
            ·
              refine ⟨75066662413980887031389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 200177766437282365417037 75066662413980887031389)
              ·
                refine ⟨28149998405242832636771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 75066662413980887031389 28149998405242832636771)
                ·
                  rfl

theorem cell19_92512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 3, 3].length) (baseStart_92512 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_92512 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_92512 prefixEnd_92512 := by exact prefixLift 92512
  have htrace : WordTrace (prefixWord ++ tailWord_92512) baseStart_92512 baseEnd_92512 := by
    simpa [prefixWord, tailWord_92512, baseEnd_92512] using wordTrace_append hprefix tailTrace_92512
  have hstable : (prefixWord ++ tailWord_92512).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92512).length < 2 ^ (prefixWord ++ tailWord_92512).sum := by decide
  have hdescent : baseEnd_92512 < baseStart_92512 := by decide
  rcases family_descends (prefixWord ++ tailWord_92512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92533 : List Nat := [1, 3, 4, 1, 2, 2, 6]
def baseStart_92533 : Nat := 118140960795 + 92533 * 2 ^ 59
def prefixEnd_92533 : Nat := 4983230072969 + 3 ^ 40 * 92533 * 2
def baseEnd_92533 : Nat := 9385462795573668723349

theorem tailTrace_92533 : CollatzResearch.WordTrace tailWord_92533 prefixEnd_92533 9385462795573668723349 := by
  unfold tailWord_92533
  simp only [CollatzResearch.WordTrace]
  refine ⟨3374955773776219223338253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2249970515850812815558835 3374955773776219223338253)
  ·
    refine ⟨1265608415166082208751845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3374955773776219223338253 1265608415166082208751845)
    ·
      refine ⟨237301577843640414140971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1265608415166082208751845 237301577843640414140971)
      ·
        refine ⟨355952366765460621211457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237301577843640414140971 355952366765460621211457)
        ·
          refine ⟨266964275074095465908593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 355952366765460621211457 266964275074095465908593)
          ·
            refine ⟨200223206305571599431445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 266964275074095465908593 200223206305571599431445)
            ·
              refine ⟨9385462795573668723349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 200223206305571599431445 9385462795573668723349)
              ·
                rfl

theorem cell19_92533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 6].length) (baseStart_92533 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_92533 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_92533 prefixEnd_92533 := by exact prefixLift 92533
  have htrace : WordTrace (prefixWord ++ tailWord_92533) baseStart_92533 baseEnd_92533 := by
    simpa [prefixWord, tailWord_92533, baseEnd_92533] using wordTrace_append hprefix tailTrace_92533
  have hstable : (prefixWord ++ tailWord_92533).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92533).length < 2 ^ (prefixWord ++ tailWord_92533).sum := by decide
  have hdescent : baseEnd_92533 < baseStart_92533 := by decide
  rcases family_descends (prefixWord ++ tailWord_92533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92628 : List Nat := [2, 4, 1, 2, 2, 1, 2, 5]
def baseStart_92628 : Nat := 118140960795 + 92628 * 2 ^ 59
def prefixEnd_92628 : Nat := 4983230072969 + 3 ^ 40 * 92628 * 2
def baseEnd_92628 : Nat := 28185295445788934058677

theorem tailTrace_92628 : CollatzResearch.WordTrace tailWord_92628 prefixEnd_92628 28185295445788934058677 := by
  unfold tailWord_92628
  simp only [CollatzResearch.WordTrace]
  refine ⟨1689210354216025224023269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2252280472288033632031025 1689210354216025224023269)
  ·
    refine ⟨316726941415504729504363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1689210354216025224023269 316726941415504729504363)
    ·
      refine ⟨475090412123257094256545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 316726941415504729504363 475090412123257094256545)
      ·
        refine ⟨356317809092442820692409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 475090412123257094256545 356317809092442820692409)
        ·
          refine ⟨267238356819332115519307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 356317809092442820692409 267238356819332115519307)
          ·
            refine ⟨400857535228998173278961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 267238356819332115519307 400857535228998173278961)
            ·
              refine ⟨300643151421748629959221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 400857535228998173278961 300643151421748629959221)
              ·
                refine ⟨28185295445788934058677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 300643151421748629959221 28185295445788934058677)
                ·
                  rfl

theorem cell19_92628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 5].length) (baseStart_92628 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_92628 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_92628 prefixEnd_92628 := by exact prefixLift 92628
  have htrace : WordTrace (prefixWord ++ tailWord_92628) baseStart_92628 baseEnd_92628 := by
    simpa [prefixWord, tailWord_92628, baseEnd_92628] using wordTrace_append hprefix tailTrace_92628
  have hstable : (prefixWord ++ tailWord_92628).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92628).length < 2 ^ (prefixWord ++ tailWord_92628).sum := by decide
  have hdescent : baseEnd_92628 < baseStart_92628 := by decide
  rcases family_descends (prefixWord ++ tailWord_92628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92704 : List Nat := [2, 1, 1, 6, 2, 1, 6]
def baseStart_92704 : Nat := 118140960795 + 92704 * 2 ^ 59
def prefixEnd_92704 : Nat := 4983230072969 + 3 ^ 40 * 92704 * 2
def baseEnd_92704 : Nat := 9402807031014425456527

theorem tailTrace_92704 : CollatzResearch.WordTrace tailWord_92704 prefixEnd_92704 9402807031014425456527 := by
  unfold tailWord_92704
  simp only [CollatzResearch.WordTrace]
  refine ⟨1690596328078357713906583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2254128437437810285208777 1690596328078357713906583)
  ·
    refine ⟨2535894492117536570859875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1690596328078357713906583 2535894492117536570859875)
    ·
      refine ⟨3803841738176304856289813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2535894492117536570859875 3803841738176304856289813)
      ·
        refine ⟨178305081477014290138585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 3803841738176304856289813 178305081477014290138585)
        ·
          refine ⟨133728811107760717603939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 178305081477014290138585 133728811107760717603939)
          ·
            refine ⟨200593216661641076405909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133728811107760717603939 200593216661641076405909)
            ·
              refine ⟨9402807031014425456527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 200593216661641076405909 9402807031014425456527)
              ·
                rfl

theorem cell19_92704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 6].length) (baseStart_92704 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_92704 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_92704 prefixEnd_92704 := by exact prefixLift 92704
  have htrace : WordTrace (prefixWord ++ tailWord_92704) baseStart_92704 baseEnd_92704 := by
    simpa [prefixWord, tailWord_92704, baseEnd_92704] using wordTrace_append hprefix tailTrace_92704
  have hstable : (prefixWord ++ tailWord_92704).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92704).length < 2 ^ (prefixWord ++ tailWord_92704).sum := by decide
  have hdescent : baseEnd_92704 < baseStart_92704 := by decide
  rcases family_descends (prefixWord ++ tailWord_92704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92725 : List Nat := [1, 3, 3, 1, 1, 2, 2, 6]
def baseStart_92725 : Nat := 118140960795 + 92725 * 2 ^ 59
def prefixEnd_92725 : Nat := 4983230072969 + 3 ^ 40 * 92725 * 2
def baseEnd_92725 : Nat := 28214811074521449902857

theorem tailTrace_92725 : CollatzResearch.WordTrace tailWord_92725 prefixEnd_92725 28214811074521449902857 := by
  unfold tailWord_92725
  simp only [CollatzResearch.WordTrace]
  refine ⟨3381958589080636014327629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2254639059387090676218419 3381958589080636014327629)
  ·
    refine ⟨1268234470905238505372861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3381958589080636014327629 1268234470905238505372861)
    ·
      refine ⟨475587926589464439514823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1268234470905238505372861 475587926589464439514823)
      ·
        refine ⟨713381889884196659272235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 475587926589464439514823 713381889884196659272235)
        ·
          refine ⟨1070072834826294988908353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 713381889884196659272235 1070072834826294988908353)
          ·
            refine ⟨802554626119721241681265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1070072834826294988908353 802554626119721241681265)
            ·
              refine ⟨601915969589790931260949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 802554626119721241681265 601915969589790931260949)
              ·
                refine ⟨28214811074521449902857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 601915969589790931260949 28214811074521449902857)
                ·
                  rfl

theorem cell19_92725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 6].length) (baseStart_92725 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_92725 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_92725 prefixEnd_92725 := by exact prefixLift 92725
  have htrace : WordTrace (prefixWord ++ tailWord_92725) baseStart_92725 baseEnd_92725 := by
    simpa [prefixWord, tailWord_92725, baseEnd_92725] using wordTrace_append hprefix tailTrace_92725
  have hstable : (prefixWord ++ tailWord_92725).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92725).length < 2 ^ (prefixWord ++ tailWord_92725).sum := by decide
  have hdescent : baseEnd_92725 < baseStart_92725 := by decide
  rcases family_descends (prefixWord ++ tailWord_92725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92801 : List Nat := [1, 2, 4, 2, 1, 1, 1, 7]
def baseStart_92801 : Nat := 118140960795 + 92801 * 2 ^ 59
def prefixEnd_92801 : Nat := 4983230072969 + 3 ^ 40 * 92801 * 2
def baseEnd_92801 : Nat := 28237936721775792213761

theorem tailTrace_92801 : CollatzResearch.WordTrace tailWord_92801 prefixEnd_92801 28237936721775792213761 := by
  unfold tailWord_92801
  simp only [CollatzResearch.WordTrace]
  refine ⟨3384730536805300994094257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2256487024536867329396171 3384730536805300994094257)
  ·
    refine ⟨2538547902603975745570693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3384730536805300994094257 2538547902603975745570693)
    ·
      refine ⟨475977731738245452294505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2538547902603975745570693 475977731738245452294505)
      ·
        refine ⟨356983298803684089220879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 475977731738245452294505 356983298803684089220879)
        ·
          refine ⟨535474948205526133831319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 356983298803684089220879 535474948205526133831319)
          ·
            refine ⟨803212422308289200746979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 535474948205526133831319 803212422308289200746979)
            ·
              refine ⟨1204818633462433801120469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 803212422308289200746979 1204818633462433801120469)
              ·
                refine ⟨28237936721775792213761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1204818633462433801120469 28237936721775792213761)
                ·
                  rfl

theorem cell19_92801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 7].length) (baseStart_92801 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_92801 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_92801 prefixEnd_92801 := by exact prefixLift 92801
  have htrace : WordTrace (prefixWord ++ tailWord_92801) baseStart_92801 baseEnd_92801 := by
    simpa [prefixWord, tailWord_92801, baseEnd_92801] using wordTrace_append hprefix tailTrace_92801
  have hstable : (prefixWord ++ tailWord_92801).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92801).length < 2 ^ (prefixWord ++ tailWord_92801).sum := by decide
  have hdescent : baseEnd_92801 < baseStart_92801 := by decide
  rcases family_descends (prefixWord ++ tailWord_92801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92951 : List Nat := [1, 1, 3, 4, 3, 1, 2, 4]
def baseStart_92951 : Nat := 118140960795 + 92951 * 2 ^ 59
def prefixEnd_92951 : Nat := 4983230072969 + 3 ^ 40 * 92951 * 2
def baseEnd_92951 : Nat := 28283579446619888880019

theorem tailTrace_92951 : CollatzResearch.WordTrace tailWord_92951 prefixEnd_92951 28283579446619888880019 := by
  unfold tailWord_92951
  simp only [CollatzResearch.WordTrace]
  refine ⟨3390201486261876612054707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2260134324174584408036471 3390201486261876612054707)
  ·
    refine ⟨5085302229392814918082061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3390201486261876612054707 5085302229392814918082061)
    ·
      refine ⟨1906988336022305594280773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5085302229392814918082061 1906988336022305594280773)
      ·
        refine ⟨357560313004182298927645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1906988336022305594280773 357560313004182298927645)
        ·
          refine ⟨134085117376568362097867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 357560313004182298927645 134085117376568362097867)
          ·
            refine ⟨201127676064852543146801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134085117376568362097867 201127676064852543146801)
            ·
              refine ⟨150845757048639407360101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 201127676064852543146801 150845757048639407360101)
              ·
                refine ⟨28283579446619888880019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 150845757048639407360101 28283579446619888880019)
                ·
                  rfl

theorem cell19_92951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 2, 4].length) (baseStart_92951 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_92951 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_92951 prefixEnd_92951 := by exact prefixLift 92951
  have htrace : WordTrace (prefixWord ++ tailWord_92951) baseStart_92951 baseEnd_92951 := by
    simpa [prefixWord, tailWord_92951, baseEnd_92951] using wordTrace_append hprefix tailTrace_92951
  have hstable : (prefixWord ++ tailWord_92951).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92951).length < 2 ^ (prefixWord ++ tailWord_92951).sum := by decide
  have hdescent : baseEnd_92951 < baseStart_92951 := by decide
  rcases family_descends (prefixWord ++ tailWord_92951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92989 : List Nat := [1, 4, 1, 4, 3, 6]
def baseStart_92989 : Nat := 118140960795 + 92989 * 2 ^ 59
def prefixEnd_92989 : Nat := 4983230072969 + 3 ^ 40 * 92989 * 2
def baseEnd_92989 : Nat := 3143904696694117781719

theorem tailTrace_92989 : CollatzResearch.WordTrace tailWord_92989 prefixEnd_92989 3143904696694117781719 := by
  unfold tailWord_92989
  simp only [CollatzResearch.WordTrace]
  refine ⟨3391587460124209101938021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2261058306749472734625347 3391587460124209101938021)
  ·
    refine ⟨635922648773289206613379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3391587460124209101938021 635922648773289206613379)
    ·
      refine ⟨953883973159933809920069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 635922648773289206613379 953883973159933809920069)
      ·
        refine ⟨178853244967487589360013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 953883973159933809920069 178853244967487589360013)
        ·
          refine ⟨67069966862807846010005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 178853244967487589360013 67069966862807846010005)
          ·
            refine ⟨3143904696694117781719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 67069966862807846010005 3143904696694117781719)
            ·
              rfl

theorem cell19_92989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 6].length) (baseStart_92989 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_92989 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_92989 prefixEnd_92989 := by exact prefixLift 92989
  have htrace : WordTrace (prefixWord ++ tailWord_92989) baseStart_92989 baseEnd_92989 := by
    simpa [prefixWord, tailWord_92989, baseEnd_92989] using wordTrace_append hprefix tailTrace_92989
  have hstable : (prefixWord ++ tailWord_92989).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92989).length < 2 ^ (prefixWord ++ tailWord_92989).sum := by decide
  have hdescent : baseEnd_92989 < baseStart_92989 := by decide
  rcases family_descends (prefixWord ++ tailWord_92989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93027 : List Nat := [1, 1, 1, 5, 3, 2, 3, 3]
def baseStart_93027 : Nat := 118140960795 + 93027 * 2 ^ 59
def prefixEnd_93027 : Nat := 4983230072969 + 3 ^ 40 * 93027 * 2
def baseEnd_93027 : Nat := 28306705093874231190923

theorem tailTrace_93027 : CollatzResearch.WordTrace tailWord_93027 prefixEnd_93027 28306705093874231190923 := by
  unfold tailWord_93027
  simp only [CollatzResearch.WordTrace]
  refine ⟨3392973433986541591821335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2261982289324361061214223 3392973433986541591821335)
  ·
    refine ⟨5089460150979812387732003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3392973433986541591821335 5089460150979812387732003)
    ·
      refine ⟨7634190226469718581598005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5089460150979812387732003 7634190226469718581598005)
      ·
        refine ⟨715705333731536117024813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7634190226469718581598005 715705333731536117024813)
        ·
          refine ⟨268389500149326043884305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 715705333731536117024813 268389500149326043884305)
          ·
            refine ⟨201292125111994532913229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 268389500149326043884305 201292125111994532913229)
            ·
              refine ⟨75484546916997949842461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 201292125111994532913229 75484546916997949842461)
              ·
                refine ⟨28306705093874231190923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 75484546916997949842461 28306705093874231190923)
                ·
                  rfl

theorem cell19_93027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 3, 3].length) (baseStart_93027 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_93027 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_93027 prefixEnd_93027 := by exact prefixLift 93027
  have htrace : WordTrace (prefixWord ++ tailWord_93027) baseStart_93027 baseEnd_93027 := by
    simpa [prefixWord, tailWord_93027, baseEnd_93027] using wordTrace_append hprefix tailTrace_93027
  have hstable : (prefixWord ++ tailWord_93027).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93027).length < 2 ^ (prefixWord ++ tailWord_93027).sum := by decide
  have hdescent : baseEnd_93027 < baseStart_93027 := by decide
  rcases family_descends (prefixWord ++ tailWord_93027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93046 : List Nat := [5, 1, 1, 3, 1, 2, 6]
def baseStart_93046 : Nat := 118140960795 + 93046 * 2 ^ 59
def prefixEnd_93046 : Nat := 4983230072969 + 3 ^ 40 * 93046 * 2
def baseEnd_93046 : Nat := 9437495501895938922883

theorem tailTrace_93046 : CollatzResearch.WordTrace tailWord_93046 prefixEnd_93046 9437495501895938922883 := by
  unfold tailWord_93046
  simp only [CollatzResearch.WordTrace]
  refine ⟨212104151307356739797687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2262444280611805224508661 212104151307356739797687)
  ·
    refine ⟨318156226961035109696531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212104151307356739797687 318156226961035109696531)
    ·
      refine ⟨477234340441552664544797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 318156226961035109696531 477234340441552664544797)
      ·
        refine ⟨178962877665582249204299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 477234340441552664544797 178962877665582249204299)
        ·
          refine ⟨268444316498373373806449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178962877665582249204299 268444316498373373806449)
          ·
            refine ⟨201333237373780030354837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 268444316498373373806449 201333237373780030354837)
            ·
              refine ⟨9437495501895938922883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 201333237373780030354837 9437495501895938922883)
              ·
                rfl

theorem cell19_93046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 6].length) (baseStart_93046 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_93046 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_93046 prefixEnd_93046 := by exact prefixLift 93046
  have htrace : WordTrace (prefixWord ++ tailWord_93046) baseStart_93046 baseEnd_93046 := by
    simpa [prefixWord, tailWord_93046, baseEnd_93046] using wordTrace_append hprefix tailTrace_93046
  have hstable : (prefixWord ++ tailWord_93046).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93046).length < 2 ^ (prefixWord ++ tailWord_93046).sum := by decide
  have hdescent : baseEnd_93046 < baseStart_93046 := by decide
  rcases family_descends (prefixWord ++ tailWord_93046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93078 : List Nat := [5, 3, 1, 1, 1, 3, 2, 3]
def baseStart_93078 : Nat := 118140960795 + 93078 * 2 ^ 59
def prefixEnd_93078 : Nat := 4983230072969 + 3 ^ 40 * 93078 * 2
def baseEnd_93078 : Nat := 28322223620321224057451

theorem tailTrace_93078 : CollatzResearch.WordTrace tailWord_93078 prefixEnd_93078 28322223620321224057451 := by
  unfold tailWord_93078
  simp only [CollatzResearch.WordTrace]
  refine ⟨212177097300111081370493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2263222371201184867951925 212177097300111081370493)
  ·
    refine ⟨79566411487541655513935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 212177097300111081370493 79566411487541655513935)
    ·
      refine ⟨119349617231312483270903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79566411487541655513935 119349617231312483270903)
      ·
        refine ⟨179024425846968724906355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119349617231312483270903 179024425846968724906355)
        ·
          refine ⟨268536638770453087359533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179024425846968724906355 268536638770453087359533)
          ·
            refine ⟨100701239538919907759825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 268536638770453087359533 100701239538919907759825)
            ·
              refine ⟨75525929654189930819869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100701239538919907759825 75525929654189930819869)
              ·
                refine ⟨28322223620321224057451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 75525929654189930819869 28322223620321224057451)
                ·
                  rfl

theorem cell19_93078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 2, 3].length) (baseStart_93078 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_93078 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_93078 prefixEnd_93078 := by exact prefixLift 93078
  have htrace : WordTrace (prefixWord ++ tailWord_93078) baseStart_93078 baseEnd_93078 := by
    simpa [prefixWord, tailWord_93078, baseEnd_93078] using wordTrace_append hprefix tailTrace_93078
  have hstable : (prefixWord ++ tailWord_93078).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93078).length < 2 ^ (prefixWord ++ tailWord_93078).sum := by decide
  have hdescent : baseEnd_93078 < baseStart_93078 := by decide
  rcases family_descends (prefixWord ++ tailWord_93078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93082 : List Nat := [3, 1, 1, 4, 3, 2, 2, 3]
def baseStart_93082 : Nat := 118140960795 + 93082 * 2 ^ 59
def prefixEnd_93082 : Nat := 4983230072969 + 3 ^ 40 * 93082 * 2
def baseEnd_93082 : Nat := 28323440759650399968551

theorem tailTrace_93082 : CollatzResearch.WordTrace tailWord_93082 prefixEnd_93082 28323440759650399968551 := by
  unfold tailWord_93082
  simp only [CollatzResearch.WordTrace]
  refine ⟨848744862196821496268375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2263319632524857323382333 848744862196821496268375)
  ·
    refine ⟨1273117293295232244402563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 848744862196821496268375 1273117293295232244402563)
    ·
      refine ⟨1909675939942848366603845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1273117293295232244402563 1909675939942848366603845)
      ·
        refine ⟨358064238739284068738221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1909675939942848366603845 358064238739284068738221)
        ·
          refine ⟨134274089527231525776833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 358064238739284068738221 134274089527231525776833)
          ·
            refine ⟨100705567145423644332625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 134274089527231525776833 100705567145423644332625)
            ·
              refine ⟨75529175359067733249469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100705567145423644332625 75529175359067733249469)
              ·
                refine ⟨28323440759650399968551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 75529175359067733249469 28323440759650399968551)
                ·
                  rfl

theorem cell19_93082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 2, 3].length) (baseStart_93082 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_93082 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_93082 prefixEnd_93082 := by exact prefixLift 93082
  have htrace : WordTrace (prefixWord ++ tailWord_93082) baseStart_93082 baseEnd_93082 := by
    simpa [prefixWord, tailWord_93082, baseEnd_93082] using wordTrace_append hprefix tailTrace_93082
  have hstable : (prefixWord ++ tailWord_93082).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93082).length < 2 ^ (prefixWord ++ tailWord_93082).sum := by decide
  have hdescent : baseEnd_93082 < baseStart_93082 := by decide
  rcases family_descends (prefixWord ++ tailWord_93082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93084 : List Nat := [2, 2, 3, 3, 2, 1, 1, 5]
def baseStart_93084 : Nat := 118140960795 + 93084 * 2 ^ 59
def prefixEnd_93084 : Nat := 4983230072969 + 3 ^ 40 * 93084 * 2
def baseEnd_93084 : Nat := 28324049329314987924101

theorem tailTrace_93084 : CollatzResearch.WordTrace tailWord_93084 prefixEnd_93084 28324049329314987924101 := by
  unfold tailWord_93084
  simp only [CollatzResearch.WordTrace]
  refine ⟨1697526197390020163323153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2263368263186693551097537 1697526197390020163323153)
  ·
    refine ⟨1273144648042515122492365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1697526197390020163323153 1273144648042515122492365)
    ·
      refine ⟨477429243015943170934637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1273144648042515122492365 477429243015943170934637)
      ·
        refine ⟨179035966130978689100489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 477429243015943170934637 179035966130978689100489)
        ·
          refine ⟨134276974598234016825367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 179035966130978689100489 134276974598234016825367)
          ·
            refine ⟨201415461897351025238051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134276974598234016825367 201415461897351025238051)
            ·
              refine ⟨302123192846026537857077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 201415461897351025238051 302123192846026537857077)
              ·
                refine ⟨28324049329314987924101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 302123192846026537857077 28324049329314987924101)
                ·
                  rfl

theorem cell19_93084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 5].length) (baseStart_93084 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_93084 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_93084 prefixEnd_93084 := by exact prefixLift 93084
  have htrace : WordTrace (prefixWord ++ tailWord_93084) baseStart_93084 baseEnd_93084 := by
    simpa [prefixWord, tailWord_93084, baseEnd_93084] using wordTrace_append hprefix tailTrace_93084
  have hstable : (prefixWord ++ tailWord_93084).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93084).length < 2 ^ (prefixWord ++ tailWord_93084).sum := by decide
  have hdescent : baseEnd_93084 < baseStart_93084 := by decide
  rcases family_descends (prefixWord ++ tailWord_93084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93101 : List Nat := [1, 5, 2, 3, 1, 2, 5]
def baseStart_93101 : Nat := 118140960795 + 93101 * 2 ^ 59
def prefixEnd_93101 : Nat := 4983230072969 + 3 ^ 40 * 93101 * 2
def baseEnd_93101 : Nat := 9443074057154661848759

theorem tailTrace_93101 : CollatzResearch.WordTrace tailWord_93101 prefixEnd_93101 9443074057154661848759 := by
  unfold tailWord_93101
  simp only [CollatzResearch.WordTrace]
  refine ⟨3395672435718452230015157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2263781623812301486676771 3395672435718452230015157)
  ·
    refine ⟨318344290848604896563921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3395672435718452230015157 318344290848604896563921)
    ·
      refine ⟨238758218136453672422941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 318344290848604896563921 238758218136453672422941)
      ·
        refine ⟨89534331801170127158603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 238758218136453672422941 89534331801170127158603)
        ·
          refine ⟨134301497701755190737905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89534331801170127158603 134301497701755190737905)
          ·
            refine ⟨100726123276316393053429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 134301497701755190737905 100726123276316393053429)
            ·
              refine ⟨9443074057154661848759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 100726123276316393053429 9443074057154661848759)
              ·
                rfl

theorem cell19_93101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 5].length) (baseStart_93101 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_93101 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_93101 prefixEnd_93101 := by exact prefixLift 93101
  have htrace : WordTrace (prefixWord ++ tailWord_93101) baseStart_93101 baseEnd_93101 := by
    simpa [prefixWord, tailWord_93101, baseEnd_93101] using wordTrace_append hprefix tailTrace_93101
  have hstable : (prefixWord ++ tailWord_93101).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93101).length < 2 ^ (prefixWord ++ tailWord_93101).sum := by decide
  have hdescent : baseEnd_93101 < baseStart_93101 := by decide
  rcases family_descends (prefixWord ++ tailWord_93101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93198 : List Nat := [4, 1, 1, 2, 2, 3, 3, 3]
def baseStart_93198 : Nat := 118140960795 + 93198 * 2 ^ 59
def prefixEnd_93198 : Nat := 4983230072969 + 3 ^ 40 * 93198 * 2
def baseEnd_93198 : Nat := 28358737800196501390457

theorem tailTrace_93198 : CollatzResearch.WordTrace tailWord_93198 prefixEnd_93198 28358737800196501390457 := by
  unfold tailWord_93198
  simp only [CollatzResearch.WordTrace]
  refine ⟨424901289545879724537031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2266140210911358530864165 424901289545879724537031)
  ·
    refine ⟨637351934318819586805547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 424901289545879724537031 637351934318819586805547)
    ·
      refine ⟨956027901478229380208321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 637351934318819586805547 956027901478229380208321)
      ·
        refine ⟨717020926108672035156241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 956027901478229380208321 717020926108672035156241)
        ·
          refine ⟨537765694581504026367181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 717020926108672035156241 537765694581504026367181)
          ·
            refine ⟨201662135468064009887693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 537765694581504026367181 201662135468064009887693)
            ·
              refine ⟨75623300800524003707885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 201662135468064009887693 75623300800524003707885)
              ·
                refine ⟨28358737800196501390457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 75623300800524003707885 28358737800196501390457)
                ·
                  rfl

theorem cell19_93198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 3, 3].length) (baseStart_93198 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_93198 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_93198 prefixEnd_93198 := by exact prefixLift 93198
  have htrace : WordTrace (prefixWord ++ tailWord_93198) baseStart_93198 baseEnd_93198 := by
    simpa [prefixWord, tailWord_93198, baseEnd_93198] using wordTrace_append hprefix tailTrace_93198
  have hstable : (prefixWord ++ tailWord_93198).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93198).length < 2 ^ (prefixWord ++ tailWord_93198).sum := by decide
  have hdescent : baseEnd_93198 < baseStart_93198 := by decide
  rcases family_descends (prefixWord ++ tailWord_93198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93221 : List Nat := [1, 3, 1, 2, 2, 2, 8]
def baseStart_93221 : Nat := 118140960795 + 93221 * 2 ^ 59
def prefixEnd_93221 : Nat := 4983230072969 + 3 ^ 40 * 93221 * 2
def baseEnd_93221 : Nat := 9455245450446420959761

theorem tailTrace_93221 : CollatzResearch.WordTrace tailWord_93221 prefixEnd_93221 9455245450446420959761 := by
  unfold tailWord_93221
  simp only [CollatzResearch.WordTrace]
  refine ⟨3400049195283712724383517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2266699463522475149589011 3400049195283712724383517)
  ·
    refine ⟨1275018448231392271643819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3400049195283712724383517 1275018448231392271643819)
    ·
      refine ⟨1912527672347088407465729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1275018448231392271643819 1912527672347088407465729)
      ·
        refine ⟨1434395754260316305599297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1912527672347088407465729 1434395754260316305599297)
        ·
          refine ⟨1075796815695237229199473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1434395754260316305599297 1075796815695237229199473)
          ·
            refine ⟨806847611771427921899605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1075796815695237229199473 806847611771427921899605)
            ·
              refine ⟨9455245450446420959761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 806847611771427921899605 9455245450446420959761)
              ·
                rfl

theorem cell19_93221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 8].length) (baseStart_93221 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_93221 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_93221 prefixEnd_93221 := by exact prefixLift 93221
  have htrace : WordTrace (prefixWord ++ tailWord_93221) baseStart_93221 baseEnd_93221 := by
    simpa [prefixWord, tailWord_93221, baseEnd_93221] using wordTrace_append hprefix tailTrace_93221
  have hstable : (prefixWord ++ tailWord_93221).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93221).length < 2 ^ (prefixWord ++ tailWord_93221).sum := by decide
  have hdescent : baseEnd_93221 < baseStart_93221 := by decide
  rcases family_descends (prefixWord ++ tailWord_93221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93255 : List Nat := [1, 1, 4, 1, 3, 4, 2, 3]
def baseStart_93255 : Nat := 118140960795 + 93255 * 2 ^ 59
def prefixEnd_93255 : Nat := 4983230072969 + 3 ^ 40 * 93255 * 2
def baseEnd_93255 : Nat := 28376082035637258123635

theorem tailTrace_93255 : CollatzResearch.WordTrace tailWord_93255 prefixEnd_93255 28376082035637258123635 := by
  unfold tailWord_93255
  simp only [CollatzResearch.WordTrace]
  refine ⟨3401289277160536531121219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2267526184773691020747479 3401289277160536531121219)
  ·
    refine ⟨5101933915740804796681829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3401289277160536531121219 5101933915740804796681829)
    ·
      refine ⟨956612609201400899377843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5101933915740804796681829 956612609201400899377843)
      ·
        refine ⟨1434918913802101349066765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 956612609201400899377843 1434918913802101349066765)
        ·
          refine ⟨538094592675788005900037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1434918913802101349066765 538094592675788005900037)
          ·
            refine ⟨100892736126710251106257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 538094592675788005900037 100892736126710251106257)
            ·
              refine ⟨75669552095032688329693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100892736126710251106257 75669552095032688329693)
              ·
                refine ⟨28376082035637258123635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 75669552095032688329693 28376082035637258123635)
                ·
                  rfl

theorem cell19_93255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 2, 3].length) (baseStart_93255 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_93255 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_93255 prefixEnd_93255 := by exact prefixLift 93255
  have htrace : WordTrace (prefixWord ++ tailWord_93255) baseStart_93255 baseEnd_93255 := by
    simpa [prefixWord, tailWord_93255, baseEnd_93255] using wordTrace_append hprefix tailTrace_93255
  have hstable : (prefixWord ++ tailWord_93255).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93255).length < 2 ^ (prefixWord ++ tailWord_93255).sum := by decide
  have hdescent : baseEnd_93255 < baseStart_93255 := by decide
  rcases family_descends (prefixWord ++ tailWord_93255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93270 : List Nat := [5, 2, 2, 1, 3, 1, 5]
def baseStart_93270 : Nat := 118140960795 + 93270 * 2 ^ 59
def prefixEnd_93270 : Nat := 4983230072969 + 3 ^ 40 * 93270 * 2
def baseEnd_93270 : Nat := 9460215436040555930087

theorem tailTrace_93270 : CollatzResearch.WordTrace tailWord_93270 prefixEnd_93270 9460215436040555930087 := by
  unfold tailWord_93270
  simp only [CollatzResearch.WordTrace]
  refine ⟨212614773256637130807329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2267890914737462728611509 212614773256637130807329)
  ·
    refine ⟨159461079942477848105497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212614773256637130807329 159461079942477848105497)
    ·
      refine ⟨119595809956858386079123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159461079942477848105497 119595809956858386079123)
      ·
        refine ⟨179393714935287579118685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119595809956858386079123 179393714935287579118685)
        ·
          refine ⟨67272643100732842169507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 179393714935287579118685 67272643100732842169507)
          ·
            refine ⟨100908964651099263254261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67272643100732842169507 100908964651099263254261)
            ·
              refine ⟨9460215436040555930087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 100908964651099263254261 9460215436040555930087)
              ·
                rfl

theorem cell19_93270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 5].length) (baseStart_93270 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_93270 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_93270 prefixEnd_93270 := by exact prefixLift 93270
  have htrace : WordTrace (prefixWord ++ tailWord_93270) baseStart_93270 baseEnd_93270 := by
    simpa [prefixWord, tailWord_93270, baseEnd_93270] using wordTrace_append hprefix tailTrace_93270
  have hstable : (prefixWord ++ tailWord_93270).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93270).length < 2 ^ (prefixWord ++ tailWord_93270).sum := by decide
  have hdescent : baseEnd_93270 < baseStart_93270 := by decide
  rcases family_descends (prefixWord ++ tailWord_93270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93335 : List Nat := [1, 1, 3, 3, 3, 8]
def baseStart_93335 : Nat := 118140960795 + 93335 * 2 ^ 59
def prefixEnd_93335 : Nat := 4983230072969 + 3 ^ 40 * 93335 * 2
def baseEnd_93335 : Nat := 3155602758024530705071

theorem tailTrace_93335 : CollatzResearch.WordTrace tailWord_93335 prefixEnd_93335 3155602758024530705071 := by
  unfold tailWord_93335
  simp only [CollatzResearch.WordTrace]
  refine ⟨3404207116870710194033459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2269471411247140129355639 3404207116870710194033459)
  ·
    refine ⟨5106310675306065291050189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3404207116870710194033459 5106310675306065291050189)
    ·
      refine ⟨1914866503239774484143821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5106310675306065291050189 1914866503239774484143821)
      ·
        refine ⟨718074938714915431553933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1914866503239774484143821 718074938714915431553933)
        ·
          refine ⟨269278102018093286832725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 718074938714915431553933 269278102018093286832725)
          ·
            refine ⟨3155602758024530705071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 269278102018093286832725 3155602758024530705071)
            ·
              rfl

theorem cell19_93335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 8].length) (baseStart_93335 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_93335 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_93335 prefixEnd_93335 := by exact prefixLift 93335
  have htrace : WordTrace (prefixWord ++ tailWord_93335) baseStart_93335 baseEnd_93335 := by
    simpa [prefixWord, tailWord_93335, baseEnd_93335] using wordTrace_append hprefix tailTrace_93335
  have hstable : (prefixWord ++ tailWord_93335).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93335).length < 2 ^ (prefixWord ++ tailWord_93335).sum := by decide
  have hdescent : baseEnd_93335 < baseStart_93335 := by decide
  rcases family_descends (prefixWord ++ tailWord_93335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93373 : List Nat := [1, 4, 1, 2, 1, 1, 2, 7]
def baseStart_93373 : Nat := 118140960795 + 93373 * 2 ^ 59
def prefixEnd_93373 : Nat := 4983230072969 + 3 ^ 40 * 93373 * 2
def baseEnd_93373 : Nat := 28411987645847947501091

theorem tailTrace_93373 : CollatzResearch.WordTrace tailWord_93373 prefixEnd_93373 28411987645847947501091 := by
  unfold tailWord_93373
  simp only [CollatzResearch.WordTrace]
  refine ⟨3405593090733042683916773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2270395393822028455944515 3405593090733042683916773)
  ·
    refine ⟨638548704512445503234395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3405593090733042683916773 638548704512445503234395)
    ·
      refine ⟨957823056768668254851593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 638548704512445503234395 957823056768668254851593)
      ·
        refine ⟨718367292576501191138695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 957823056768668254851593 718367292576501191138695)
        ·
          refine ⟨1077550938864751786708043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 718367292576501191138695 1077550938864751786708043)
          ·
            refine ⟨1616326408297127680062065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1077550938864751786708043 1616326408297127680062065)
            ·
              refine ⟨1212244806222845760046549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1616326408297127680062065 1212244806222845760046549)
              ·
                refine ⟨28411987645847947501091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1212244806222845760046549 28411987645847947501091)
                ·
                  rfl

theorem cell19_93373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 7].length) (baseStart_93373 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_93373 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_93373 prefixEnd_93373 := by exact prefixLift 93373
  have htrace : WordTrace (prefixWord ++ tailWord_93373) baseStart_93373 baseEnd_93373 := by
    simpa [prefixWord, tailWord_93373, baseEnd_93373] using wordTrace_append hprefix tailTrace_93373
  have hstable : (prefixWord ++ tailWord_93373).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93373).length < 2 ^ (prefixWord ++ tailWord_93373).sum := by decide
  have hdescent : baseEnd_93373 < baseStart_93373 := by decide
  rcases family_descends (prefixWord ++ tailWord_93373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93390 : List Nat := [4, 1, 1, 1, 5, 1, 6]
def baseStart_93390 : Nat := 118140960795 + 93390 * 2 ^ 59
def prefixEnd_93390 : Nat := 4983230072969 + 3 ^ 40 * 93390 * 2
def baseEnd_93390 : Nat := 9472386829332315041089

theorem tailTrace_93390 : CollatzResearch.WordTrace tailWord_93390 prefixEnd_93390 9472386829332315041089 := by
  unfold tailWord_93390
  simp only [CollatzResearch.WordTrace]
  refine ⟨425776641458931823410703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2270808754447636391523749 425776641458931823410703)
  ·
    refine ⟨638664962188397735116055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 425776641458931823410703 638664962188397735116055)
    ·
      refine ⟨957997443282596602674083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 638664962188397735116055 957997443282596602674083)
      ·
        refine ⟨1436996164923894904011125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 957997443282596602674083 1436996164923894904011125)
        ·
          refine ⟨134718390461615147251043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1436996164923894904011125 134718390461615147251043)
          ·
            refine ⟨202077585692422720876565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134718390461615147251043 202077585692422720876565)
            ·
              refine ⟨9472386829332315041089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 202077585692422720876565 9472386829332315041089)
              ·
                rfl

theorem cell19_93390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 6].length) (baseStart_93390 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_93390 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_93390 prefixEnd_93390 := by exact prefixLift 93390
  have htrace : WordTrace (prefixWord ++ tailWord_93390) baseStart_93390 baseEnd_93390 := by
    simpa [prefixWord, tailWord_93390, baseEnd_93390] using wordTrace_append hprefix tailTrace_93390
  have hstable : (prefixWord ++ tailWord_93390).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93390).length < 2 ^ (prefixWord ++ tailWord_93390).sum := by decide
  have hdescent : baseEnd_93390 < baseStart_93390 := by decide
  rcases family_descends (prefixWord ++ tailWord_93390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93466 : List Nat := [3, 1, 1, 3, 3, 2, 2, 4]
def baseStart_93466 : Nat := 118140960795 + 93466 * 2 ^ 59
def prefixEnd_93466 : Nat := 4983230072969 + 3 ^ 40 * 93466 * 2
def baseEnd_93466 : Nat := 28440286135251287434171

theorem tailTrace_93466 : CollatzResearch.WordTrace tailWord_93466 prefixEnd_93466 28440286135251287434171 := by
  unfold tailWord_93466
  simp only [CollatzResearch.WordTrace]
  refine ⟨852246269849029891763063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2272656719597413044701501 852246269849029891763063)
  ·
    refine ⟨1278369404773544837644595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 852246269849029891763063 1278369404773544837644595)
    ·
      refine ⟨1917554107160317256466893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1278369404773544837644595 1917554107160317256466893)
      ·
        refine ⟨719082790185118971175085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1917554107160317256466893 719082790185118971175085)
        ·
          refine ⟨269656046319419614190657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 719082790185118971175085 269656046319419614190657)
          ·
            refine ⟨202242034739564710642993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 269656046319419614190657 202242034739564710642993)
            ·
              refine ⟨151681526054673532982245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 202242034739564710642993 151681526054673532982245)
              ·
                refine ⟨28440286135251287434171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 151681526054673532982245 28440286135251287434171)
                ·
                  rfl

theorem cell19_93466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 2, 4].length) (baseStart_93466 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_93466 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_93466 prefixEnd_93466 := by exact prefixLift 93466
  have htrace : WordTrace (prefixWord ++ tailWord_93466) baseStart_93466 baseEnd_93466 := by
    simpa [prefixWord, tailWord_93466, baseEnd_93466] using wordTrace_append hprefix tailTrace_93466
  have hstable : (prefixWord ++ tailWord_93466).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93466).length < 2 ^ (prefixWord ++ tailWord_93466).sum := by decide
  have hdescent : baseEnd_93466 < baseStart_93466 := by decide
  rcases family_descends (prefixWord ++ tailWord_93466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93468 : List Nat := [2, 2, 3, 1, 1, 1, 3, 6]
def baseStart_93468 : Nat := 118140960795 + 93468 * 2 ^ 59
def prefixEnd_93468 : Nat := 4983230072969 + 3 ^ 40 * 93468 * 2
def baseEnd_93468 : Nat := 28440894704915875389721

theorem tailTrace_93468 : CollatzResearch.WordTrace tailWord_93468 prefixEnd_93468 28440894704915875389721 := by
  unfold tailWord_93468
  simp only [CollatzResearch.WordTrace]
  refine ⟨1704529012694436954312529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2272705350259249272416705 1704529012694436954312529)
  ·
    refine ⟨1278396759520827715734397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1704529012694436954312529 1278396759520827715734397)
    ·
      refine ⟨479398784820310393400399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1278396759520827715734397 479398784820310393400399)
      ·
        refine ⟨719098177230465590100599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 479398784820310393400399 719098177230465590100599)
        ·
          refine ⟨1078647265845698385150899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 719098177230465590100599 1078647265845698385150899)
          ·
            refine ⟨1617970898768547577726349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1078647265845698385150899 1617970898768547577726349)
            ·
              refine ⟨606739087038205341647381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1617970898768547577726349 606739087038205341647381)
              ·
                refine ⟨28440894704915875389721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 606739087038205341647381 28440894704915875389721)
                ·
                  rfl

theorem cell19_93468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 6].length) (baseStart_93468 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_93468 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_93468 prefixEnd_93468 := by exact prefixLift 93468
  have htrace : WordTrace (prefixWord ++ tailWord_93468) baseStart_93468 baseEnd_93468 := by
    simpa [prefixWord, tailWord_93468, baseEnd_93468] using wordTrace_append hprefix tailTrace_93468
  have hstable : (prefixWord ++ tailWord_93468).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93468).length < 2 ^ (prefixWord ++ tailWord_93468).sum := by decide
  have hdescent : baseEnd_93468 < baseStart_93468 := by decide
  rcases family_descends (prefixWord ++ tailWord_93468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93517 : List Nat := [1, 6, 1, 3, 2, 1, 1, 4]
def baseStart_93517 : Nat := 118140960795 + 93517 * 2 ^ 59
def prefixEnd_93517 : Nat := 4983230072969 + 3 ^ 40 * 93517 * 2
def baseEnd_93517 : Nat := 28455804661698280300699

theorem tailTrace_93517 : CollatzResearch.WordTrace tailWord_93517 prefixEnd_93517 28455804661698280300699 := by
  unfold tailWord_93517
  simp only [CollatzResearch.WordTrace]
  refine ⟨3410845202211355277158805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2273896801474236851439203 3410845202211355277158805)
  ·
    refine ⟨159883368853657278616819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 3410845202211355277158805 159883368853657278616819)
    ·
      refine ⟨239825053280485917925229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159883368853657278616819 239825053280485917925229)
      ·
        refine ⟨89934394980182219221961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 239825053280485917925229 89934394980182219221961)
        ·
          refine ⟨67450796235136664416471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89934394980182219221961 67450796235136664416471)
          ·
            refine ⟨101176194352704996624707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67450796235136664416471 101176194352704996624707)
            ·
              refine ⟨151764291529057494937061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101176194352704996624707 151764291529057494937061)
              ·
                refine ⟨28455804661698280300699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 151764291529057494937061 28455804661698280300699)
                ·
                  rfl

theorem cell19_93517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 1, 4].length) (baseStart_93517 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_93517 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_93517 prefixEnd_93517 := by exact prefixLift 93517
  have htrace : WordTrace (prefixWord ++ tailWord_93517) baseStart_93517 baseEnd_93517 := by
    simpa [prefixWord, tailWord_93517, baseEnd_93517] using wordTrace_append hprefix tailTrace_93517
  have hstable : (prefixWord ++ tailWord_93517).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93517).length < 2 ^ (prefixWord ++ tailWord_93517).sum := by decide
  have hdescent : baseEnd_93517 < baseStart_93517 := by decide
  rcases family_descends (prefixWord ++ tailWord_93517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93597 : List Nat := [1, 4, 2, 1, 3, 3, 2, 3]
def baseStart_93597 : Nat := 118140960795 + 93597 * 2 ^ 59
def prefixEnd_93597 : Nat := 4983230072969 + 3 ^ 40 * 93597 * 2
def baseEnd_93597 : Nat := 28480147448281798522703

theorem tailTrace_93597 : CollatzResearch.WordTrace tailWord_93597 prefixEnd_93597 28480147448281798522703 := by
  unfold tailWord_93597
  simp only [CollatzResearch.WordTrace]
  refine ⟨3413763041921528940071045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2275842027947685960047363 3413763041921528940071045)
  ·
    refine ⟨640080570360286676263321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3413763041921528940071045 640080570360286676263321)
    ·
      refine ⟨480060427770215007197491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 640080570360286676263321 480060427770215007197491)
      ·
        refine ⟨720090641655322510796237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 480060427770215007197491 720090641655322510796237)
        ·
          refine ⟨270033990620745941548589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 720090641655322510796237 270033990620745941548589)
          ·
            refine ⟨101262746482779728080721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 270033990620745941548589 101262746482779728080721)
            ·
              refine ⟨75947059862084796060541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101262746482779728080721 75947059862084796060541)
              ·
                refine ⟨28480147448281798522703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 75947059862084796060541 28480147448281798522703)
                ·
                  rfl

theorem cell19_93597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 2, 3].length) (baseStart_93597 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_93597 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_93597 prefixEnd_93597 := by exact prefixLift 93597
  have htrace : WordTrace (prefixWord ++ tailWord_93597) baseStart_93597 baseEnd_93597 := by
    simpa [prefixWord, tailWord_93597, baseEnd_93597] using wordTrace_append hprefix tailTrace_93597
  have hstable : (prefixWord ++ tailWord_93597).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93597).length < 2 ^ (prefixWord ++ tailWord_93597).sum := by decide
  have hdescent : baseEnd_93597 < baseStart_93597 := by decide
  rcases family_descends (prefixWord ++ tailWord_93597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93599 : List Nat := [1, 1, 2, 5, 1, 2, 4, 3]
def baseStart_93599 : Nat := 118140960795 + 93599 * 2 ^ 59
def prefixEnd_93599 : Nat := 4983230072969 + 3 ^ 40 * 93599 * 2
def baseEnd_93599 : Nat := 28480756017946386478253

theorem tailTrace_93599 : CollatzResearch.WordTrace tailWord_93599 prefixEnd_93599 28480756017946386478253 := by
  unfold tailWord_93599
  simp only [CollatzResearch.WordTrace]
  refine ⟨3413835987914283281643851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2275890658609522187762567 3413835987914283281643851)
  ·
    refine ⟨5120753981871424922465777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3413835987914283281643851 5120753981871424922465777)
    ·
      refine ⟨3840565486403568691849333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5120753981871424922465777 3840565486403568691849333)
      ·
        refine ⟨360053014350334564860875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3840565486403568691849333 360053014350334564860875)
        ·
          refine ⟨540079521525501847291313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 360053014350334564860875 540079521525501847291313)
          ·
            refine ⟨405059641144126385468485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 540079521525501847291313 405059641144126385468485)
            ·
              refine ⟨75948682714523697275341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 405059641144126385468485 75948682714523697275341)
              ·
                refine ⟨28480756017946386478253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 75948682714523697275341 28480756017946386478253)
                ·
                  rfl

theorem cell19_93599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 4, 3].length) (baseStart_93599 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_93599 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_93599 prefixEnd_93599 := by exact prefixLift 93599
  have htrace : WordTrace (prefixWord ++ tailWord_93599) baseStart_93599 baseEnd_93599 := by
    simpa [prefixWord, tailWord_93599, baseEnd_93599] using wordTrace_append hprefix tailTrace_93599
  have hstable : (prefixWord ++ tailWord_93599).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93599).length < 2 ^ (prefixWord ++ tailWord_93599).sum := by decide
  have hdescent : baseEnd_93599 < baseStart_93599 := by decide
  rcases family_descends (prefixWord ++ tailWord_93599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93639 : List Nat := [1, 1, 4, 1, 1, 3, 4, 4]
def baseStart_93639 : Nat := 118140960795 + 93639 * 2 ^ 59
def prefixEnd_93639 : Nat := 4983230072969 + 3 ^ 40 * 93639 * 2
def baseEnd_93639 : Nat := 28492927411238145589255

theorem tailTrace_93639 : CollatzResearch.WordTrace tailWord_93639 prefixEnd_93639 28492927411238145589255 := by
  unfold tailWord_93639
  simp only [CollatzResearch.WordTrace]
  refine ⟨3415294907769370113099971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2276863271846246742066647 3415294907769370113099971)
  ·
    refine ⟨5122942361654055169649957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3415294907769370113099971 5122942361654055169649957)
    ·
      refine ⟨960551692810135344309367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5122942361654055169649957 960551692810135344309367)
      ·
        refine ⟨1440827539215203016464051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 960551692810135344309367 1440827539215203016464051)
        ·
          refine ⟨2161241308822804524696077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1440827539215203016464051 2161241308822804524696077)
          ·
            refine ⟨810465490808551696761029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2161241308822804524696077 810465490808551696761029)
            ·
              refine ⟨151962279526603443142693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 810465490808551696761029 151962279526603443142693)
              ·
                refine ⟨28492927411238145589255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 151962279526603443142693 28492927411238145589255)
                ·
                  rfl

theorem cell19_93639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 4, 4].length) (baseStart_93639 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_93639 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_93639 prefixEnd_93639 := by exact prefixLift 93639
  have htrace : WordTrace (prefixWord ++ tailWord_93639) baseStart_93639 baseEnd_93639 := by
    simpa [prefixWord, tailWord_93639, baseEnd_93639] using wordTrace_append hprefix tailTrace_93639
  have hstable : (prefixWord ++ tailWord_93639).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93639).length < 2 ^ (prefixWord ++ tailWord_93639).sum := by decide
  have hdescent : baseEnd_93639 < baseStart_93639 := by decide
  rcases family_descends (prefixWord ++ tailWord_93639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93658 : List Nat := [3, 1, 1, 2, 3, 2, 2, 5]
def baseStart_93658 : Nat := 118140960795 + 93658 * 2 ^ 59
def prefixEnd_93658 : Nat := 4983230072969 + 3 ^ 40 * 93658 * 2
def baseEnd_93658 : Nat := 28498708823051731166981

theorem tailTrace_93658 : CollatzResearch.WordTrace tailWord_93658 prefixEnd_93658 28498708823051731166981 := by
  unfold tailWord_93658
  simp only [CollatzResearch.WordTrace]
  refine ⟨853996973675134089510407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2277325263133690905361085 853996973675134089510407)
  ·
    refine ⟨1280995460512701134265611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 853996973675134089510407 1280995460512701134265611)
    ·
      refine ⟨1921493190769051701398417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1280995460512701134265611 1921493190769051701398417)
      ·
        refine ⟨1441119893076788776048813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1921493190769051701398417 1441119893076788776048813)
        ·
          refine ⟨540419959903795791018305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1441119893076788776048813 540419959903795791018305)
          ·
            refine ⟨405314969927846843263729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 540419959903795791018305 405314969927846843263729)
            ·
              refine ⟨303986227445885132447797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 405314969927846843263729 303986227445885132447797)
              ·
                refine ⟨28498708823051731166981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 303986227445885132447797 28498708823051731166981)
                ·
                  rfl

theorem cell19_93658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 5].length) (baseStart_93658 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_93658 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_93658 prefixEnd_93658 := by exact prefixLift 93658
  have htrace : WordTrace (prefixWord ++ tailWord_93658) baseStart_93658 baseEnd_93658 := by
    simpa [prefixWord, tailWord_93658, baseEnd_93658] using wordTrace_append hprefix tailTrace_93658
  have hstable : (prefixWord ++ tailWord_93658).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93658).length < 2 ^ (prefixWord ++ tailWord_93658).sum := by decide
  have hdescent : baseEnd_93658 < baseStart_93658 := by decide
  rcases family_descends (prefixWord ++ tailWord_93658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93677 : List Nat := [1, 5, 1, 3, 9]
def baseStart_93677 : Nat := 118140960795 + 93677 * 2 ^ 59
def prefixEnd_93677 : Nat := 4983230072969 + 3 ^ 40 * 93677 * 2
def baseEnd_93677 : Nat := 1055721860550567286841

theorem tailTrace_93677 : CollatzResearch.WordTrace tailWord_93677 prefixEnd_93677 1055721860550567286841 := by
  unfold tailWord_93677
  simp only [CollatzResearch.WordTrace]
  refine ⟨3416680881631702602983285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2277787254421135068655523 3416680881631702602983285)
  ·
    refine ⟨320313832652972119029683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3416680881631702602983285 320313832652972119029683)
    ·
      refine ⟨480470748979458178544525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 320313832652972119029683 480470748979458178544525)
      ·
        refine ⟨180176530867296816954197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 480470748979458178544525 180176530867296816954197)
        ·
          refine ⟨1055721860550567286841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 180176530867296816954197 1055721860550567286841)
          ·
            rfl

theorem cell19_93677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 9].length) (baseStart_93677 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_93677 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_93677 prefixEnd_93677 := by exact prefixLift 93677
  have htrace : WordTrace (prefixWord ++ tailWord_93677) baseStart_93677 baseEnd_93677 := by
    simpa [prefixWord, tailWord_93677, baseEnd_93677] using wordTrace_append hprefix tailTrace_93677
  have hstable : (prefixWord ++ tailWord_93677).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93677).length < 2 ^ (prefixWord ++ tailWord_93677).sum := by decide
  have hdescent : baseEnd_93677 < baseStart_93677 := by decide
  rcases family_descends (prefixWord ++ tailWord_93677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93772 : List Nat := [2, 2, 1, 3, 1, 4, 1, 5]
def baseStart_93772 : Nat := 118140960795 + 93772 * 2 ^ 59
def prefixEnd_93772 : Nat := 4983230072969 + 3 ^ 40 * 93772 * 2
def baseEnd_93772 : Nat := 28533397293933244633337

theorem tailTrace_93772 : CollatzResearch.WordTrace tailWord_93772 prefixEnd_93772 28533397293933244633337 := by
  unfold tailWord_93772
  simp only [CollatzResearch.WordTrace]
  refine ⟨1710072908143766913845785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2280097210858355885127713 1710072908143766913845785)
  ·
    refine ⟨1282554681107825185384339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1710072908143766913845785 1282554681107825185384339)
    ·
      refine ⟨1923832021661737778076509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1282554681107825185384339 1923832021661737778076509)
      ·
        refine ⟨721437008123151666778691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1923832021661737778076509 721437008123151666778691)
        ·
          refine ⟨1082155512184727500168037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 721437008123151666778691 1082155512184727500168037)
          ·
            refine ⟨202904158534636406281507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1082155512184727500168037 202904158534636406281507)
            ·
              refine ⟨304356237801954609422261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 202904158534636406281507 304356237801954609422261)
              ·
                refine ⟨28533397293933244633337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 304356237801954609422261 28533397293933244633337)
                ·
                  rfl

theorem cell19_93772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 5].length) (baseStart_93772 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_93772 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_93772 prefixEnd_93772 := by exact prefixLift 93772
  have htrace : WordTrace (prefixWord ++ tailWord_93772) baseStart_93772 baseEnd_93772 := by
    simpa [prefixWord, tailWord_93772, baseEnd_93772] using wordTrace_append hprefix tailTrace_93772
  have hstable : (prefixWord ++ tailWord_93772).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93772).length < 2 ^ (prefixWord ++ tailWord_93772).sum := by decide
  have hdescent : baseEnd_93772 < baseStart_93772 := by decide
  rcases family_descends (prefixWord ++ tailWord_93772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93810 : List Nat := [3, 2, 1, 2, 3, 1, 1, 6]
def baseStart_93810 : Nat := 118140960795 + 93810 * 2 ^ 59
def prefixEnd_93810 : Nat := 4983230072969 + 3 ^ 40 * 93810 * 2
def baseEnd_93810 : Nat := 28544960117560415788789

theorem tailTrace_93810 : CollatzResearch.WordTrace tailWord_93810 prefixEnd_93810 28544960117560415788789 := by
  unfold tailWord_93810
  simp only [CollatzResearch.WordTrace]
  refine ⟨855382947537466579393721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2281021193433244211716589 855382947537466579393721)
  ·
    refine ⟨641537210653099934545291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 855382947537466579393721 641537210653099934545291)
    ·
      refine ⟨962305815979649901817937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 641537210653099934545291 962305815979649901817937)
      ·
        refine ⟨721729361984737426363453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 962305815979649901817937 721729361984737426363453)
        ·
          refine ⟨270648510744276534886295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 721729361984737426363453 270648510744276534886295)
          ·
            refine ⟨405972766116414802329443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 270648510744276534886295 405972766116414802329443)
            ·
              refine ⟨608959149174622203494165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 405972766116414802329443 608959149174622203494165)
              ·
                refine ⟨28544960117560415788789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 608959149174622203494165 28544960117560415788789)
                ·
                  rfl

theorem cell19_93810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 6].length) (baseStart_93810 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_93810 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_93810 prefixEnd_93810 := by exact prefixLift 93810
  have htrace : WordTrace (prefixWord ++ tailWord_93810) baseStart_93810 baseEnd_93810 := by
    simpa [prefixWord, tailWord_93810, baseEnd_93810] using wordTrace_append hprefix tailTrace_93810
  have hstable : (prefixWord ++ tailWord_93810).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93810).length < 2 ^ (prefixWord ++ tailWord_93810).sum := by decide
  have hdescent : baseEnd_93810 < baseStart_93810 := by decide
  rcases family_descends (prefixWord ++ tailWord_93810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93850 : List Nat := [3, 1, 1, 14]
def baseStart_93850 : Nat := 118140960795 + 93850 * 2 ^ 59
def prefixEnd_93850 : Nat := 4983230072969 + 3 ^ 40 * 93850 * 2
def baseEnd_93850 : Nat := 352557179146323146911

theorem tailTrace_93850 : CollatzResearch.WordTrace tailWord_93850 prefixEnd_93850 352557179146323146911 := by
  unfold tailWord_93850
  simp only [CollatzResearch.WordTrace]
  refine ⟨855747677501238287257751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2281993806669968766020669 855747677501238287257751)
  ·
    refine ⟨1283621516251857430886627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 855747677501238287257751 1283621516251857430886627)
    ·
      refine ⟨1925432274377786146329941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1283621516251857430886627 1925432274377786146329941)
      ·
        refine ⟨352557179146323146911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 14 1925432274377786146329941 352557179146323146911)
        ·
          rfl

theorem cell19_93850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 14].length) (baseStart_93850 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_93850 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_93850 prefixEnd_93850 := by exact prefixLift 93850
  have htrace : WordTrace (prefixWord ++ tailWord_93850) baseStart_93850 baseEnd_93850 := by
    simpa [prefixWord, tailWord_93850, baseEnd_93850] using wordTrace_append hprefix tailTrace_93850
  have hstable : (prefixWord ++ tailWord_93850).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93850).length < 2 ^ (prefixWord ++ tailWord_93850).sum := by decide
  have hdescent : baseEnd_93850 < baseStart_93850 := by decide
  rcases family_descends (prefixWord ++ tailWord_93850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93884 : List Nat := [2, 2, 2, 3, 1, 3, 3, 3]
def baseStart_93884 : Nat := 118140960795 + 93884 * 2 ^ 59
def prefixEnd_93884 : Nat := 4983230072969 + 3 ^ 40 * 93884 * 2
def baseEnd_93884 : Nat := 28567477195150170144143

theorem tailTrace_93884 : CollatzResearch.WordTrace tailWord_93884 prefixEnd_93884 28567477195150170144143 := by
  unfold tailWord_93884
  simp only [CollatzResearch.WordTrace]
  refine ⟨1712115395940888477884353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2282820527921184637179137 1712115395940888477884353)
  ·
    refine ⟨1284086546955666358413265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1712115395940888477884353 1284086546955666358413265)
    ·
      refine ⟨963064910216749768809949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1284086546955666358413265 963064910216749768809949)
      ·
        refine ⟨361149341331281163303731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 963064910216749768809949 361149341331281163303731)
        ·
          refine ⟨541724011996921744955597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 361149341331281163303731 541724011996921744955597)
          ·
            refine ⟨203146504498845654358349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 541724011996921744955597 203146504498845654358349)
            ·
              refine ⟨76179939187067120384381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 203146504498845654358349 76179939187067120384381)
              ·
                refine ⟨28567477195150170144143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 76179939187067120384381 28567477195150170144143)
                ·
                  rfl

theorem cell19_93884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 3, 3].length) (baseStart_93884 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_93884 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_93884 prefixEnd_93884 := by exact prefixLift 93884
  have htrace : WordTrace (prefixWord ++ tailWord_93884) baseStart_93884 baseEnd_93884 := by
    simpa [prefixWord, tailWord_93884, baseEnd_93884] using wordTrace_append hprefix tailTrace_93884
  have hstable : (prefixWord ++ tailWord_93884).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93884).length < 2 ^ (prefixWord ++ tailWord_93884).sum := by decide
  have hdescent : baseEnd_93884 < baseStart_93884 := by decide
  rcases family_descends (prefixWord ++ tailWord_93884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93943 : List Nat := [1, 1, 3, 1, 1, 1, 8, 3]
def baseStart_93943 : Nat := 118140960795 + 93943 * 2 ^ 59
def prefixEnd_93943 : Nat := 4983230072969 + 3 ^ 40 * 93943 * 2
def baseEnd_93943 : Nat := 28585430000255514832871

theorem tailTrace_93943 : CollatzResearch.WordTrace tailWord_93943 prefixEnd_93943 28585430000255514832871 := by
  unfold tailWord_93943
  simp only [CollatzResearch.WordTrace]
  refine ⟨3426382698668030032166483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2284255132445353354777655 3426382698668030032166483)
  ·
    refine ⟨5139574048002045048249725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3426382698668030032166483 5139574048002045048249725)
    ·
      refine ⟨1927340268000766893093647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5139574048002045048249725 1927340268000766893093647)
      ·
        refine ⟨2891010402001150339640471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1927340268000766893093647 2891010402001150339640471)
        ·
          refine ⟨4336515603001725509460707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2891010402001150339640471 4336515603001725509460707)
          ·
            refine ⟨6504773404502588264191061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4336515603001725509460707 6504773404502588264191061)
            ·
              refine ⟨76227813334014706220989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 6504773404502588264191061 76227813334014706220989)
              ·
                refine ⟨28585430000255514832871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 76227813334014706220989 28585430000255514832871)
                ·
                  rfl

theorem cell19_93943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 8, 3].length) (baseStart_93943 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_93943 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_93943 prefixEnd_93943 := by exact prefixLift 93943
  have htrace : WordTrace (prefixWord ++ tailWord_93943) baseStart_93943 baseEnd_93943 := by
    simpa [prefixWord, tailWord_93943, baseEnd_93943] using wordTrace_append hprefix tailTrace_93943
  have hstable : (prefixWord ++ tailWord_93943).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93943).length < 2 ^ (prefixWord ++ tailWord_93943).sum := by decide
  have hdescent : baseEnd_93943 < baseStart_93943 := by decide
  rcases family_descends (prefixWord ++ tailWord_93943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93962 : List Nat := [3, 1, 2, 2, 1, 5, 5]
def baseStart_93962 : Nat := 118140960795 + 93962 * 2 ^ 59
def prefixEnd_93962 : Nat := 4983230072969 + 3 ^ 40 * 93962 * 2
def baseEnd_93962 : Nat := 9530403804023033470199

theorem tailTrace_93962 : CollatzResearch.WordTrace tailWord_93962 prefixEnd_93962 9530403804023033470199 := by
  unfold tailWord_93962
  simp only [CollatzResearch.WordTrace]
  refine ⟨856768921399799069277035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2284717123732797518072093 856768921399799069277035)
  ·
    refine ⟨1285153382099698603915553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 856768921399799069277035 1285153382099698603915553)
    ·
      refine ⟨963865036574773952936665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1285153382099698603915553 963865036574773952936665)
      ·
        refine ⟨722898777431080464702499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 963865036574773952936665 722898777431080464702499)
        ·
          refine ⟨1084348166146620697053749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 722898777431080464702499 1084348166146620697053749)
          ·
            refine ⟨101657640576245690348789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1084348166146620697053749 101657640576245690348789)
            ·
              refine ⟨9530403804023033470199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 101657640576245690348789 9530403804023033470199)
              ·
                rfl

theorem cell19_93962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 5].length) (baseStart_93962 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_93962 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_93962 prefixEnd_93962 := by exact prefixLift 93962
  have htrace : WordTrace (prefixWord ++ tailWord_93962) baseStart_93962 baseEnd_93962 := by
    simpa [prefixWord, tailWord_93962, baseEnd_93962] using wordTrace_append hprefix tailTrace_93962
  have hstable : (prefixWord ++ tailWord_93962).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93962).length < 2 ^ (prefixWord ++ tailWord_93962).sum := by decide
  have hdescent : baseEnd_93962 < baseStart_93962 := by decide
  rcases family_descends (prefixWord ++ tailWord_93962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93964 : List Nat := [2, 2, 1, 2, 2, 1, 9]
def baseStart_93964 : Nat := 118140960795 + 93964 * 2 ^ 59
def prefixEnd_93964 : Nat := 4983230072969 + 3 ^ 40 * 93964 * 2
def baseEnd_93964 : Nat := 9530606660577896122049

theorem tailTrace_93964 : CollatzResearch.WordTrace tailWord_93964 prefixEnd_93964 9530606660577896122049 := by
  unfold tailWord_93964
  simp only [CollatzResearch.WordTrace]
  refine ⟨1713574315795975309340473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2284765754394633745787297 1713574315795975309340473)
  ·
    refine ⟨1285180736846981482005355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1713574315795975309340473 1285180736846981482005355)
    ·
      refine ⟨1927771105270472223008033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1285180736846981482005355 1927771105270472223008033)
      ·
        refine ⟨1445828328952854167256025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1927771105270472223008033 1445828328952854167256025)
        ·
          refine ⟨1084371246714640625442019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1445828328952854167256025 1084371246714640625442019)
          ·
            refine ⟨1626556870071960938163029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1084371246714640625442019 1626556870071960938163029)
            ·
              refine ⟨9530606660577896122049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1626556870071960938163029 9530606660577896122049)
              ·
                rfl

theorem cell19_93964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 9].length) (baseStart_93964 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_93964 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_93964 prefixEnd_93964 := by exact prefixLift 93964
  have htrace : WordTrace (prefixWord ++ tailWord_93964) baseStart_93964 baseEnd_93964 := by
    simpa [prefixWord, tailWord_93964, baseEnd_93964] using wordTrace_append hprefix tailTrace_93964
  have hstable : (prefixWord ++ tailWord_93964).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93964).length < 2 ^ (prefixWord ++ tailWord_93964).sum := by decide
  have hdescent : baseEnd_93964 < baseStart_93964 := by decide
  rcases family_descends (prefixWord ++ tailWord_93964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94036 : List Nat := [2, 4, 1, 1, 3, 3, 1, 4]
def baseStart_94036 : Nat := 118140960795 + 94036 * 2 ^ 59
def prefixEnd_94036 : Nat := 4983230072969 + 3 ^ 40 * 94036 * 2
def baseEnd_94036 : Nat := 28613728489658854765951

theorem tailTrace_94036 : CollatzResearch.WordTrace tailWord_94036 prefixEnd_94036 28613728489658854765951 := by
  unfold tailWord_94036
  simp only [CollatzResearch.WordTrace]
  refine ⟨1714887343665553457650981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2286516458220737943534641 1714887343665553457650981)
  ·
    refine ⟨321541376937291273309559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1714887343665553457650981 321541376937291273309559)
    ·
      refine ⟨482312065405936909964339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 321541376937291273309559 482312065405936909964339)
      ·
        refine ⟨723468098108905364946509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 482312065405936909964339 723468098108905364946509)
        ·
          refine ⟨271300536790839511854941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 723468098108905364946509 271300536790839511854941)
          ·
            refine ⟨101737701296564816945603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 271300536790839511854941 101737701296564816945603)
            ·
              refine ⟨152606551944847225418405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101737701296564816945603 152606551944847225418405)
              ·
                refine ⟨28613728489658854765951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 152606551944847225418405 28613728489658854765951)
                ·
                  rfl

theorem cell19_94036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 1, 4].length) (baseStart_94036 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_94036 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_94036 prefixEnd_94036 := by exact prefixLift 94036
  have htrace : WordTrace (prefixWord ++ tailWord_94036) baseStart_94036 baseEnd_94036 := by
    simpa [prefixWord, tailWord_94036, baseEnd_94036] using wordTrace_append hprefix tailTrace_94036
  have hstable : (prefixWord ++ tailWord_94036).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94036).length < 2 ^ (prefixWord ++ tailWord_94036).sum := by decide
  have hdescent : baseEnd_94036 < baseStart_94036 := by decide
  rcases family_descends (prefixWord ++ tailWord_94036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94110 : List Nat := [4, 3, 1, 3, 1, 1, 1, 5]
def baseStart_94110 : Nat := 118140960795 + 94110 * 2 ^ 59
def prefixEnd_94110 : Nat := 4983230072969 + 3 ^ 40 * 94110 * 2
def baseEnd_94110 : Nat := 28636245567248609121305

theorem tailTrace_94110 : CollatzResearch.WordTrace tailWord_94110 prefixEnd_94110 28636245567248609121305 := by
  unfold tailWord_94110
  simp only [CollatzResearch.WordTrace]
  refine ⟨429059211132877194186973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2288315792708678368997189 429059211132877194186973)
  ·
    refine ⟨160897204174828947820115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 429059211132877194186973 160897204174828947820115)
    ·
      refine ⟨241345806262243421730173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160897204174828947820115 241345806262243421730173)
      ·
        refine ⟨90504677348341283148815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 241345806262243421730173 90504677348341283148815)
        ·
          refine ⟨135757016022511924723223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90504677348341283148815 135757016022511924723223)
          ·
            refine ⟨203635524033767887084835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135757016022511924723223 203635524033767887084835)
            ·
              refine ⟨305453286050651830627253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 203635524033767887084835 305453286050651830627253)
              ·
                refine ⟨28636245567248609121305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 305453286050651830627253 28636245567248609121305)
                ·
                  rfl

theorem cell19_94110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 5].length) (baseStart_94110 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_94110 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_94110 prefixEnd_94110 := by exact prefixLift 94110
  have htrace : WordTrace (prefixWord ++ tailWord_94110) baseStart_94110 baseEnd_94110 := by
    simpa [prefixWord, tailWord_94110, baseEnd_94110] using wordTrace_append hprefix tailTrace_94110
  have hstable : (prefixWord ++ tailWord_94110).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94110).length < 2 ^ (prefixWord ++ tailWord_94110).sum := by decide
  have hdescent : baseEnd_94110 < baseStart_94110 := by decide
  rcases family_descends (prefixWord ++ tailWord_94110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94133 : List Nat := [1, 3, 3, 2, 1, 4, 5]
def baseStart_94133 : Nat := 118140960795 + 94133 * 2 ^ 59
def prefixEnd_94133 : Nat := 4983230072969 + 3 ^ 40 * 94133 * 2
def baseEnd_94133 : Nat := 9547748039463790203377

theorem tailTrace_94133 : CollatzResearch.WordTrace tailWord_94133 prefixEnd_94133 9547748039463790203377 := by
  unfold tailWord_94133
  simp only [CollatzResearch.WordTrace]
  refine ⟨3433312567979692481583053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2288875045319794987722035 3433312567979692481583053)
  ·
    refine ⟨1287492212992384680593645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3433312567979692481583053 1287492212992384680593645)
    ·
      refine ⟨482809579872144255222617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1287492212992384680593645 482809579872144255222617)
      ·
        refine ⟨362107184904108191416963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 482809579872144255222617 362107184904108191416963)
        ·
          refine ⟨543160777356162287125445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 362107184904108191416963 543160777356162287125445)
          ·
            refine ⟨101842645754280428836021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 543160777356162287125445 101842645754280428836021)
            ·
              refine ⟨9547748039463790203377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 101842645754280428836021 9547748039463790203377)
              ·
                rfl

theorem cell19_94133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 5].length) (baseStart_94133 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_94133 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_94133 prefixEnd_94133 := by exact prefixLift 94133
  have htrace : WordTrace (prefixWord ++ tailWord_94133) baseStart_94133 baseEnd_94133 := by
    simpa [prefixWord, tailWord_94133, baseEnd_94133] using wordTrace_append hprefix tailTrace_94133
  have hstable : (prefixWord ++ tailWord_94133).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94133).length < 2 ^ (prefixWord ++ tailWord_94133).sum := by decide
  have hdescent : baseEnd_94133 < baseStart_94133 := by decide
  rcases family_descends (prefixWord ++ tailWord_94133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94152 : List Nat := [2, 1, 3, 1, 4, 2, 2, 4]
def baseStart_94152 : Nat := 118140960795 + 94152 * 2 ^ 59
def prefixEnd_94152 : Nat := 4983230072969 + 3 ^ 40 * 94152 * 2
def baseEnd_94152 : Nat := 28649025530204956187857

theorem tailTrace_94152 : CollatzResearch.WordTrace tailWord_94152 prefixEnd_94152 28649025530204956187857 := by
  unfold tailWord_94152
  simp only [CollatzResearch.WordTrace]
  refine ⟨1717002777455429363262355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2289337036607239151016473 1717002777455429363262355)
  ·
    refine ⟨2575504166183144044893533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1717002777455429363262355 2575504166183144044893533)
    ·
      refine ⟨965814062318679016835075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2575504166183144044893533 965814062318679016835075)
      ·
        refine ⟨1448721093478018525252613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 965814062318679016835075 1448721093478018525252613)
        ·
          refine ⟨271635205027128473484865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1448721093478018525252613 271635205027128473484865)
          ·
            refine ⟨203726403770346355113649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 271635205027128473484865 203726403770346355113649)
            ·
              refine ⟨152794802827759766335237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 203726403770346355113649 152794802827759766335237)
              ·
                refine ⟨28649025530204956187857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 152794802827759766335237 28649025530204956187857)
                ·
                  rfl

theorem cell19_94152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 2, 4].length) (baseStart_94152 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_94152 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_94152 prefixEnd_94152 := by exact prefixLift 94152
  have htrace : WordTrace (prefixWord ++ tailWord_94152) baseStart_94152 baseEnd_94152 := by
    simpa [prefixWord, tailWord_94152, baseEnd_94152] using wordTrace_append hprefix tailTrace_94152
  have hstable : (prefixWord ++ tailWord_94152).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94152).length < 2 ^ (prefixWord ++ tailWord_94152).sum := by decide
  have hdescent : baseEnd_94152 < baseStart_94152 := by decide
  rcases family_descends (prefixWord ++ tailWord_94152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94154 : List Nat := [3, 1, 2, 1, 2, 1, 3, 6]
def baseStart_94154 : Nat := 118140960795 + 94154 * 2 ^ 59
def prefixEnd_94154 : Nat := 4983230072969 + 3 ^ 40 * 94154 * 2
def baseEnd_94154 : Nat := 28649634099869544143407

theorem tailTrace_94154 : CollatzResearch.WordTrace tailWord_94154 prefixEnd_94154 28649634099869544143407 := by
  unfold tailWord_94154
  simp only [CollatzResearch.WordTrace]
  refine ⟨858519625225903267024379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2289385667269075378731677 858519625225903267024379)
  ·
    refine ⟨1287779437838854900536569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 858519625225903267024379 1287779437838854900536569)
    ·
      refine ⟨965834578379141175402427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1287779437838854900536569 965834578379141175402427)
      ·
        refine ⟨1448751867568711763103641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 965834578379141175402427 1448751867568711763103641)
        ·
          refine ⟨1086563900676533822327731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1448751867568711763103641 1086563900676533822327731)
          ·
            refine ⟨1629845851014800733491597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1086563900676533822327731 1629845851014800733491597)
            ·
              refine ⟨611192194130550275059349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1629845851014800733491597 611192194130550275059349)
              ·
                refine ⟨28649634099869544143407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 611192194130550275059349 28649634099869544143407)
                ·
                  rfl

theorem cell19_94154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 6].length) (baseStart_94154 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_94154 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_94154 prefixEnd_94154 := by exact prefixLift 94154
  have htrace : WordTrace (prefixWord ++ tailWord_94154) baseStart_94154 baseEnd_94154 := by
    simpa [prefixWord, tailWord_94154, baseEnd_94154] using wordTrace_append hprefix tailTrace_94154
  have hstable : (prefixWord ++ tailWord_94154).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94154).length < 2 ^ (prefixWord ++ tailWord_94154).sum := by decide
  have hdescent : baseEnd_94154 < baseStart_94154 := by decide
  rcases family_descends (prefixWord ++ tailWord_94154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94268 : List Nat := [2, 2, 2, 2, 2, 1, 2, 6]
def baseStart_94268 : Nat := 118140960795 + 94268 * 2 ^ 59
def prefixEnd_94268 : Nat := 4983230072969 + 3 ^ 40 * 94268 * 2
def baseEnd_94268 : Nat := 28684322570751057609763

theorem tailTrace_94268 : CollatzResearch.WordTrace tailWord_94268 prefixEnd_94268 28684322570751057609763 := by
  unfold tailWord_94268
  simp only [CollatzResearch.WordTrace]
  refine ⟨1719118211245305268873729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2292157614993740358498305 1719118211245305268873729)
  ·
    refine ⟨1289338658433978951655297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1719118211245305268873729 1289338658433978951655297)
    ·
      refine ⟨967003993825484213741473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1289338658433978951655297 967003993825484213741473)
      ·
        refine ⟨725252995369113160306105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 967003993825484213741473 725252995369113160306105)
        ·
          refine ⟨543939746526834870229579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 725252995369113160306105 543939746526834870229579)
          ·
            refine ⟨815909619790252305344369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 543939746526834870229579 815909619790252305344369)
            ·
              refine ⟨611932214842689229008277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 815909619790252305344369 611932214842689229008277)
              ·
                refine ⟨28684322570751057609763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 611932214842689229008277 28684322570751057609763)
                ·
                  rfl

theorem cell19_94268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 6].length) (baseStart_94268 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_94268 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_94268 prefixEnd_94268 := by exact prefixLift 94268
  have htrace : WordTrace (prefixWord ++ tailWord_94268) baseStart_94268 baseEnd_94268 := by
    simpa [prefixWord, tailWord_94268, baseEnd_94268] using wordTrace_append hprefix tailTrace_94268
  have hstable : (prefixWord ++ tailWord_94268).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94268).length < 2 ^ (prefixWord ++ tailWord_94268).sum := by decide
  have hdescent : baseEnd_94268 < baseStart_94268 := by decide
  rcases family_descends (prefixWord ++ tailWord_94268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94285 : List Nat := [1, 6, 1, 1, 1, 1, 3, 5]
def baseStart_94285 : Nat := 118140960795 + 94285 * 2 ^ 59
def prefixEnd_94285 : Nat := 4983230072969 + 3 ^ 40 * 94285 * 2
def baseEnd_94285 : Nat := 28689495412900055231939

theorem tailTrace_94285 : CollatzResearch.WordTrace tailWord_94285 prefixEnd_94285 28689495412900055231939 := by
  unfold tailWord_94285
  simp only [CollatzResearch.WordTrace]
  refine ⟨3438856463429022441116309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2292570975619348294077539 3438856463429022441116309)
  ·
    refine ⟨161196396723235426927327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 3438856463429022441116309 161196396723235426927327)
    ·
      refine ⟨241794595084853140390991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161196396723235426927327 241794595084853140390991)
      ·
        refine ⟨362691892627279710586487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 241794595084853140390991 362691892627279710586487)
        ·
          refine ⟨544037838940919565879731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 362691892627279710586487 544037838940919565879731)
          ·
            refine ⟨816056758411379348819597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 544037838940919565879731 816056758411379348819597)
            ·
              refine ⟨306021284404267255807349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 816056758411379348819597 306021284404267255807349)
              ·
                refine ⟨28689495412900055231939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 306021284404267255807349 28689495412900055231939)
                ·
                  rfl

theorem cell19_94285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 5].length) (baseStart_94285 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_94285 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_94285 prefixEnd_94285 := by exact prefixLift 94285
  have htrace : WordTrace (prefixWord ++ tailWord_94285) baseStart_94285 baseEnd_94285 := by
    simpa [prefixWord, tailWord_94285, baseEnd_94285] using wordTrace_append hprefix tailTrace_94285
  have hstable : (prefixWord ++ tailWord_94285).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94285).length < 2 ^ (prefixWord ++ tailWord_94285).sum := by decide
  have hdescent : baseEnd_94285 < baseStart_94285 := by decide
  rcases family_descends (prefixWord ++ tailWord_94285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94458 : List Nat := [3, 1, 1, 1, 1, 6, 1, 5]
def baseStart_94458 : Nat := 118140960795 + 94458 * 2 ^ 59
def prefixEnd_94458 : Nat := 4983230072969 + 3 ^ 40 * 94458 * 2
def baseEnd_94458 : Nat := 28742136688886913387023

theorem tailTrace_94458 : CollatzResearch.WordTrace tailWord_94458 prefixEnd_94458 28742136688886913387023 := by
  unfold tailWord_94458
  simp only [CollatzResearch.WordTrace]
  refine ⟨861291572950568246791007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2296777527868181991442685 861291572950568246791007)
  ·
    refine ⟨1291937359425852370186511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 861291572950568246791007 1291937359425852370186511)
    ·
      refine ⟨1937906039138778555279767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1291937359425852370186511 1937906039138778555279767)
      ·
        refine ⟨2906859058708167832919651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1937906039138778555279767 2906859058708167832919651)
        ·
          refine ⟨4360288588062251749379477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2906859058708167832919651 4360288588062251749379477)
          ·
            refine ⟨204388527565418050752163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 4360288588062251749379477 204388527565418050752163)
            ·
              refine ⟨306582791348127076128245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 204388527565418050752163 306582791348127076128245)
              ·
                refine ⟨28742136688886913387023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 306582791348127076128245 28742136688886913387023)
                ·
                  rfl

theorem cell19_94458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 5].length) (baseStart_94458 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_94458 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_94458 prefixEnd_94458 := by exact prefixLift 94458
  have htrace : WordTrace (prefixWord ++ tailWord_94458) baseStart_94458 baseEnd_94458 := by
    simpa [prefixWord, tailWord_94458, baseEnd_94458] using wordTrace_append hprefix tailTrace_94458
  have hstable : (prefixWord ++ tailWord_94458).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94458).length < 2 ^ (prefixWord ++ tailWord_94458).sum := by decide
  have hdescent : baseEnd_94458 < baseStart_94458 := by decide
  rcases family_descends (prefixWord ++ tailWord_94458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94496 : List Nat := [2, 1, 1, 5, 2, 1, 1, 6]
def baseStart_94496 : Nat := 118140960795 + 94496 * 2 ^ 59
def prefixEnd_94496 : Nat := 4983230072969 + 3 ^ 40 * 94496 * 2
def baseEnd_94496 : Nat := 28753699512514084542475

theorem tailTrace_94496 : CollatzResearch.WordTrace tailWord_94496 prefixEnd_94496 28753699512514084542475 := by
  unfold tailWord_94496
  simp only [CollatzResearch.WordTrace]
  refine ⟨1723276132832302738523671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2297701510443070318031561 1723276132832302738523671)
  ·
    refine ⟨2584914199248454107785507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1723276132832302738523671 2584914199248454107785507)
    ·
      refine ⟨3877371298872681161678261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2584914199248454107785507 3877371298872681161678261)
      ·
        refine ⟨363503559269313858907337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3877371298872681161678261 363503559269313858907337)
        ·
          refine ⟨272627669451985394180503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 363503559269313858907337 272627669451985394180503)
          ·
            refine ⟨408941504177978091270755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 272627669451985394180503 408941504177978091270755)
            ·
              refine ⟨613412256266967136906133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 408941504177978091270755 613412256266967136906133)
              ·
                refine ⟨28753699512514084542475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 613412256266967136906133 28753699512514084542475)
                ·
                  rfl

theorem cell19_94496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 6].length) (baseStart_94496 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_94496 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_94496 prefixEnd_94496 := by exact prefixLift 94496
  have htrace : WordTrace (prefixWord ++ tailWord_94496) baseStart_94496 baseEnd_94496 := by
    simpa [prefixWord, tailWord_94496, baseEnd_94496] using wordTrace_append hprefix tailTrace_94496
  have hstable : (prefixWord ++ tailWord_94496).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94496).length < 2 ^ (prefixWord ++ tailWord_94496).sum := by decide
  have hdescent : baseEnd_94496 < baseStart_94496 := by decide
  rcases family_descends (prefixWord ++ tailWord_94496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94532 : List Nat := [2, 3, 4, 1, 2, 7]
def baseStart_94532 : Nat := 118140960795 + 94532 * 2 ^ 59
def prefixEnd_94532 : Nat := 4983230072969 + 3 ^ 40 * 94532 * 2
def baseEnd_94532 : Nat := 3196072640719629749153

theorem tailTrace_94532 : CollatzResearch.WordTrace tailWord_94532 prefixEnd_94532 3196072640719629749153 := by
  unfold tailWord_94532
  simp only [CollatzResearch.WordTrace]
  refine ⟨1723932646767091812678925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2298576862356122416905233 1723932646767091812678925)
  ·
    refine ⟨646474742537659429754597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1723932646767091812678925 646474742537659429754597)
    ·
      refine ⟨121214014225811143078987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 646474742537659429754597 121214014225811143078987)
      ·
        refine ⟨181821021338716714618481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121214014225811143078987 181821021338716714618481)
        ·
          refine ⟨136365766004037535963861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 181821021338716714618481 136365766004037535963861)
          ·
            refine ⟨3196072640719629749153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 136365766004037535963861 3196072640719629749153)
            ·
              rfl

theorem cell19_94532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 7].length) (baseStart_94532 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_94532 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_94532 prefixEnd_94532 := by exact prefixLift 94532
  have htrace : WordTrace (prefixWord ++ tailWord_94532) baseStart_94532 baseEnd_94532 := by
    simpa [prefixWord, tailWord_94532, baseEnd_94532] using wordTrace_append hprefix tailTrace_94532
  have hstable : (prefixWord ++ tailWord_94532).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94532).length < 2 ^ (prefixWord ++ tailWord_94532).sum := by decide
  have hdescent : baseEnd_94532 < baseStart_94532 := by decide
  rcases family_descends (prefixWord ++ tailWord_94532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94549 : List Nat := [1, 3, 2, 2, 5, 1, 1, 4]
def baseStart_94549 : Nat := 118140960795 + 94549 * 2 ^ 59
def prefixEnd_94549 : Nat := 4983230072969 + 3 ^ 40 * 94549 * 2
def baseEnd_94549 : Nat := 28769826608625665364553

theorem tailTrace_94549 : CollatzResearch.WordTrace tailWord_94549 prefixEnd_94549 28769826608625665364553 := by
  unfold tailWord_94549
  simp only [CollatzResearch.WordTrace]
  refine ⟨3448485334472595528726701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2298990222981730352484467 3448485334472595528726701)
  ·
    refine ⟨1293182000427223323272513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3448485334472595528726701 1293182000427223323272513)
    ·
      refine ⟨969886500320417492454385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1293182000427223323272513 969886500320417492454385)
      ·
        refine ⟨727414875240313119340789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 969886500320417492454385 727414875240313119340789)
        ·
          refine ⟨68195144553779354938199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 727414875240313119340789 68195144553779354938199)
          ·
            refine ⟨102292716830669032407299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68195144553779354938199 102292716830669032407299)
            ·
              refine ⟨153439075246003548610949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102292716830669032407299 153439075246003548610949)
              ·
                refine ⟨28769826608625665364553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 153439075246003548610949 28769826608625665364553)
                ·
                  rfl

theorem cell19_94549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 1, 4].length) (baseStart_94549 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_94549 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_94549 prefixEnd_94549 := by exact prefixLift 94549
  have htrace : WordTrace (prefixWord ++ tailWord_94549) baseStart_94549 baseEnd_94549 := by
    simpa [prefixWord, tailWord_94549, baseEnd_94549] using wordTrace_append hprefix tailTrace_94549
  have hstable : (prefixWord ++ tailWord_94549).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94549).length < 2 ^ (prefixWord ++ tailWord_94549).sum := by decide
  have hdescent : baseEnd_94549 < baseStart_94549 := by decide
  rcases family_descends (prefixWord ++ tailWord_94549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94627 : List Nat := [1, 1, 1, 4, 1, 6, 2, 3]
def baseStart_94627 : Nat := 118140960795 + 94627 * 2 ^ 59
def prefixEnd_94627 : Nat := 4983230072969 + 3 ^ 40 * 94627 * 2
def baseEnd_94627 : Nat := 28793560825544595631007

theorem tailTrace_94627 : CollatzResearch.WordTrace tailWord_94627 prefixEnd_94627 28793560825544595631007 := by
  unfold tailWord_94627
  simp only [CollatzResearch.WordTrace]
  refine ⟨3451330228190014850066135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2300886818793343233377423 3451330228190014850066135)
  ·
    refine ⟨5176995342285022275099203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3451330228190014850066135 5176995342285022275099203)
    ·
      refine ⟨7765493013427533412648805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5176995342285022275099203 7765493013427533412648805)
      ·
        refine ⟨1456029940017662514871651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7765493013427533412648805 1456029940017662514871651)
        ·
          refine ⟨2184044910026493772307477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1456029940017662514871651 2184044910026493772307477)
          ·
            refine ⟨102377105157491895576913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 2184044910026493772307477 102377105157491895576913)
            ·
              refine ⟨76782828868118921682685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102377105157491895576913 76782828868118921682685)
              ·
                refine ⟨28793560825544595631007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 76782828868118921682685 28793560825544595631007)
                ·
                  rfl

theorem cell19_94627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 2, 3].length) (baseStart_94627 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_94627 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_94627 prefixEnd_94627 := by exact prefixLift 94627
  have htrace : WordTrace (prefixWord ++ tailWord_94627) baseStart_94627 baseEnd_94627 := by
    simpa [prefixWord, tailWord_94627, baseEnd_94627] using wordTrace_append hprefix tailTrace_94627
  have hstable : (prefixWord ++ tailWord_94627).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94627).length < 2 ^ (prefixWord ++ tailWord_94627).sum := by decide
  have hdescent : baseEnd_94627 < baseStart_94627 := by decide
  rcases family_descends (prefixWord ++ tailWord_94627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94688 : List Nat := [2, 1, 1, 3, 1, 1, 3, 7]
def baseStart_94688 : Nat := 118140960795 + 94688 * 2 ^ 59
def prefixEnd_94688 : Nat := 4983230072969 + 3 ^ 40 * 94688 * 2
def baseEnd_94688 : Nat := 28812122200314528275285

theorem tailTrace_94688 : CollatzResearch.WordTrace tailWord_94688 prefixEnd_94688 28812122200314528275285 := by
  unfold tailWord_94688
  simp only [CollatzResearch.WordTrace]
  refine ⟨1726777540484511134018359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2302370053979348178691145 1726777540484511134018359)
  ·
    refine ⟨2590166310726766701027539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1726777540484511134018359 2590166310726766701027539)
    ·
      refine ⟨3885249466090150051541309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2590166310726766701027539 3885249466090150051541309)
      ·
        refine ⟨1456968549783806269327991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3885249466090150051541309 1456968549783806269327991)
        ·
          refine ⟨2185452824675709403991987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1456968549783806269327991 2185452824675709403991987)
          ·
            refine ⟨3278179237013564105987981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2185452824675709403991987 3278179237013564105987981)
            ·
              refine ⟨1229317213880086539745493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3278179237013564105987981 1229317213880086539745493)
              ·
                refine ⟨28812122200314528275285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1229317213880086539745493 28812122200314528275285)
                ·
                  rfl

theorem cell19_94688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 7].length) (baseStart_94688 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_94688 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_94688 prefixEnd_94688 := by exact prefixLift 94688
  have htrace : WordTrace (prefixWord ++ tailWord_94688) baseStart_94688 baseEnd_94688 := by
    simpa [prefixWord, tailWord_94688, baseEnd_94688] using wordTrace_append hprefix tailTrace_94688
  have hstable : (prefixWord ++ tailWord_94688).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94688).length < 2 ^ (prefixWord ++ tailWord_94688).sum := by decide
  have hdescent : baseEnd_94688 < baseStart_94688 := by decide
  rcases family_descends (prefixWord ++ tailWord_94688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94762 : List Nat := [3, 1, 4, 1, 1, 3, 6]
def baseStart_94762 : Nat := 118140960795 + 94762 * 2 ^ 59
def prefixEnd_94762 : Nat := 4983230072969 + 3 ^ 40 * 94762 * 2
def baseEnd_94762 : Nat := 9611546425968094210213

theorem tailTrace_94762 : CollatzResearch.WordTrace tailWord_94762 prefixEnd_94762 9611546425968094210213 := by
  unfold tailWord_94762
  simp only [CollatzResearch.WordTrace]
  refine ⟨864063520675233226557635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2304169388467288604153693 864063520675233226557635)
  ·
    refine ⟨1296095281012849839836453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 864063520675233226557635 1296095281012849839836453)
    ·
      refine ⟨243017865189909344969335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1296095281012849839836453 243017865189909344969335)
      ·
        refine ⟨364526797784864017454003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243017865189909344969335 364526797784864017454003)
        ·
          refine ⟨546790196677296026181005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 364526797784864017454003 546790196677296026181005)
          ·
            refine ⟨205046323753986009817877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 546790196677296026181005 205046323753986009817877)
            ·
              refine ⟨9611546425968094210213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 205046323753986009817877 9611546425968094210213)
              ·
                rfl

theorem cell19_94762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 6].length) (baseStart_94762 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_94762 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_94762 prefixEnd_94762 := by exact prefixLift 94762
  have htrace : WordTrace (prefixWord ++ tailWord_94762) baseStart_94762 baseEnd_94762 := by
    simpa [prefixWord, tailWord_94762, baseEnd_94762] using wordTrace_append hprefix tailTrace_94762
  have hstable : (prefixWord ++ tailWord_94762).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94762).length < 2 ^ (prefixWord ++ tailWord_94762).sum := by decide
  have hdescent : baseEnd_94762 < baseStart_94762 := by decide
  rcases family_descends (prefixWord ++ tailWord_94762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94783 : List Nat := [1, 1, 2, 2, 3, 2, 2, 6]
def baseStart_94783 : Nat := 118140960795 + 94783 * 2 ^ 59
def prefixEnd_94783 : Nat := 4983230072969 + 3 ^ 40 * 94783 * 2
def baseEnd_94783 : Nat := 28841029259382456163915

theorem tailTrace_94783 : CollatzResearch.WordTrace tailWord_94783 prefixEnd_94783 28841029259382456163915 := by
  unfold tailWord_94783
  simp only [CollatzResearch.WordTrace]
  refine ⟨3457020015624853492745003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2304680010416568995163335 3457020015624853492745003)
  ·
    refine ⟨5185530023437280239117505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3457020015624853492745003 5185530023437280239117505)
    ·
      refine ⟨3889147517577960179338129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5185530023437280239117505 3889147517577960179338129)
      ·
        refine ⟨2916860638183470134503597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3889147517577960179338129 2916860638183470134503597)
        ·
          refine ⟨1093822739318801300438849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2916860638183470134503597 1093822739318801300438849)
          ·
            refine ⟨820367054489100975329137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1093822739318801300438849 820367054489100975329137)
            ·
              refine ⟨615275290866825731496853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 820367054489100975329137 615275290866825731496853)
              ·
                refine ⟨28841029259382456163915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 615275290866825731496853 28841029259382456163915)
                ·
                  rfl

theorem cell19_94783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 6].length) (baseStart_94783 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_94783 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_94783 prefixEnd_94783 := by exact prefixLift 94783
  have htrace : WordTrace (prefixWord ++ tailWord_94783) baseStart_94783 baseEnd_94783 := by
    simpa [prefixWord, tailWord_94783, baseEnd_94783] using wordTrace_append hprefix tailTrace_94783
  have hstable : (prefixWord ++ tailWord_94783).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94783).length < 2 ^ (prefixWord ++ tailWord_94783).sum := by decide
  have hdescent : baseEnd_94783 < baseStart_94783 := by decide
  rcases family_descends (prefixWord ++ tailWord_94783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94874 : List Nat := [3, 1, 1, 6, 2, 6]
def baseStart_94874 : Nat := 118140960795 + 94874 * 2 ^ 59
def prefixEnd_94874 : Nat := 4983230072969 + 3 ^ 40 * 94874 * 2
def baseEnd_94874 : Nat := 3207635464346800904605

theorem tailTrace_94874 : CollatzResearch.WordTrace tailWord_94874 prefixEnd_94874 3207635464346800904605 := by
  unfold tailWord_94874
  simp only [CollatzResearch.WordTrace]
  refine ⟨865084764573794008576919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2306892705530117356205117 865084764573794008576919)
  ·
    refine ⟨1297627146860691012865379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 865084764573794008576919 1297627146860691012865379)
    ·
      refine ⟨1946440720291036519298069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1297627146860691012865379 1946440720291036519298069)
      ·
        refine ⟨91239408763642336842097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 1946440720291036519298069 91239408763642336842097)
        ·
          refine ⟨68429556572731752631573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91239408763642336842097 68429556572731752631573)
          ·
            refine ⟨3207635464346800904605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 68429556572731752631573 3207635464346800904605)
            ·
              rfl

theorem cell19_94874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 6].length) (baseStart_94874 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_94874 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_94874 prefixEnd_94874 := by exact prefixLift 94874
  have htrace : WordTrace (prefixWord ++ tailWord_94874) baseStart_94874 baseEnd_94874 := by
    simpa [prefixWord, tailWord_94874, baseEnd_94874] using wordTrace_append hprefix tailTrace_94874
  have hstable : (prefixWord ++ tailWord_94874).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94874).length < 2 ^ (prefixWord ++ tailWord_94874).sum := by decide
  have hdescent : baseEnd_94874 < baseStart_94874 := by decide
  rcases family_descends (prefixWord ++ tailWord_94874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94893 : List Nat := [1, 5, 2, 1, 1, 4, 1, 4]
def baseStart_94893 : Nat := 118140960795 + 94893 * 2 ^ 59
def prefixEnd_94893 : Nat := 4983230072969 + 3 ^ 40 * 94893 * 2
def baseEnd_94893 : Nat := 28874500590934793719171

theorem tailTrace_94893 : CollatzResearch.WordTrace tailWord_94893 prefixEnd_94893 28874500590934793719171 := by
  unfold tailWord_94893
  simp only [CollatzResearch.WordTrace]
  refine ⟨3461032045226342279249333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2307354696817561519499555 3461032045226342279249333)
  ·
    refine ⟨324471754239969588679625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3461032045226342279249333 324471754239969588679625)
    ·
      refine ⟨243353815679977191509719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 324471754239969588679625 243353815679977191509719)
      ·
        refine ⟨365030723519965787264579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243353815679977191509719 365030723519965787264579)
        ·
          refine ⟨547546085279948680896869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 365030723519965787264579 547546085279948680896869)
          ·
            refine ⟨102664890989990377668163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 547546085279948680896869 102664890989990377668163)
            ·
              refine ⟨153997336484985566502245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102664890989990377668163 153997336484985566502245)
              ·
                refine ⟨28874500590934793719171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 153997336484985566502245 28874500590934793719171)
                ·
                  rfl

theorem cell19_94893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 1, 4].length) (baseStart_94893 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_94893 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_94893 prefixEnd_94893 := by exact prefixLift 94893
  have htrace : WordTrace (prefixWord ++ tailWord_94893) baseStart_94893 baseEnd_94893 := by
    simpa [prefixWord, tailWord_94893, baseEnd_94893] using wordTrace_append hprefix tailTrace_94893
  have hstable : (prefixWord ++ tailWord_94893).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94893).length < 2 ^ (prefixWord ++ tailWord_94893).sum := by decide
  have hdescent : baseEnd_94893 < baseStart_94893 := by decide
  rcases family_descends (prefixWord ++ tailWord_94893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94895 : List Nat := [1, 1, 2, 1, 2, 7, 1, 4]
def baseStart_94895 : Nat := 118140960795 + 94895 * 2 ^ 59
def prefixEnd_94895 : Nat := 4983230072969 + 3 ^ 40 * 94895 * 2
def baseEnd_94895 : Nat := 28875109160599381674721

theorem tailTrace_94895 : CollatzResearch.WordTrace tailWord_94895 prefixEnd_94895 28875109160599381674721 := by
  unfold tailWord_94895
  simp only [CollatzResearch.WordTrace]
  refine ⟨3461104991219096620822139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2307403327479397747214759 3461104991219096620822139)
  ·
    refine ⟨5191657486828644931233209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3461104991219096620822139 5191657486828644931233209)
    ·
      refine ⟨3893743115121483698424907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5191657486828644931233209 3893743115121483698424907)
      ·
        refine ⟨5840614672682225547637361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3893743115121483698424907 5840614672682225547637361)
        ·
          refine ⟨4380461004511669160728021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5840614672682225547637361 4380461004511669160728021)
          ·
            refine ⟨102667054793242245954563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 4380461004511669160728021 102667054793242245954563)
            ·
              refine ⟨154000582189863368931845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102667054793242245954563 154000582189863368931845)
              ·
                refine ⟨28875109160599381674721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 154000582189863368931845 28875109160599381674721)
                ·
                  rfl

theorem cell19_94895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 1, 4].length) (baseStart_94895 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_94895 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_94895 prefixEnd_94895 := by exact prefixLift 94895
  have htrace : WordTrace (prefixWord ++ tailWord_94895) baseStart_94895 baseEnd_94895 := by
    simpa [prefixWord, tailWord_94895, baseEnd_94895] using wordTrace_append hprefix tailTrace_94895
  have hstable : (prefixWord ++ tailWord_94895).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94895).length < 2 ^ (prefixWord ++ tailWord_94895).sum := by decide
  have hdescent : baseEnd_94895 < baseStart_94895 := by decide
  rcases family_descends (prefixWord ++ tailWord_94895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94935 : List Nat := [1, 1, 3, 2, 1, 5, 6]
def baseStart_94935 : Nat := 118140960795 + 94935 * 2 ^ 59
def prefixEnd_94935 : Nat := 4983230072969 + 3 ^ 40 * 94935 * 2
def baseEnd_94935 : Nat := 9629093517963713595241

theorem tailTrace_94935 : CollatzResearch.WordTrace tailWord_94935 prefixEnd_94935 9629093517963713595241 := by
  unfold tailWord_94935
  simp only [CollatzResearch.WordTrace]
  refine ⟨3462563911074183452278259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2308375940716122301518839 3462563911074183452278259)
  ·
    refine ⟨5193845866611275178417389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3462563911074183452278259 5193845866611275178417389)
    ·
      refine ⟨1947692199979228191906521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5193845866611275178417389 1947692199979228191906521)
      ·
        refine ⟨1460769149984421143929891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1947692199979228191906521 1460769149984421143929891)
        ·
          refine ⟨2191153724976631715894837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1460769149984421143929891 2191153724976631715894837)
          ·
            refine ⟨205420661716559223365141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2191153724976631715894837 205420661716559223365141)
            ·
              refine ⟨9629093517963713595241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 205420661716559223365141 9629093517963713595241)
              ·
                rfl

theorem cell19_94935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 6].length) (baseStart_94935 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_94935 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_94935 prefixEnd_94935 := by exact prefixLift 94935
  have htrace : WordTrace (prefixWord ++ tailWord_94935) baseStart_94935 baseEnd_94935 := by
    simpa [prefixWord, tailWord_94935, baseEnd_94935] using wordTrace_append hprefix tailTrace_94935
  have hstable : (prefixWord ++ tailWord_94935).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94935).length < 2 ^ (prefixWord ++ tailWord_94935).sum := by decide
  have hdescent : baseEnd_94935 < baseStart_94935 := by decide
  rcases family_descends (prefixWord ++ tailWord_94935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94954 : List Nat := [3, 1, 3, 1, 1, 1, 1, 8]
def baseStart_94954 : Nat := 118140960795 + 94954 * 2 ^ 59
def prefixEnd_94954 : Nat := 4983230072969 + 3 ^ 40 * 94954 * 2
def baseEnd_94954 : Nat := 28893061965704726363449

theorem tailTrace_94954 : CollatzResearch.WordTrace tailWord_94954 prefixEnd_94954 28893061965704726363449 := by
  unfold tailWord_94954
  simp only [CollatzResearch.WordTrace]
  refine ⟨865814224501337424304979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2308837932003566464813277 865814224501337424304979)
  ·
    refine ⟨1298721336752006136457469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 865814224501337424304979 1298721336752006136457469)
    ·
      refine ⟨487020501282002301171551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1298721336752006136457469 487020501282002301171551)
      ·
        refine ⟨730530751923003451757327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 487020501282002301171551 730530751923003451757327)
        ·
          refine ⟨1095796127884505177635991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 730530751923003451757327 1095796127884505177635991)
          ·
            refine ⟨1643694191826757766453987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1095796127884505177635991 1643694191826757766453987)
            ·
              refine ⟨2465541287740136649680981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1643694191826757766453987 2465541287740136649680981)
              ·
                refine ⟨28893061965704726363449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2465541287740136649680981 28893061965704726363449)
                ·
                  rfl

theorem cell19_94954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 8].length) (baseStart_94954 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_94954 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_94954 prefixEnd_94954 := by exact prefixLift 94954
  have htrace : WordTrace (prefixWord ++ tailWord_94954) baseStart_94954 baseEnd_94954 := by
    simpa [prefixWord, tailWord_94954, baseEnd_94954] using wordTrace_append hprefix tailTrace_94954
  have hstable : (prefixWord ++ tailWord_94954).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94954).length < 2 ^ (prefixWord ++ tailWord_94954).sum := by decide
  have hdescent : baseEnd_94954 < baseStart_94954 := by decide
  rcases family_descends (prefixWord ++ tailWord_94954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94973 : List Nat := [1, 4, 1, 1, 1, 1, 5, 5]
def baseStart_94973 : Nat := 118140960795 + 94973 * 2 ^ 59
def prefixEnd_94973 : Nat := 4983230072969 + 3 ^ 40 * 94973 * 2
def baseEnd_94973 : Nat := 28898843377518311941175

theorem tailTrace_94973 : CollatzResearch.WordTrace tailWord_94973 prefixEnd_94973 28898843377518311941175 := by
  unfold tailWord_94973
  simp only [CollatzResearch.WordTrace]
  refine ⟨3463949884936515942161573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2309299923291010628107715 3463949884936515942161573)
  ·
    refine ⟨649490603425596739155295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3463949884936515942161573 649490603425596739155295)
    ·
      refine ⟨974235905138395108732943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 649490603425596739155295 974235905138395108732943)
      ·
        refine ⟨1461353857707592663099415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 974235905138395108732943 1461353857707592663099415)
        ·
          refine ⟨2192030786561388994649123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1461353857707592663099415 2192030786561388994649123)
          ·
            refine ⟨3288046179842083491973685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2192030786561388994649123 3288046179842083491973685)
            ·
              refine ⟨308254329360195327372533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3288046179842083491973685 308254329360195327372533)
              ·
                refine ⟨28898843377518311941175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 308254329360195327372533 28898843377518311941175)
                ·
                  rfl

theorem cell19_94973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 5].length) (baseStart_94973 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_94973 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_94973 prefixEnd_94973 := by exact prefixLift 94973
  have htrace : WordTrace (prefixWord ++ tailWord_94973) baseStart_94973 baseEnd_94973 := by
    simpa [prefixWord, tailWord_94973, baseEnd_94973] using wordTrace_append hprefix tailTrace_94973
  have hstable : (prefixWord ++ tailWord_94973).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94973).length < 2 ^ (prefixWord ++ tailWord_94973).sum := by decide
  have hdescent : baseEnd_94973 < baseStart_94973 := by decide
  rcases family_descends (prefixWord ++ tailWord_94973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95066 : List Nat := [3, 1, 1, 2, 1, 6, 1, 4]
def baseStart_95066 : Nat := 118140960795 + 95066 * 2 ^ 59
def prefixEnd_95066 : Nat := 4983230072969 + 3 ^ 40 * 95066 * 2
def baseEnd_95066 : Nat := 28927141866921651874255

theorem tailTrace_95066 : CollatzResearch.WordTrace tailWord_95066 prefixEnd_95066 28927141866921651874255 := by
  unfold tailWord_95066
  simp only [CollatzResearch.WordTrace]
  refine ⟨866835468399898206324263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2311561249066395216864701 866835468399898206324263)
  ·
    refine ⟨1300253202599847309486395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 866835468399898206324263 1300253202599847309486395)
    ·
      refine ⟨1950379803899770964229593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1300253202599847309486395 1950379803899770964229593)
      ·
        refine ⟨1462784852924828223172195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1950379803899770964229593 1462784852924828223172195)
        ·
          refine ⟨2194177279387242334758293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1462784852924828223172195 2194177279387242334758293)
          ·
            refine ⟨102852059971276984441795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 2194177279387242334758293 102852059971276984441795)
            ·
              refine ⟨154278089956915476662693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102852059971276984441795 154278089956915476662693)
              ·
                refine ⟨28927141866921651874255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 154278089956915476662693 28927141866921651874255)
                ·
                  rfl

theorem cell19_95066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 1, 4].length) (baseStart_95066 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_95066 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_95066 prefixEnd_95066 := by exact prefixLift 95066
  have htrace : WordTrace (prefixWord ++ tailWord_95066) baseStart_95066 baseEnd_95066 := by
    simpa [prefixWord, tailWord_95066, baseEnd_95066] using wordTrace_append hprefix tailTrace_95066
  have hstable : (prefixWord ++ tailWord_95066).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95066).length < 2 ^ (prefixWord ++ tailWord_95066).sum := by decide
  have hdescent : baseEnd_95066 < baseStart_95066 := by decide
  rcases family_descends (prefixWord ++ tailWord_95066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95102 : List Nat := [4, 2, 3, 1, 2, 1, 6]
def baseStart_95102 : Nat := 118140960795 + 95102 * 2 ^ 59
def prefixEnd_95102 : Nat := 4983230072969 + 3 ^ 40 * 95102 * 2
def baseEnd_95102 : Nat := 9646032040294745024719

theorem tailTrace_95102 : CollatzResearch.WordTrace tailWord_95102 prefixEnd_95102 9646032040294745024719 := by
  unfold tailWord_95102
  simp only [CollatzResearch.WordTrace]
  refine ⟨433581862683646371700945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2312436600979447315738373 433581862683646371700945)
  ·
    refine ⟨325186397012734778775709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 433581862683646371700945 325186397012734778775709)
    ·
      refine ⟨121944898879775542040891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 325186397012734778775709 121944898879775542040891)
      ·
        refine ⟨182917348319663313061337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121944898879775542040891 182917348319663313061337)
        ·
          refine ⟨137188011239747484796003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 182917348319663313061337 137188011239747484796003)
          ·
            refine ⟨205782016859621227194005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137188011239747484796003 205782016859621227194005)
            ·
              refine ⟨9646032040294745024719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 205782016859621227194005 9646032040294745024719)
              ·
                rfl

theorem cell19_95102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 6].length) (baseStart_95102 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_95102 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_95102 prefixEnd_95102 := by exact prefixLift 95102
  have htrace : WordTrace (prefixWord ++ tailWord_95102) baseStart_95102 baseEnd_95102 := by
    simpa [prefixWord, tailWord_95102, baseEnd_95102] using wordTrace_append hprefix tailTrace_95102
  have hstable : (prefixWord ++ tailWord_95102).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95102).length < 2 ^ (prefixWord ++ tailWord_95102).sum := by decide
  have hdescent : baseEnd_95102 < baseStart_95102 := by decide
  rcases family_descends (prefixWord ++ tailWord_95102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95182 : List Nat := [4, 1, 1, 1, 2, 3, 1, 6]
def baseStart_95182 : Nat := 118140960795 + 95182 * 2 ^ 59
def prefixEnd_95182 : Nat := 4983230072969 + 3 ^ 40 * 95182 * 2
def baseEnd_95182 : Nat := 28962438907467753296161

theorem tailTrace_95182 : CollatzResearch.WordTrace tailWord_95182 prefixEnd_95182 28962438907467753296161 := by
  unfold tailWord_95182
  simp only [CollatzResearch.WordTrace]
  refine ⟨433946592647418079564975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2314381827452896424346533 433946592647418079564975)
  ·
    refine ⟨650919888971127119347463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 433946592647418079564975 650919888971127119347463)
    ·
      refine ⟨976379833456690679021195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 650919888971127119347463 976379833456690679021195)
      ·
        refine ⟨1464569750185036018531793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 976379833456690679021195 1464569750185036018531793)
        ·
          refine ⟨1098427312638777013898845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1464569750185036018531793 1098427312638777013898845)
          ·
            refine ⟨411910242239541380212067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1098427312638777013898845 411910242239541380212067)
            ·
              refine ⟨617865363359312070318101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 411910242239541380212067 617865363359312070318101)
              ·
                refine ⟨28962438907467753296161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 617865363359312070318101 28962438907467753296161)
                ·
                  rfl

theorem cell19_95182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 6].length) (baseStart_95182 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_95182 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_95182 prefixEnd_95182 := by exact prefixLift 95182
  have htrace : WordTrace (prefixWord ++ tailWord_95182) baseStart_95182 baseEnd_95182 := by
    simpa [prefixWord, tailWord_95182, baseEnd_95182] using wordTrace_append hprefix tailTrace_95182
  have hstable : (prefixWord ++ tailWord_95182).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95182).length < 2 ^ (prefixWord ++ tailWord_95182).sum := by decide
  have hdescent : baseEnd_95182 < baseStart_95182 := by decide
  rcases family_descends (prefixWord ++ tailWord_95182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95218 : List Nat := [3, 2, 1, 5, 1, 7]
def baseStart_95218 : Nat := 118140960795 + 95218 * 2 ^ 59
def prefixEnd_95218 : Nat := 4983230072969 + 3 ^ 40 * 95218 * 2
def baseEnd_95218 : Nat := 3219265906825592944007

theorem tailTrace_95218 : CollatzResearch.WordTrace tailWord_95218 prefixEnd_95218 3219265906825592944007 := by
  unfold tailWord_95218
  simp only [CollatzResearch.WordTrace]
  refine ⟨868221442262230696207577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2315257179365948523220205 868221442262230696207577)
  ·
    refine ⟨651166081696673022155683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 868221442262230696207577 651166081696673022155683)
    ·
      refine ⟨976749122545009533233525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 651166081696673022155683 976749122545009533233525)
      ·
        refine ⟨91570230238594643740643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 976749122545009533233525 91570230238594643740643)
        ·
          refine ⟨137355345357891965610965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91570230238594643740643 137355345357891965610965)
          ·
            refine ⟨3219265906825592944007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 137355345357891965610965 3219265906825592944007)
            ·
              rfl

theorem cell19_95218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 7].length) (baseStart_95218 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_95218 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_95218 prefixEnd_95218 := by exact prefixLift 95218
  have htrace : WordTrace (prefixWord ++ tailWord_95218) baseStart_95218 baseEnd_95218 := by
    simpa [prefixWord, tailWord_95218, baseEnd_95218] using wordTrace_append hprefix tailTrace_95218
  have hstable : (prefixWord ++ tailWord_95218).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95218).length < 2 ^ (prefixWord ++ tailWord_95218).sum := by decide
  have hdescent : baseEnd_95218 < baseStart_95218 := by decide
  rcases family_descends (prefixWord ++ tailWord_95218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95250 : List Nat := [3, 2, 5, 1, 1, 1, 3, 3]
def baseStart_95250 : Nat := 118140960795 + 95250 * 2 ^ 59
def prefixEnd_95250 : Nat := 4983230072969 + 3 ^ 40 * 95250 * 2
def baseEnd_95250 : Nat := 28983130276063743784865

theorem tailTrace_95250 : CollatzResearch.WordTrace tailWord_95250 prefixEnd_95250 28983130276063743784865 := by
  unfold tailWord_95250
  simp only [CollatzResearch.WordTrace]
  refine ⟨868513226233248062498801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2316035269955328166663469 868513226233248062498801)
  ·
    refine ⟨651384919674936046874101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 868513226233248062498801 651384919674936046874101)
    ·
      refine ⟨61067336219525254394447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 651384919674936046874101 61067336219525254394447)
      ·
        refine ⟨91601004329287881591671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61067336219525254394447 91601004329287881591671)
        ·
          refine ⟨137401506493931822387507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91601004329287881591671 137401506493931822387507)
          ·
            refine ⟨206102259740897733581261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137401506493931822387507 206102259740897733581261)
            ·
              refine ⟨77288347402836650092973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 206102259740897733581261 77288347402836650092973)
              ·
                refine ⟨28983130276063743784865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77288347402836650092973 28983130276063743784865)
                ·
                  rfl

theorem cell19_95250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 3, 3].length) (baseStart_95250 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_95250 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_95250 prefixEnd_95250 := by exact prefixLift 95250
  have htrace : WordTrace (prefixWord ++ tailWord_95250) baseStart_95250 baseEnd_95250 := by
    simpa [prefixWord, tailWord_95250, baseEnd_95250] using wordTrace_append hprefix tailTrace_95250
  have hstable : (prefixWord ++ tailWord_95250).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95250).length < 2 ^ (prefixWord ++ tailWord_95250).sum := by decide
  have hdescent : baseEnd_95250 < baseStart_95250 := by decide
  rcases family_descends (prefixWord ++ tailWord_95250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95256 : List Nat := [2, 1, 2, 3, 2, 3, 3, 3]
def baseStart_95256 : Nat := 118140960795 + 95256 * 2 ^ 59
def prefixEnd_95256 : Nat := 4983230072969 + 3 ^ 40 * 95256 * 2
def baseEnd_95256 : Nat := 28984955985057507651515

theorem tailTrace_95256 : CollatzResearch.WordTrace tailWord_95256 prefixEnd_95256 28984955985057507651515 := by
  unfold tailWord_95256
  simp only [CollatzResearch.WordTrace]
  refine ⟨1737135871455627637356811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2316181161940836849809081 1737135871455627637356811)
  ·
    refine ⟨2605703807183441456035217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1737135871455627637356811 2605703807183441456035217)
    ·
      refine ⟨1954277855387581092026413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2605703807183441456035217 1954277855387581092026413)
      ·
        refine ⟨732854195770342909509905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1954277855387581092026413 732854195770342909509905)
        ·
          refine ⟨549640646827757182132429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 732854195770342909509905 549640646827757182132429)
          ·
            refine ⟨206115242560408943299661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 549640646827757182132429 206115242560408943299661)
            ·
              refine ⟨77293215960153353737373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 206115242560408943299661 77293215960153353737373)
              ·
                refine ⟨28984955985057507651515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77293215960153353737373 28984955985057507651515)
                ·
                  rfl

theorem cell19_95256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 3, 3].length) (baseStart_95256 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_95256 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_95256 prefixEnd_95256 := by exact prefixLift 95256
  have htrace : WordTrace (prefixWord ++ tailWord_95256) baseStart_95256 baseEnd_95256 := by
    simpa [prefixWord, tailWord_95256, baseEnd_95256] using wordTrace_append hprefix tailTrace_95256
  have hstable : (prefixWord ++ tailWord_95256).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95256).length < 2 ^ (prefixWord ++ tailWord_95256).sum := by decide
  have hdescent : baseEnd_95256 < baseStart_95256 := by decide
  rcases family_descends (prefixWord ++ tailWord_95256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95349 : List Nat := [1, 3, 4, 3, 1, 1, 2, 4]
def baseStart_95349 : Nat := 118140960795 + 95349 * 2 ^ 59
def prefixEnd_95349 : Nat := 4983230072969 + 3 ^ 40 * 95349 * 2
def baseEnd_95349 : Nat := 29013254474460847584595

theorem tailTrace_95349 : CollatzResearch.WordTrace tailWord_95349 prefixEnd_95349 29013254474460847584595 := by
  unfold tailWord_95349
  simp only [CollatzResearch.WordTrace]
  refine ⟨3477663731574332157849101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2318442487716221438566067 3477663731574332157849101)
  ·
    refine ⟨1304123899340374559193413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3477663731574332157849101 1304123899340374559193413)
    ·
      refine ⟨244523231126320229848765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1304123899340374559193413 244523231126320229848765)
      ·
        refine ⟨91696211672370086193287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 244523231126320229848765 91696211672370086193287)
        ·
          refine ⟨137544317508555129289931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91696211672370086193287 137544317508555129289931)
          ·
            refine ⟨206316476262832693934897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137544317508555129289931 206316476262832693934897)
            ·
              refine ⟨154737357197124520451173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 206316476262832693934897 154737357197124520451173)
              ·
                refine ⟨29013254474460847584595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 154737357197124520451173 29013254474460847584595)
                ·
                  rfl

theorem cell19_95349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 2, 4].length) (baseStart_95349 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_95349 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_95349 prefixEnd_95349 := by exact prefixLift 95349
  have htrace : WordTrace (prefixWord ++ tailWord_95349) baseStart_95349 baseEnd_95349 := by
    simpa [prefixWord, tailWord_95349, baseEnd_95349] using wordTrace_append hprefix tailTrace_95349
  have hstable : (prefixWord ++ tailWord_95349).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95349).length < 2 ^ (prefixWord ++ tailWord_95349).sum := by decide
  have hdescent : baseEnd_95349 < baseStart_95349 := by decide
  rcases family_descends (prefixWord ++ tailWord_95349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95391 : List Nat := [1, 1, 2, 6, 2, 7]
def baseStart_95391 : Nat := 118140960795 + 95391 * 2 ^ 59
def prefixEnd_95391 : Nat := 4983230072969 + 3 ^ 40 * 95391 * 2
def baseEnd_95391 : Nat := 3225114937490799405683

theorem tailTrace_95391 : CollatzResearch.WordTrace tailWord_95391 prefixEnd_95391 3225114937490799405683 := by
  unfold tailWord_95391
  simp only [CollatzResearch.WordTrace]
  refine ⟨3479195597422173330878027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2319463731614782220585351 3479195597422173330878027)
  ·
    refine ⟨5218793396133259996317041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3479195597422173330878027 5218793396133259996317041)
    ·
      refine ⟨3914095047099944997237781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5218793396133259996317041 3914095047099944997237781)
      ·
        refine ⟨183473205332809921745521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 3914095047099944997237781 183473205332809921745521)
        ·
          refine ⟨137604903999607441309141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 183473205332809921745521 137604903999607441309141)
          ·
            refine ⟨3225114937490799405683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 137604903999607441309141 3225114937490799405683)
            ·
              rfl

theorem cell19_95391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 7].length) (baseStart_95391 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_95391 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_95391 prefixEnd_95391 := by exact prefixLift 95391
  have htrace : WordTrace (prefixWord ++ tailWord_95391) baseStart_95391 baseEnd_95391 := by
    simpa [prefixWord, tailWord_95391, baseEnd_95391] using wordTrace_append hprefix tailTrace_95391
  have hstable : (prefixWord ++ tailWord_95391).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95391).length < 2 ^ (prefixWord ++ tailWord_95391).sum := by decide
  have hdescent : baseEnd_95391 < baseStart_95391 := by decide
  rcases family_descends (prefixWord ++ tailWord_95391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95410 : List Nat := [3, 2, 1, 1, 1, 4, 3, 4]
def baseStart_95410 : Nat := 118140960795 + 95410 * 2 ^ 59
def prefixEnd_95410 : Nat := 4983230072969 + 3 ^ 40 * 95410 * 2
def baseEnd_95410 : Nat := 29031815849230780228873

theorem tailTrace_95410 : CollatzResearch.WordTrace tailWord_95410 prefixEnd_95410 29031815849230780228873 := by
  unfold tailWord_95410
  simp only [CollatzResearch.WordTrace]
  refine ⟨869972146088334893954921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2319925722902226383879789 869972146088334893954921)
  ·
    refine ⟨652479109566251170466191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 869972146088334893954921 652479109566251170466191)
    ·
      refine ⟨978718664349376755699287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 652479109566251170466191 978718664349376755699287)
      ·
        refine ⟨1468077996524065133548931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 978718664349376755699287 1468077996524065133548931)
        ·
          refine ⟨2202116994786097700323397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1468077996524065133548931 2202116994786097700323397)
          ·
            refine ⟨412896936522393318810637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2202116994786097700323397 412896936522393318810637)
            ·
              refine ⟨154836351195897494553989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 412896936522393318810637 154836351195897494553989)
              ·
                refine ⟨29031815849230780228873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 154836351195897494553989 29031815849230780228873)
                ·
                  rfl

theorem cell19_95410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 3, 4].length) (baseStart_95410 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_95410 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_95410 prefixEnd_95410 := by exact prefixLift 95410
  have htrace : WordTrace (prefixWord ++ tailWord_95410) baseStart_95410 baseEnd_95410 := by
    simpa [prefixWord, tailWord_95410, baseEnd_95410] using wordTrace_append hprefix tailTrace_95410
  have hstable : (prefixWord ++ tailWord_95410).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95410).length < 2 ^ (prefixWord ++ tailWord_95410).sum := by decide
  have hdescent : baseEnd_95410 < baseStart_95410 := by decide
  rcases family_descends (prefixWord ++ tailWord_95410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95425 : List Nat := [1, 2, 6, 1, 1, 2, 3, 3]
def baseStart_95425 : Nat := 118140960795 + 95425 * 2 ^ 59
def prefixEnd_95425 : Nat := 4983230072969 + 3 ^ 40 * 95425 * 2
def baseEnd_95425 : Nat := 29036380121715189895499

theorem tailTrace_95425 : CollatzResearch.WordTrace tailWord_95425 prefixEnd_95425 29036380121715189895499 := by
  unfold tailWord_95425
  simp only [CollatzResearch.WordTrace]
  refine ⟨3480435679298997137615729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2320290452865998091743819 3480435679298997137615729)
  ·
    refine ⟨2610326759474247853211797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3480435679298997137615729 2610326759474247853211797)
    ·
      refine ⟨122359066850355368119303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 2610326759474247853211797 122359066850355368119303)
      ·
        refine ⟨183538600275533052178955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122359066850355368119303 183538600275533052178955)
        ·
          refine ⟨275307900413299578268433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183538600275533052178955 275307900413299578268433)
          ·
            refine ⟨206480925309974683701325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 275307900413299578268433 206480925309974683701325)
            ·
              refine ⟨77430346991240506387997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 206480925309974683701325 77430346991240506387997)
              ·
                refine ⟨29036380121715189895499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77430346991240506387997 29036380121715189895499)
                ·
                  rfl

theorem cell19_95425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 3, 3].length) (baseStart_95425 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_95425 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_95425 prefixEnd_95425 := by exact prefixLift 95425
  have htrace : WordTrace (prefixWord ++ tailWord_95425) baseStart_95425 baseEnd_95425 := by
    simpa [prefixWord, tailWord_95425, baseEnd_95425] using wordTrace_append hprefix tailTrace_95425
  have hstable : (prefixWord ++ tailWord_95425).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95425).length < 2 ^ (prefixWord ++ tailWord_95425).sum := by decide
  have hdescent : baseEnd_95425 < baseStart_95425 := by decide
  rcases family_descends (prefixWord ++ tailWord_95425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95431 : List Nat := [1, 1, 4, 1, 1, 1, 1, 9]
def baseStart_95431 : Nat := 118140960795 + 95431 * 2 ^ 59
def prefixEnd_95431 : Nat := 4983230072969 + 3 ^ 40 * 95431 * 2
def baseEnd_95431 : Nat := 29038205830708953762149

theorem tailTrace_95431 : CollatzResearch.WordTrace tailWord_95431 prefixEnd_95431 29038205830708953762149 := by
  unfold tailWord_95431
  simp only [CollatzResearch.WordTrace]
  refine ⟨3480654517277260162334147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2320436344851506774889431 3480654517277260162334147)
  ·
    refine ⟨5220981775915890243501221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3480654517277260162334147 5220981775915890243501221)
    ·
      refine ⟨978934082984229420656479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5220981775915890243501221 978934082984229420656479)
      ·
        refine ⟨1468401124476344130984719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 978934082984229420656479 1468401124476344130984719)
        ·
          refine ⟨2202601686714516196477079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1468401124476344130984719 2202601686714516196477079)
          ·
            refine ⟨3303902530071774294715619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2202601686714516196477079 3303902530071774294715619)
            ·
              refine ⟨4955853795107661442073429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3303902530071774294715619 4955853795107661442073429)
              ·
                refine ⟨29038205830708953762149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 4955853795107661442073429 29038205830708953762149)
                ·
                  rfl

theorem cell19_95431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 9].length) (baseStart_95431 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_95431 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_95431 prefixEnd_95431 := by exact prefixLift 95431
  have htrace : WordTrace (prefixWord ++ tailWord_95431) baseStart_95431 baseEnd_95431 := by
    simpa [prefixWord, tailWord_95431, baseEnd_95431] using wordTrace_append hprefix tailTrace_95431
  have hstable : (prefixWord ++ tailWord_95431).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95431).length < 2 ^ (prefixWord ++ tailWord_95431).sum := by decide
  have hdescent : baseEnd_95431 < baseStart_95431 := by decide
  rcases family_descends (prefixWord ++ tailWord_95431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95448 : List Nat := [2, 1, 2, 2, 5, 1, 6]
def baseStart_95448 : Nat := 118140960795 + 95448 * 2 ^ 59
def prefixEnd_95448 : Nat := 4983230072969 + 3 ^ 40 * 95448 * 2
def baseEnd_95448 : Nat := 9681126224285983794775

theorem tailTrace_95448 : CollatzResearch.WordTrace tailWord_95448 prefixEnd_95448 9681126224285983794775 := by
  unfold tailWord_95448
  simp only [CollatzResearch.WordTrace]
  refine ⟨1740637279107836032851499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2320849705477114710468665 1740637279107836032851499)
  ·
    refine ⟨2610955918661754049277249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1740637279107836032851499 2610955918661754049277249)
    ·
      refine ⟨1958216938996315536957937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2610955918661754049277249 1958216938996315536957937)
      ·
        refine ⟨1468662704247236652718453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1958216938996315536957937 1468662704247236652718453)
        ·
          refine ⟨137687128523178436192355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1468662704247236652718453 137687128523178436192355)
          ·
            refine ⟨206530692784767654288533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137687128523178436192355 206530692784767654288533)
            ·
              refine ⟨9681126224285983794775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 206530692784767654288533 9681126224285983794775)
              ·
                rfl

theorem cell19_95448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 6].length) (baseStart_95448 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_95448 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_95448 prefixEnd_95448 := by exact prefixLift 95448
  have htrace : WordTrace (prefixWord ++ tailWord_95448) baseStart_95448 baseEnd_95448 := by
    simpa [prefixWord, tailWord_95448, baseEnd_95448] using wordTrace_append hprefix tailTrace_95448
  have hstable : (prefixWord ++ tailWord_95448).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95448).length < 2 ^ (prefixWord ++ tailWord_95448).sum := by decide
  have hdescent : baseEnd_95448 < baseStart_95448 := by decide
  rcases family_descends (prefixWord ++ tailWord_95448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95476 : List Nat := [2, 6, 1, 2, 2, 1, 2, 3]
def baseStart_95476 : Nat := 118140960795 + 95476 * 2 ^ 59
def prefixEnd_95476 : Nat := 4983230072969 + 3 ^ 40 * 95476 * 2
def baseEnd_95476 : Nat := 29051898648162182762027

theorem tailTrace_95476 : CollatzResearch.WordTrace tailWord_95476 prefixEnd_95476 29051898648162182762027 := by
  unfold tailWord_95476
  simp only [CollatzResearch.WordTrace]
  refine ⟨1741147901057116423861141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2321530534742821898481521 1741147901057116423861141)
  ·
    refine ⟨81616307862052332368491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 1741147901057116423861141 81616307862052332368491)
    ·
      refine ⟨122424461793078498552737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81616307862052332368491 122424461793078498552737)
      ·
        refine ⟨91818346344808873914553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122424461793078498552737 91818346344808873914553)
        ·
          refine ⟨68863759758606655435915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91818346344808873914553 68863759758606655435915)
          ·
            refine ⟨103295639637909983153873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68863759758606655435915 103295639637909983153873)
            ·
              refine ⟨77471729728432487365405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103295639637909983153873 77471729728432487365405)
              ·
                refine ⟨29051898648162182762027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77471729728432487365405 29051898648162182762027)
                ·
                  rfl

theorem cell19_95476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 2, 3].length) (baseStart_95476 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_95476 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_95476 prefixEnd_95476 := by exact prefixLift 95476
  have htrace : WordTrace (prefixWord ++ tailWord_95476) baseStart_95476 baseEnd_95476 := by
    simpa [prefixWord, tailWord_95476, baseEnd_95476] using wordTrace_append hprefix tailTrace_95476
  have hstable : (prefixWord ++ tailWord_95476).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95476).length < 2 ^ (prefixWord ++ tailWord_95476).sum := by decide
  have hdescent : baseEnd_95476 < baseStart_95476 := by decide
  rcases family_descends (prefixWord ++ tailWord_95476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95522 : List Nat := [3, 3, 1, 1, 4, 1, 2, 4]
def baseStart_95522 : Nat := 118140960795 + 95522 * 2 ^ 59
def prefixEnd_95522 : Nat := 4983230072969 + 3 ^ 40 * 95522 * 2
def baseEnd_95522 : Nat := 29065895750447705739679

theorem tailTrace_95522 : CollatzResearch.WordTrace tailWord_95522 prefixEnd_95522 29065895750447705739679 := by
  unfold tailWord_95522
  simp only [CollatzResearch.WordTrace]
  refine ⟨870993389986895675974205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2322649039965055135931213 870993389986895675974205)
  ·
    refine ⟨326622521245085878490327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 870993389986895675974205 326622521245085878490327)
    ·
      refine ⟨489933781867628817735491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 326622521245085878490327 489933781867628817735491)
      ·
        refine ⟨734900672801443226603237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 489933781867628817735491 734900672801443226603237)
        ·
          refine ⟨137793876150270604988107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 734900672801443226603237 137793876150270604988107)
          ·
            refine ⟨206690814225405907482161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137793876150270604988107 206690814225405907482161)
            ·
              refine ⟨155018110669054430611621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 206690814225405907482161 155018110669054430611621)
              ·
                refine ⟨29065895750447705739679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 155018110669054430611621 29065895750447705739679)
                ·
                  rfl

theorem cell19_95522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 2, 4].length) (baseStart_95522 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_95522 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_95522 prefixEnd_95522 := by exact prefixLift 95522
  have htrace : WordTrace (prefixWord ++ tailWord_95522) baseStart_95522 baseEnd_95522 := by
    simpa [prefixWord, tailWord_95522, baseEnd_95522] using wordTrace_append hprefix tailTrace_95522
  have hstable : (prefixWord ++ tailWord_95522).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95522).length < 2 ^ (prefixWord ++ tailWord_95522).sum := by decide
  have hdescent : baseEnd_95522 < baseStart_95522 := by decide
  rcases family_descends (prefixWord ++ tailWord_95522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95524 : List Nat := [2, 3, 1, 3, 1, 1, 4, 4]
def baseStart_95524 : Nat := 118140960795 + 95524 * 2 ^ 59
def prefixEnd_95524 : Nat := 4983230072969 + 3 ^ 40 * 95524 * 2
def baseEnd_95524 : Nat := 29066504320112293695229

theorem tailTrace_95524 : CollatzResearch.WordTrace tailWord_95524 prefixEnd_95524 29066504320112293695229 := by
  unfold tailWord_95524
  simp only [CollatzResearch.WordTrace]
  refine ⟨1742023252970168522734813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2322697670626891363646417 1742023252970168522734813)
  ·
    refine ⟨653258719863813196025555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1742023252970168522734813 653258719863813196025555)
    ·
      refine ⟨979888079795719794038333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 653258719863813196025555 979888079795719794038333)
      ·
        refine ⟨367458029923394922764375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 979888079795719794038333 367458029923394922764375)
        ·
          refine ⟨551187044885092384146563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 367458029923394922764375 551187044885092384146563)
          ·
            refine ⟨826780567327638576219845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 551187044885092384146563 826780567327638576219845)
            ·
              refine ⟨155021356373932233041221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 826780567327638576219845 155021356373932233041221)
              ·
                refine ⟨29066504320112293695229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 155021356373932233041221 29066504320112293695229)
                ·
                  rfl

theorem cell19_95524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 4, 4].length) (baseStart_95524 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_95524 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_95524 prefixEnd_95524 := by exact prefixLift 95524
  have htrace : WordTrace (prefixWord ++ tailWord_95524) baseStart_95524 baseEnd_95524 := by
    simpa [prefixWord, tailWord_95524, baseEnd_95524] using wordTrace_append hprefix tailTrace_95524
  have hstable : (prefixWord ++ tailWord_95524).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95524).length < 2 ^ (prefixWord ++ tailWord_95524).sum := by decide
  have hdescent : baseEnd_95524 < baseStart_95524 := by decide
  rcases family_descends (prefixWord ++ tailWord_95524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95558 : List Nat := [6, 1, 1, 3, 1, 7]
def baseStart_95558 : Nat := 118140960795 + 95558 * 2 ^ 59
def prefixEnd_95558 : Nat := 4983230072969 + 3 ^ 40 * 95558 * 2
def baseEnd_95558 : Nat := 3230761111601143215509

theorem tailTrace_95558 : CollatzResearch.WordTrace tailWord_95558 prefixEnd_95558 3230761111601143215509 := by
  unfold tailWord_95558
  simp only [CollatzResearch.WordTrace]
  refine ⟨108915205869286276631479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 2323524391878107234804885 108915205869286276631479)
  ·
    refine ⟨163372808803929414947219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108915205869286276631479 163372808803929414947219)
    ·
      refine ⟨245059213205894122420829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163372808803929414947219 245059213205894122420829)
      ·
        refine ⟨91897204952210295907811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 245059213205894122420829 91897204952210295907811)
        ·
          refine ⟨137845807428315443861717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91897204952210295907811 137845807428315443861717)
          ·
            refine ⟨3230761111601143215509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 137845807428315443861717 3230761111601143215509)
            ·
              rfl

theorem cell19_95558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 7].length) (baseStart_95558 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_95558 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_95558 prefixEnd_95558 := by exact prefixLift 95558
  have htrace : WordTrace (prefixWord ++ tailWord_95558) baseStart_95558 baseEnd_95558 := by
    simpa [prefixWord, tailWord_95558, baseEnd_95558] using wordTrace_append hprefix tailTrace_95558
  have hstable : (prefixWord ++ tailWord_95558).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95558).length < 2 ^ (prefixWord ++ tailWord_95558).sum := by decide
  have hdescent : baseEnd_95558 < baseStart_95558 := by decide
  rcases family_descends (prefixWord ++ tailWord_95558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95564 : List Nat := [2, 2, 1, 3, 2, 9]
def baseStart_95564 : Nat := 118140960795 + 95564 * 2 ^ 59
def prefixEnd_95564 : Nat := 4983230072969 + 3 ^ 40 * 95564 * 2
def baseEnd_95564 : Nat := 3230963968156005867359

theorem tailTrace_95564 : CollatzResearch.WordTrace tailWord_95564 prefixEnd_95564 3230963968156005867359 := by
  unfold tailWord_95564
  simp only [CollatzResearch.WordTrace]
  refine ⟨1742752712897711938462873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2323670283863615917950497 1742752712897711938462873)
  ·
    refine ⟨1307064534673283953847155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1742752712897711938462873 1307064534673283953847155)
    ·
      refine ⟨1960596802009925930770733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1307064534673283953847155 1960596802009925930770733)
      ·
        refine ⟨735223800753722224039025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1960596802009925930770733 735223800753722224039025)
        ·
          refine ⟨551417850565291668029269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 735223800753722224039025 551417850565291668029269)
          ·
            refine ⟨3230963968156005867359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 551417850565291668029269 3230963968156005867359)
            ·
              rfl

theorem cell19_95564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 9].length) (baseStart_95564 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_95564 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_95564 prefixEnd_95564 := by exact prefixLift 95564
  have htrace : WordTrace (prefixWord ++ tailWord_95564) baseStart_95564 baseEnd_95564 := by
    simpa [prefixWord, tailWord_95564, baseEnd_95564] using wordTrace_append hprefix tailTrace_95564
  have hstable : (prefixWord ++ tailWord_95564).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95564).length < 2 ^ (prefixWord ++ tailWord_95564).sum := by decide
  have hdescent : baseEnd_95564 < baseStart_95564 := by decide
  rcases family_descends (prefixWord ++ tailWord_95564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95600 : List Nat := [2, 1, 1, 1, 4, 2, 5, 3]
def baseStart_95600 : Nat := 118140960795 + 95600 * 2 ^ 59
def prefixEnd_95600 : Nat := 4983230072969 + 3 ^ 40 * 95600 * 2
def baseEnd_95600 : Nat := 29089629967366636006133

theorem tailTrace_95600 : CollatzResearch.WordTrace tailWord_95600 prefixEnd_95600 29089629967366636006133 := by
  unfold tailWord_95600
  simp only [CollatzResearch.WordTrace]
  refine ⟨1743409226832501012618127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2324545635776668016824169 1743409226832501012618127)
  ·
    refine ⟨2615113840248751518927191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1743409226832501012618127 2615113840248751518927191)
    ·
      refine ⟨3922670760373127278390787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2615113840248751518927191 3922670760373127278390787)
      ·
        refine ⟨5884006140559690917586181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3922670760373127278390787 5884006140559690917586181)
        ·
          refine ⟨1103251151354942047047409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5884006140559690917586181 1103251151354942047047409)
          ·
            refine ⟨827438363516206535285557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1103251151354942047047409 827438363516206535285557)
            ·
              refine ⟨77572346579644362683021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 827438363516206535285557 77572346579644362683021)
              ·
                refine ⟨29089629967366636006133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77572346579644362683021 29089629967366636006133)
                ·
                  rfl

theorem cell19_95600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 5, 3].length) (baseStart_95600 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_95600 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_95600 prefixEnd_95600 := by exact prefixLift 95600
  have htrace : WordTrace (prefixWord ++ tailWord_95600) baseStart_95600 baseEnd_95600 := by
    simpa [prefixWord, tailWord_95600, baseEnd_95600] using wordTrace_append hprefix tailTrace_95600
  have hstable : (prefixWord ++ tailWord_95600).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95600).length < 2 ^ (prefixWord ++ tailWord_95600).sum := by decide
  have hdescent : baseEnd_95600 < baseStart_95600 := by decide
  rcases family_descends (prefixWord ++ tailWord_95600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95733 : List Nat := [1, 3, 5, 1, 1, 8]
def baseStart_95733 : Nat := 118140960795 + 95733 * 2 ^ 59
def prefixEnd_95733 : Nat := 4983230072969 + 3 ^ 40 * 95733 * 2
def baseEnd_95733 : Nat := 3236677761117970561135

theorem tailTrace_95733 : CollatzResearch.WordTrace tailWord_95733 prefixEnd_95733 3236677761117970561135 := by
  unfold tailWord_95733
  simp only [CollatzResearch.WordTrace]
  refine ⟨3491669362183165739827853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2327779574788777159885235 3491669362183165739827853)
  ·
    refine ⟨1309376010818687152435445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3491669362183165739827853 1309376010818687152435445)
    ·
      refine ⟨122754001014251920540823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1309376010818687152435445 122754001014251920540823)
      ·
        refine ⟨184131001521377880811235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122754001014251920540823 184131001521377880811235)
        ·
          refine ⟨276196502282066821216853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184131001521377880811235 276196502282066821216853)
          ·
            refine ⟨3236677761117970561135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 276196502282066821216853 3236677761117970561135)
            ·
              rfl

theorem cell19_95733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 8].length) (baseStart_95733 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_95733 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_95733 prefixEnd_95733 := by exact prefixLift 95733
  have htrace : WordTrace (prefixWord ++ tailWord_95733) baseStart_95733 baseEnd_95733 := by
    simpa [prefixWord, tailWord_95733, baseEnd_95733] using wordTrace_append hprefix tailTrace_95733
  have hstable : (prefixWord ++ tailWord_95733).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95733).length < 2 ^ (prefixWord ++ tailWord_95733).sum := by decide
  have hdescent : baseEnd_95733 < baseStart_95733 := by decide
  rcases family_descends (prefixWord ++ tailWord_95733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95748 : List Nat := [2, 3, 2, 3, 3, 1, 1, 4]
def baseStart_95748 : Nat := 118140960795 + 95748 * 2 ^ 59
def prefixEnd_95748 : Nat := 4983230072969 + 3 ^ 40 * 95748 * 2
def baseEnd_95748 : Nat := 29134664122546144716841

theorem tailTrace_95748 : CollatzResearch.WordTrace tailWord_95748 prefixEnd_95748 29134664122546144716841 := by
  unfold tailWord_95748
  simp only [CollatzResearch.WordTrace]
  refine ⟨1746108228564411650811949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2328144304752548867749265 1746108228564411650811949)
  ·
    refine ⟨654790585711654369054481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1746108228564411650811949 654790585711654369054481)
    ·
      refine ⟨491092939283740776790861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 654790585711654369054481 491092939283740776790861)
      ·
        refine ⟨184159852231402791296573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 491092939283740776790861 184159852231402791296573)
        ·
          refine ⟨69059944586776046736215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 184159852231402791296573 69059944586776046736215)
          ·
            refine ⟨103589916880164070104323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69059944586776046736215 103589916880164070104323)
            ·
              refine ⟨155384875320246105156485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103589916880164070104323 155384875320246105156485)
              ·
                refine ⟨29134664122546144716841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 155384875320246105156485 29134664122546144716841)
                ·
                  rfl

theorem cell19_95748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 1, 4].length) (baseStart_95748 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_95748 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_95748 prefixEnd_95748 := by exact prefixLift 95748
  have htrace : WordTrace (prefixWord ++ tailWord_95748) baseStart_95748 baseEnd_95748 := by
    simpa [prefixWord, tailWord_95748, baseEnd_95748] using wordTrace_append hprefix tailTrace_95748
  have hstable : (prefixWord ++ tailWord_95748).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95748).length < 2 ^ (prefixWord ++ tailWord_95748).sum := by decide
  have hdescent : baseEnd_95748 < baseStart_95748 := by decide
  rcases family_descends (prefixWord ++ tailWord_95748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95790 : List Nat := [4, 1, 3, 1, 2, 2, 6]
def baseStart_95790 : Nat := 118140960795 + 95790 * 2 ^ 59
def prefixEnd_95790 : Nat := 4983230072969 + 3 ^ 40 * 95790 * 2
def baseEnd_95790 : Nat := 9715814695167497261131

theorem tailTrace_95790 : CollatzResearch.WordTrace tailWord_95790 prefixEnd_95790 9715814695167497261131 := by
  unfold tailWord_95790
  simp only [CollatzResearch.WordTrace]
  refine ⟨436718540372083059331603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2329165548651109649768549 436718540372083059331603)
  ·
    refine ⟨655077810558124588997405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 436718540372083059331603 655077810558124588997405)
    ·
      refine ⟨245654178959296720874027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 655077810558124588997405 245654178959296720874027)
      ·
        refine ⟨368481268438945081311041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245654178959296720874027 368481268438945081311041)
        ·
          refine ⟨276360951329208810983281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 368481268438945081311041 276360951329208810983281)
          ·
            refine ⟨207270713496906608237461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 276360951329208810983281 207270713496906608237461)
            ·
              refine ⟨9715814695167497261131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 207270713496906608237461 9715814695167497261131)
              ·
                rfl

theorem cell19_95790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 6].length) (baseStart_95790 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_95790 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_95790 prefixEnd_95790 := by exact prefixLift 95790
  have htrace : WordTrace (prefixWord ++ tailWord_95790) baseStart_95790 baseEnd_95790 := by
    simpa [prefixWord, tailWord_95790, baseEnd_95790] using wordTrace_append hprefix tailTrace_95790
  have hstable : (prefixWord ++ tailWord_95790).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95790).length < 2 ^ (prefixWord ++ tailWord_95790).sum := by decide
  have hdescent : baseEnd_95790 < baseStart_95790 := by decide
  rcases family_descends (prefixWord ++ tailWord_95790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95826 : List Nat := [3, 2, 2, 1, 2, 4, 2, 3]
def baseStart_95826 : Nat := 118140960795 + 95826 * 2 ^ 59
def prefixEnd_95826 : Nat := 4983230072969 + 3 ^ 40 * 95826 * 2
def baseEnd_95826 : Nat := 29158398339465074983295

theorem tailTrace_95826 : CollatzResearch.WordTrace tailWord_95826 prefixEnd_95826 29158398339465074983295 := by
  unfold tailWord_95826
  simp only [CollatzResearch.WordTrace]
  refine ⟨873765337711560655740833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2330040900564161748642221 873765337711560655740833)
  ·
    refine ⟨655324003283670491805625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 873765337711560655740833 655324003283670491805625)
    ·
      refine ⟨491493002462752868854219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 655324003283670491805625 491493002462752868854219)
      ·
        refine ⟨737239503694129303281329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 491493002462752868854219 737239503694129303281329)
        ·
          refine ⟨552929627770596977460997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 737239503694129303281329 552929627770596977460997)
          ·
            refine ⟨103674305206986933273937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 552929627770596977460997 103674305206986933273937)
            ·
              refine ⟨77755728905240199955453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103674305206986933273937 77755728905240199955453)
              ·
                refine ⟨29158398339465074983295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77755728905240199955453 29158398339465074983295)
                ·
                  rfl

theorem cell19_95826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 2, 3].length) (baseStart_95826 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_95826 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_95826 prefixEnd_95826 := by exact prefixLift 95826
  have htrace : WordTrace (prefixWord ++ tailWord_95826) baseStart_95826 baseEnd_95826 := by
    simpa [prefixWord, tailWord_95826, baseEnd_95826] using wordTrace_append hprefix tailTrace_95826
  have hstable : (prefixWord ++ tailWord_95826).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95826).length < 2 ^ (prefixWord ++ tailWord_95826).sum := by decide
  have hdescent : baseEnd_95826 < baseStart_95826 := by decide
  rcases family_descends (prefixWord ++ tailWord_95826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95982 : List Nat := [4, 1, 2, 1, 1, 2, 2, 6]
def baseStart_95982 : Nat := 118140960795 + 95982 * 2 ^ 59
def prefixEnd_95982 : Nat := 4983230072969 + 3 ^ 40 * 95982 * 2
def baseEnd_95982 : Nat := 29205866773302935516203

theorem tailTrace_95982 : CollatzResearch.WordTrace tailWord_95982 prefixEnd_95982 29205866773302935516203 := by
  unfold tailWord_95982
  simp only [CollatzResearch.WordTrace]
  refine ⟨437593892285135158205275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2333834092187387510428133 437593892285135158205275)
  ·
    refine ⟨656390838427702737307913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 437593892285135158205275 656390838427702737307913)
    ·
      refine ⟨492293128820777052980935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 656390838427702737307913 492293128820777052980935)
      ·
        refine ⟨738439693231165579471403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 492293128820777052980935 738439693231165579471403)
        ·
          refine ⟨1107659539846748369207105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 738439693231165579471403 1107659539846748369207105)
          ·
            refine ⟨830744654885061276905329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1107659539846748369207105 830744654885061276905329)
            ·
              refine ⟨623058491163795957678997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 830744654885061276905329 623058491163795957678997)
              ·
                refine ⟨29205866773302935516203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 623058491163795957678997 29205866773302935516203)
                ·
                  rfl

theorem cell19_95982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 6].length) (baseStart_95982 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_95982 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_95982 prefixEnd_95982 := by exact prefixLift 95982
  have htrace : WordTrace (prefixWord ++ tailWord_95982) baseStart_95982 baseEnd_95982 := by
    simpa [prefixWord, tailWord_95982, baseEnd_95982] using wordTrace_append hprefix tailTrace_95982
  have hstable : (prefixWord ++ tailWord_95982).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95982).length < 2 ^ (prefixWord ++ tailWord_95982).sum := by decide
  have hdescent : baseEnd_95982 < baseStart_95982 := by decide
  rcases family_descends (prefixWord ++ tailWord_95982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96018 : List Nat := [3, 2, 4, 1, 1, 1, 7]
def baseStart_96018 : Nat := 118140960795 + 96018 * 2 ^ 59
def prefixEnd_96018 : Nat := 4983230072969 + 3 ^ 40 * 96018 * 2
def baseEnd_96018 : Nat := 9738940342421839572035

theorem tailTrace_96018 : CollatzResearch.WordTrace tailWord_96018 prefixEnd_96018 9738940342421839572035 := by
  unfold tailWord_96018
  simp only [CollatzResearch.WordTrace]
  refine ⟨875516041537664853488177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2334709444100439609301805 875516041537664853488177)
  ·
    refine ⟨656637031153248640116133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 875516041537664853488177 656637031153248640116133)
    ·
      refine ⟨123119443341234120021775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 656637031153248640116133 123119443341234120021775)
      ·
        refine ⟨184679165011851180032663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123119443341234120021775 184679165011851180032663)
        ·
          refine ⟨277018747517776770048995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184679165011851180032663 277018747517776770048995)
          ·
            refine ⟨415528121276665155073493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 277018747517776770048995 415528121276665155073493)
            ·
              refine ⟨9738940342421839572035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 415528121276665155073493 9738940342421839572035)
              ·
                rfl

theorem cell19_96018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 7].length) (baseStart_96018 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_96018 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_96018 prefixEnd_96018 := by exact prefixLift 96018
  have htrace : WordTrace (prefixWord ++ tailWord_96018) baseStart_96018 baseEnd_96018 := by
    simpa [prefixWord, tailWord_96018, baseEnd_96018] using wordTrace_append hprefix tailTrace_96018
  have hstable : (prefixWord ++ tailWord_96018).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96018).length < 2 ^ (prefixWord ++ tailWord_96018).sum := by decide
  have hdescent : baseEnd_96018 < baseStart_96018 := by decide
  rcases family_descends (prefixWord ++ tailWord_96018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96058 : List Nat := [3, 1, 1, 1, 5, 1, 2, 5]
def baseStart_96058 : Nat := 118140960795 + 96058 * 2 ^ 59
def prefixEnd_96058 : Nat := 4983230072969 + 3 ^ 40 * 96058 * 2
def baseEnd_96058 : Nat := 29228992420557277827107

theorem tailTrace_96058 : CollatzResearch.WordTrace tailWord_96058 prefixEnd_96058 29228992420557277827107 := by
  unfold tailWord_96058
  simp only [CollatzResearch.WordTrace]
  refine ⟨875880771501436561352207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2335682057337164163605885 875880771501436561352207)
  ·
    refine ⟨1313821157252154842028311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 875880771501436561352207 1313821157252154842028311)
    ·
      refine ⟨1970731735878232263042467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1313821157252154842028311 1970731735878232263042467)
      ·
        refine ⟨2956097603817348394563701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1970731735878232263042467 2956097603817348394563701)
        ·
          refine ⟨277134150357876411990347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2956097603817348394563701 277134150357876411990347)
          ·
            refine ⟨415701225536814617985521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 277134150357876411990347 415701225536814617985521)
            ·
              refine ⟨311775919152610963489141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 415701225536814617985521 311775919152610963489141)
              ·
                refine ⟨29228992420557277827107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 311775919152610963489141 29228992420557277827107)
                ·
                  rfl

theorem cell19_96058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 5].length) (baseStart_96058 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_96058 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_96058 prefixEnd_96058 := by exact prefixLift 96058
  have htrace : WordTrace (prefixWord ++ tailWord_96058) baseStart_96058 baseEnd_96058 := by
    simpa [prefixWord, tailWord_96058, baseEnd_96058] using wordTrace_append hprefix tailTrace_96058
  have hstable : (prefixWord ++ tailWord_96058).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96058).length < 2 ^ (prefixWord ++ tailWord_96058).sum := by decide
  have hdescent : baseEnd_96058 < baseStart_96058 := by decide
  rcases family_descends (prefixWord ++ tailWord_96058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96092 : List Nat := [2, 2, 4, 2, 2, 2, 1, 4]
def baseStart_96092 : Nat := 118140960795 + 96092 * 2 ^ 59
def prefixEnd_96092 : Nat := 4983230072969 + 3 ^ 40 * 96092 * 2
def baseEnd_96092 : Nat := 29239338104855273071459

theorem tailTrace_96092 : CollatzResearch.WordTrace tailWord_96092 prefixEnd_96092 29239338104855273071459 := by
  unfold tailWord_96092
  simp only [CollatzResearch.WordTrace]
  refine ⟨1752381583941285026073265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2336508778588380034764353 1752381583941285026073265)
  ·
    refine ⟨1314286187955963769554949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1752381583941285026073265 1314286187955963769554949)
    ·
      refine ⟨246428660241743206791553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1314286187955963769554949 246428660241743206791553)
      ·
        refine ⟨184821495181307405093665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 246428660241743206791553 184821495181307405093665)
        ·
          refine ⟨138616121385980553820249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 184821495181307405093665 138616121385980553820249)
          ·
            refine ⟨103962091039485415365187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 138616121385980553820249 103962091039485415365187)
            ·
              refine ⟨155943136559228123047781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103962091039485415365187 155943136559228123047781)
              ·
                refine ⟨29239338104855273071459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 155943136559228123047781 29239338104855273071459)
                ·
                  rfl

theorem cell19_96092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 1, 4].length) (baseStart_96092 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_96092 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_96092 prefixEnd_96092 := by exact prefixLift 96092
  have htrace : WordTrace (prefixWord ++ tailWord_96092) baseStart_96092 baseEnd_96092 := by
    simpa [prefixWord, tailWord_96092, baseEnd_96092] using wordTrace_append hprefix tailTrace_96092
  have hstable : (prefixWord ++ tailWord_96092).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96092).length < 2 ^ (prefixWord ++ tailWord_96092).sum := by decide
  have hdescent : baseEnd_96092 < baseStart_96092 := by decide
  rcases family_descends (prefixWord ++ tailWord_96092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96096 : List Nat := [2, 1, 1, 3, 3, 2, 3, 4]
def baseStart_96096 : Nat := 118140960795 + 96096 * 2 ^ 59
def prefixEnd_96096 : Nat := 4983230072969 + 3 ^ 40 * 96096 * 2
def baseEnd_96096 : Nat := 29240555244184448982559

theorem tailTrace_96096 : CollatzResearch.WordTrace tailWord_96096 prefixEnd_96096 29240555244184448982559 := by
  unfold tailWord_96096
  simp only [CollatzResearch.WordTrace]
  refine ⟨1752454529934039367646071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2336606039912052490194761 1752454529934039367646071)
  ·
    refine ⟨2628681794901059051469107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1752454529934039367646071 2628681794901059051469107)
    ·
      refine ⟨3943022692351588577203661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2628681794901059051469107 3943022692351588577203661)
      ·
        refine ⟨1478633509631845716451373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3943022692351588577203661 1478633509631845716451373)
        ·
          refine ⟨554487566111942143669265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1478633509631845716451373 554487566111942143669265)
          ·
            refine ⟨415865674583956607751949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 554487566111942143669265 415865674583956607751949)
            ·
              refine ⟨155949627968983727906981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 415865674583956607751949 155949627968983727906981)
              ·
                refine ⟨29240555244184448982559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 155949627968983727906981 29240555244184448982559)
                ·
                  rfl

theorem cell19_96096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 3, 4].length) (baseStart_96096 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_96096 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_96096 prefixEnd_96096 := by exact prefixLift 96096
  have htrace : WordTrace (prefixWord ++ tailWord_96096) baseStart_96096 baseEnd_96096 := by
    simpa [prefixWord, tailWord_96096, baseEnd_96096] using wordTrace_append hprefix tailTrace_96096
  have hstable : (prefixWord ++ tailWord_96096).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96096).length < 2 ^ (prefixWord ++ tailWord_96096).sum := by decide
  have hdescent : baseEnd_96096 < baseStart_96096 := by decide
  rcases family_descends (prefixWord ++ tailWord_96096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96168 : List Nat := [2, 1, 6, 2, 1, 1, 1, 5]
def baseStart_96168 : Nat := 118140960795 + 96168 * 2 ^ 59
def prefixEnd_96168 : Nat := 4983230072969 + 3 ^ 40 * 96168 * 2
def baseEnd_96168 : Nat := 29262463752109615382363

theorem tailTrace_96168 : CollatzResearch.WordTrace tailWord_96168 prefixEnd_96168 29262463752109615382363 := by
  unfold tailWord_96168
  simp only [CollatzResearch.WordTrace]
  refine ⟨1753767557803617515956579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2338356743738156687942105 1753767557803617515956579)
  ·
    refine ⟨2630651336705426273934869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1753767557803617515956579 2630651336705426273934869)
    ·
      refine ⟨123311781408066856590697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 2630651336705426273934869 123311781408066856590697)
      ·
        refine ⟨92483836056050142443023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123311781408066856590697 92483836056050142443023)
        ·
          refine ⟨138725754084075213664535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92483836056050142443023 138725754084075213664535)
          ·
            refine ⟨208088631126112820496803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138725754084075213664535 208088631126112820496803)
            ·
              refine ⟨312132946689169230745205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 208088631126112820496803 312132946689169230745205)
              ·
                refine ⟨29262463752109615382363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 312132946689169230745205 29262463752109615382363)
                ·
                  rfl

theorem cell19_96168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 5].length) (baseStart_96168 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_96168 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_96168 prefixEnd_96168 := by exact prefixLift 96168
  have htrace : WordTrace (prefixWord ++ tailWord_96168) baseStart_96168 baseEnd_96168 := by
    simpa [prefixWord, tailWord_96168, baseEnd_96168] using wordTrace_append hprefix tailTrace_96168
  have hstable : (prefixWord ++ tailWord_96168).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96168).length < 2 ^ (prefixWord ++ tailWord_96168).sum := by decide
  have hdescent : baseEnd_96168 < baseStart_96168 := by decide
  rcases family_descends (prefixWord ++ tailWord_96168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96246 : List Nat := [5, 1, 1, 1, 5, 6]
def baseStart_96246 : Nat := 118140960795 + 96246 * 2 ^ 59
def prefixEnd_96246 : Nat := 4983230072969 + 3 ^ 40 * 96246 * 2
def baseEnd_96246 : Nat := 3254021996558727294313

theorem tailTrace_96246 : CollatzResearch.WordTrace tailWord_96246 prefixEnd_96246 3254021996558727294313 := by
  unfold tailWord_96246
  simp only [CollatzResearch.WordTrace]
  refine ⟨219398750582790897078287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2340253339549769568835061 219398750582790897078287)
  ·
    refine ⟨329098125874186345617431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219398750582790897078287 329098125874186345617431)
    ·
      refine ⟨493647188811279518426147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 329098125874186345617431 493647188811279518426147)
      ·
        refine ⟨740470783216919277639221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 493647188811279518426147 740470783216919277639221)
        ·
          refine ⟨69419135926586182278677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 740470783216919277639221 69419135926586182278677)
          ·
            refine ⟨3254021996558727294313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 69419135926586182278677 3254021996558727294313)
            ·
              rfl

theorem cell19_96246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 6].length) (baseStart_96246 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_96246 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_96246 prefixEnd_96246 := by exact prefixLift 96246
  have htrace : WordTrace (prefixWord ++ tailWord_96246) baseStart_96246 baseEnd_96246 := by
    simpa [prefixWord, tailWord_96246, baseEnd_96246] using wordTrace_append hprefix tailTrace_96246
  have hstable : (prefixWord ++ tailWord_96246).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96246).length < 2 ^ (prefixWord ++ tailWord_96246).sum := by decide
  have hdescent : baseEnd_96246 < baseStart_96246 := by decide
  rcases family_descends (prefixWord ++ tailWord_96246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96284 : List Nat := [2, 2, 3, 1, 3, 2, 3, 3]
def baseStart_96284 : Nat := 118140960795 + 96284 * 2 ^ 59
def prefixEnd_96284 : Nat := 4983230072969 + 3 ^ 40 * 96284 * 2
def baseEnd_96284 : Nat := 29297760792655716804269

theorem tailTrace_96284 : CollatzResearch.WordTrace tailWord_96284 prefixEnd_96284 29297760792655716804269 := by
  unfold tailWord_96284
  simp only [CollatzResearch.WordTrace]
  refine ⟨1755882991593493421567953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2341177322124657895423937 1755882991593493421567953)
  ·
    refine ⟨1316912243695120066175965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1755882991593493421567953 1316912243695120066175965)
    ·
      refine ⟨493842091385670024815987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1316912243695120066175965 493842091385670024815987)
      ·
        refine ⟨740763137078505037223981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 493842091385670024815987 740763137078505037223981)
        ·
          refine ⟨277786176404439388958993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 740763137078505037223981 277786176404439388958993)
          ·
            refine ⟨208339632303329541719245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 277786176404439388958993 208339632303329541719245)
            ·
              refine ⟨78127362113748578144717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 208339632303329541719245 78127362113748578144717)
              ·
                refine ⟨29297760792655716804269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78127362113748578144717 29297760792655716804269)
                ·
                  rfl

theorem cell19_96284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 3, 3].length) (baseStart_96284 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_96284 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_96284 prefixEnd_96284 := by exact prefixLift 96284
  have htrace : WordTrace (prefixWord ++ tailWord_96284) baseStart_96284 baseEnd_96284 := by
    simpa [prefixWord, tailWord_96284, baseEnd_96284] using wordTrace_append hprefix tailTrace_96284
  have hstable : (prefixWord ++ tailWord_96284).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96284).length < 2 ^ (prefixWord ++ tailWord_96284).sum := by decide
  have hdescent : baseEnd_96284 < baseStart_96284 := by decide
  rcases family_descends (prefixWord ++ tailWord_96284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96341 : List Nat := [1, 3, 2, 2, 1, 5, 2, 3]
def baseStart_96341 : Nat := 118140960795 + 96341 * 2 ^ 59
def prefixEnd_96341 : Nat := 4983230072969 + 3 ^ 40 * 96341 * 2
def baseEnd_96341 : Nat := 29315105028096473537447

theorem tailTrace_96341 : CollatzResearch.WordTrace tailWord_96341 prefixEnd_96341 29315105028096473537447 := by
  unfold tailWord_96341
  simp only [CollatzResearch.WordTrace]
  refine ⟨3513844943980485577960877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2342563295986990385307251 3513844943980485577960877)
  ·
    refine ⟨1317691853992682091735329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3513844943980485577960877 1317691853992682091735329)
    ·
      refine ⟨988268890494511568801497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1317691853992682091735329 988268890494511568801497)
      ·
        refine ⟨741201667870883676601123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 988268890494511568801497 741201667870883676601123)
        ·
          refine ⟨1111802501806325514901685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 741201667870883676601123 1111802501806325514901685)
          ·
            refine ⟨104231484544343017022033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1111802501806325514901685 104231484544343017022033)
            ·
              refine ⟨78173613408257262766525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104231484544343017022033 78173613408257262766525)
              ·
                refine ⟨29315105028096473537447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78173613408257262766525 29315105028096473537447)
                ·
                  rfl

theorem cell19_96341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 2, 3].length) (baseStart_96341 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_96341 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_96341 prefixEnd_96341 := by exact prefixLift 96341
  have htrace : WordTrace (prefixWord ++ tailWord_96341) baseStart_96341 baseEnd_96341 := by
    simpa [prefixWord, tailWord_96341, baseEnd_96341] using wordTrace_append hprefix tailTrace_96341
  have hstable : (prefixWord ++ tailWord_96341).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96341).length < 2 ^ (prefixWord ++ tailWord_96341).sum := by decide
  have hdescent : baseEnd_96341 < baseStart_96341 := by decide
  rcases family_descends (prefixWord ++ tailWord_96341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96343 : List Nat := [1, 1, 3, 2, 2, 1, 6, 3]
def baseStart_96343 : Nat := 118140960795 + 96343 * 2 ^ 59
def prefixEnd_96343 : Nat := 4983230072969 + 3 ^ 40 * 96343 * 2
def baseEnd_96343 : Nat := 29315713597761061492997

theorem tailTrace_96343 : CollatzResearch.WordTrace tailWord_96343 prefixEnd_96343 29315713597761061492997 := by
  unfold tailWord_96343
  simp only [CollatzResearch.WordTrace]
  refine ⟨3513917889973239919533683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2342611926648826613022455 3513917889973239919533683)
  ·
    refine ⟨5270876834959859879300525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3513917889973239919533683 5270876834959859879300525)
    ·
      refine ⟨1976578813109947454737697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5270876834959859879300525 1976578813109947454737697)
      ·
        refine ⟨1482434109832460591053273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1976578813109947454737697 1482434109832460591053273)
        ·
          refine ⟨1111825582374345443289955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1482434109832460591053273 1111825582374345443289955)
          ·
            refine ⟨1667738373561518164934933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1111825582374345443289955 1667738373561518164934933)
            ·
              refine ⟨78175236260696163981325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1667738373561518164934933 78175236260696163981325)
              ·
                refine ⟨29315713597761061492997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78175236260696163981325 29315713597761061492997)
                ·
                  rfl

theorem cell19_96343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 6, 3].length) (baseStart_96343 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_96343 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_96343 prefixEnd_96343 := by exact prefixLift 96343
  have htrace : WordTrace (prefixWord ++ tailWord_96343) baseStart_96343 baseEnd_96343 := by
    simpa [prefixWord, tailWord_96343, baseEnd_96343] using wordTrace_append hprefix tailTrace_96343
  have hstable : (prefixWord ++ tailWord_96343).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96343).length < 2 ^ (prefixWord ++ tailWord_96343).sum := by decide
  have hdescent : baseEnd_96343 < baseStart_96343 := by decide
  rcases family_descends (prefixWord ++ tailWord_96343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96345 : List Nat := [1, 2, 1, 2, 2, 1, 5, 5]
def baseStart_96345 : Nat := 118140960795 + 96345 * 2 ^ 59
def prefixEnd_96345 : Nat := 4983230072969 + 3 ^ 40 * 96345 * 2
def baseEnd_96345 : Nat := 29316322167425649448547

theorem tailTrace_96345 : CollatzResearch.WordTrace tailWord_96345 prefixEnd_96345 29316322167425649448547 := by
  unfold tailWord_96345
  simp only [CollatzResearch.WordTrace]
  refine ⟨3513990835965994261106489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2342660557310662840737659 3513990835965994261106489)
  ·
    refine ⟨2635493126974495695829867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3513990835965994261106489 2635493126974495695829867)
    ·
      refine ⟨3953239690461743543744801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2635493126974495695829867 3953239690461743543744801)
      ·
        refine ⟨2964929767846307657808601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3953239690461743543744801 2964929767846307657808601)
        ·
          refine ⟨2223697325884730743356451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2964929767846307657808601 2223697325884730743356451)
          ·
            refine ⟨3335545988827096115034677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2223697325884730743356451 3335545988827096115034677)
            ·
              refine ⟨312707436452540260784501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3335545988827096115034677 312707436452540260784501)
              ·
                refine ⟨29316322167425649448547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 312707436452540260784501 29316322167425649448547)
                ·
                  rfl

theorem cell19_96345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 5].length) (baseStart_96345 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_96345 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_96345 prefixEnd_96345 := by exact prefixLift 96345
  have htrace : WordTrace (prefixWord ++ tailWord_96345) baseStart_96345 baseEnd_96345 := by
    simpa [prefixWord, tailWord_96345, baseEnd_96345] using wordTrace_append hprefix tailTrace_96345
  have hstable : (prefixWord ++ tailWord_96345).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96345).length < 2 ^ (prefixWord ++ tailWord_96345).sum := by decide
  have hdescent : baseEnd_96345 < baseStart_96345 := by decide
  rcases family_descends (prefixWord ++ tailWord_96345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96364 : List Nat := [2, 2, 1, 1, 3, 3, 7]
def baseStart_96364 : Nat := 118140960795 + 96364 * 2 ^ 59
def prefixEnd_96364 : Nat := 4983230072969 + 3 ^ 40 * 96364 * 2
def baseEnd_96364 : Nat := 9774034526413078342091

theorem tailTrace_96364 : CollatzResearch.WordTrace tailWord_96364 prefixEnd_96364 9774034526413078342091 := by
  unfold tailWord_96364
  simp only [CollatzResearch.WordTrace]
  refine ⟨1757341911448580253024073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2343122548598107004032097 1757341911448580253024073)
  ·
    refine ⟨1318006433586435189768055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1757341911448580253024073 1318006433586435189768055)
    ·
      refine ⟨1977009650379652784652083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1318006433586435189768055 1977009650379652784652083)
      ·
        refine ⟨2965514475569479176978125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1977009650379652784652083 2965514475569479176978125)
        ·
          refine ⟨1112067928338554691366797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2965514475569479176978125 1112067928338554691366797)
          ·
            refine ⟨417025473126958009262549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1112067928338554691366797 417025473126958009262549)
            ·
              refine ⟨9774034526413078342091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 417025473126958009262549 9774034526413078342091)
              ·
                rfl

theorem cell19_96364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 7].length) (baseStart_96364 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_96364 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_96364 prefixEnd_96364 := by exact prefixLift 96364
  have htrace : WordTrace (prefixWord ++ tailWord_96364) baseStart_96364 baseEnd_96364 := by
    simpa [prefixWord, tailWord_96364, baseEnd_96364] using wordTrace_append hprefix tailTrace_96364
  have hstable : (prefixWord ++ tailWord_96364).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96364).length < 2 ^ (prefixWord ++ tailWord_96364).sum := by decide
  have hdescent : baseEnd_96364 < baseStart_96364 := by decide
  rcases family_descends (prefixWord ++ tailWord_96364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96381 : List Nat := [1, 4, 1, 1, 3, 3, 2, 4]
def baseStart_96381 : Nat := 118140960795 + 96381 * 2 ^ 59
def prefixEnd_96381 : Nat := 4983230072969 + 3 ^ 40 * 96381 * 2
def baseEnd_96381 : Nat := 29327276421388232648449

theorem tailTrace_96381 : CollatzResearch.WordTrace tailWord_96381 prefixEnd_96381 29327276421388232648449 := by
  unfold tailWord_96381
  simp only [CollatzResearch.WordTrace]
  refine ⟨3515303863835572409416997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2343535909223714939611331 3515303863835572409416997)
  ·
    refine ⟨659119474469169826765687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3515303863835572409416997 659119474469169826765687)
    ·
      refine ⟨988679211703754740148531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 659119474469169826765687 988679211703754740148531)
      ·
        refine ⟨1483018817555632110222797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 988679211703754740148531 1483018817555632110222797)
        ·
          refine ⟨556132056583362041333549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1483018817555632110222797 556132056583362041333549)
          ·
            refine ⟨208549521218760765500081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 556132056583362041333549 208549521218760765500081)
            ·
              refine ⟨156412140914070574125061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 208549521218760765500081 156412140914070574125061)
              ·
                refine ⟨29327276421388232648449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 156412140914070574125061 29327276421388232648449)
                ·
                  rfl

theorem cell19_96381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 2, 4].length) (baseStart_96381 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_96381 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_96381 prefixEnd_96381 := by exact prefixLift 96381
  have htrace : WordTrace (prefixWord ++ tailWord_96381) baseStart_96381 baseEnd_96381 := by
    simpa [prefixWord, tailWord_96381, baseEnd_96381] using wordTrace_append hprefix tailTrace_96381
  have hstable : (prefixWord ++ tailWord_96381).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96381).length < 2 ^ (prefixWord ++ tailWord_96381).sum := by decide
  have hdescent : baseEnd_96381 < baseStart_96381 := by decide
  rcases family_descends (prefixWord ++ tailWord_96381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96535 : List Nat := [1, 1, 3, 4, 1, 2, 7]
def baseStart_96535 : Nat := 118140960795 + 96535 * 2 ^ 59
def prefixEnd_96535 : Nat := 4983230072969 + 3 ^ 40 * 96535 * 2
def baseEnd_96535 : Nat := 9791378761853835075269

theorem tailTrace_96535 : CollatzResearch.WordTrace tailWord_96535 prefixEnd_96535 9791378761853835075269 := by
  unfold tailWord_96535
  simp only [CollatzResearch.WordTrace]
  refine ⟨3520920705277656710523059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2347280470185104473682039 3520920705277656710523059)
  ·
    refine ⟨5281381057916485065784589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3520920705277656710523059 5281381057916485065784589)
    ·
      refine ⟨1980517896718681899669221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5281381057916485065784589 1980517896718681899669221)
      ·
        refine ⟨371347105634752856187979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1980517896718681899669221 371347105634752856187979)
        ·
          refine ⟨557020658452129284281969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 371347105634752856187979 557020658452129284281969)
          ·
            refine ⟨417765493839096963211477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 557020658452129284281969 417765493839096963211477)
            ·
              refine ⟨9791378761853835075269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 417765493839096963211477 9791378761853835075269)
              ·
                rfl

theorem cell19_96535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 7].length) (baseStart_96535 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_96535 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_96535 prefixEnd_96535 := by exact prefixLift 96535
  have htrace : WordTrace (prefixWord ++ tailWord_96535) baseStart_96535 baseEnd_96535 := by
    simpa [prefixWord, tailWord_96535, baseEnd_96535] using wordTrace_append hprefix tailTrace_96535
  have hstable : (prefixWord ++ tailWord_96535).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96535).length < 2 ^ (prefixWord ++ tailWord_96535).sum := by decide
  have hdescent : baseEnd_96535 < baseStart_96535 := by decide
  rcases family_descends (prefixWord ++ tailWord_96535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96649 : List Nat := [1, 2, 1, 1, 6, 2, 6]
def baseStart_96649 : Nat := 118140960795 + 96649 * 2 ^ 59
def prefixEnd_96649 : Nat := 4983230072969 + 3 ^ 40 * 96649 * 2
def baseEnd_96649 : Nat := 9802941585481006230721

theorem tailTrace_96649 : CollatzResearch.WordTrace tailWord_96649 prefixEnd_96649 9802941585481006230721 := by
  unfold tailWord_96649
  simp only [CollatzResearch.WordTrace]
  refine ⟨3525078626864654180173001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2350052417909769453448667 3525078626864654180173001)
  ·
    refine ⟨2643808970148490635129751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3525078626864654180173001 2643808970148490635129751)
    ·
      refine ⟨3965713455222735952694627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2643808970148490635129751 3965713455222735952694627)
      ·
        refine ⟨5948570182834103929041941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3965713455222735952694627 5948570182834103929041941)
        ·
          refine ⟨278839227320348621673841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 5948570182834103929041941 278839227320348621673841)
          ·
            refine ⟨209129420490261466255381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 278839227320348621673841 209129420490261466255381)
            ·
              refine ⟨9802941585481006230721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 209129420490261466255381 9802941585481006230721)
              ·
                rfl

theorem cell19_96649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 6].length) (baseStart_96649 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_96649 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_96649 prefixEnd_96649 := by exact prefixLift 96649
  have htrace : WordTrace (prefixWord ++ tailWord_96649) baseStart_96649 baseEnd_96649 := by
    simpa [prefixWord, tailWord_96649, baseEnd_96649] using wordTrace_append hprefix tailTrace_96649
  have hstable : (prefixWord ++ tailWord_96649).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96649).length < 2 ^ (prefixWord ++ tailWord_96649).sum := by decide
  have hdescent : baseEnd_96649 < baseStart_96649 := by decide
  rcases family_descends (prefixWord ++ tailWord_96649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96725 : List Nat := [1, 3, 2, 3, 1, 2, 1, 6]
def baseStart_96725 : Nat := 118140960795 + 96725 * 2 ^ 59
def prefixEnd_96725 : Nat := 4983230072969 + 3 ^ 40 * 96725 * 2
def baseEnd_96725 : Nat := 29431950403697361003067

theorem tailTrace_96725 : CollatzResearch.WordTrace tailWord_96725 prefixEnd_96725 29431950403697361003067 := by
  unfold tailWord_96725
  simp only [CollatzResearch.WordTrace]
  refine ⟨3527850574589319159939629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2351900383059546106626419 3527850574589319159939629)
  ·
    refine ⟨1322943965470994684977361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3527850574589319159939629 1322943965470994684977361)
    ·
      refine ⟨992207974103246013733021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1322943965470994684977361 992207974103246013733021)
      ·
        refine ⟨372077990288717255149883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 992207974103246013733021 372077990288717255149883)
        ·
          refine ⟨558116985433075882724825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 372077990288717255149883 558116985433075882724825)
          ·
            refine ⟨418587739074806912043619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 558116985433075882724825 418587739074806912043619)
            ·
              refine ⟨627881608612210368065429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 418587739074806912043619 627881608612210368065429)
              ·
                refine ⟨29431950403697361003067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 627881608612210368065429 29431950403697361003067)
                ·
                  rfl

theorem cell19_96725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 6].length) (baseStart_96725 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_96725 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_96725 prefixEnd_96725 := by exact prefixLift 96725
  have htrace : WordTrace (prefixWord ++ tailWord_96725) baseStart_96725 baseEnd_96725 := by
    simpa [prefixWord, tailWord_96725, baseEnd_96725] using wordTrace_append hprefix tailTrace_96725
  have hstable : (prefixWord ++ tailWord_96725).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96725).length < 2 ^ (prefixWord ++ tailWord_96725).sum := by decide
  have hdescent : baseEnd_96725 < baseStart_96725 := by decide
  rcases family_descends (prefixWord ++ tailWord_96725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96744 : List Nat := [2, 1, 4, 1, 1, 3, 2, 5]
def baseStart_96744 : Nat := 118140960795 + 96744 * 2 ^ 59
def prefixEnd_96744 : Nat := 4983230072969 + 3 ^ 40 * 96744 * 2
def baseEnd_96744 : Nat := 29437731815510946580793

theorem tailTrace_96744 : CollatzResearch.WordTrace tailWord_96744 prefixEnd_96744 29437731815510946580793 := by
  unfold tailWord_96744
  simp only [CollatzResearch.WordTrace]
  refine ⟨1764271780760242702440643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2352362374346990269920857 1764271780760242702440643)
  ·
    refine ⟨2646407671140364053660965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1764271780760242702440643 2646407671140364053660965)
    ·
      refine ⟨496201438338818260061431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2646407671140364053660965 496201438338818260061431)
      ·
        refine ⟨744302157508227390092147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 496201438338818260061431 744302157508227390092147)
        ·
          refine ⟨1116453236262341085138221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 744302157508227390092147 1116453236262341085138221)
          ·
            refine ⟨418669963598377906926833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1116453236262341085138221 418669963598377906926833)
            ·
              refine ⟨314002472698783430195125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 418669963598377906926833 314002472698783430195125)
              ·
                refine ⟨29437731815510946580793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 314002472698783430195125 29437731815510946580793)
                ·
                  rfl

theorem cell19_96744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 5].length) (baseStart_96744 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_96744 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_96744 prefixEnd_96744 := by exact prefixLift 96744
  have htrace : WordTrace (prefixWord ++ tailWord_96744) baseStart_96744 baseEnd_96744 := by
    simpa [prefixWord, tailWord_96744, baseEnd_96744] using wordTrace_append hprefix tailTrace_96744
  have hstable : (prefixWord ++ tailWord_96744).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96744).length < 2 ^ (prefixWord ++ tailWord_96744).sum := by decide
  have hdescent : baseEnd_96744 < baseStart_96744 := by decide
  rcases family_descends (prefixWord ++ tailWord_96744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96774 : List Nat := [6, 2, 1, 1, 1, 3, 1, 4]
def baseStart_96774 : Nat := 118140960795 + 96774 * 2 ^ 59
def prefixEnd_96774 : Nat := 4983230072969 + 3 ^ 40 * 96774 * 2
def baseEnd_96774 : Nat := 29446860360479765914045

theorem tailTrace_96774 : CollatzResearch.WordTrace tailWord_96774 prefixEnd_96774 29446860360479765914045 := by
  unfold tailWord_96774
  simp only [CollatzResearch.WordTrace]
  refine ⟨110301179731618766514793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 2353091834274533685648917 110301179731618766514793)
  ·
    refine ⟨82725884798714074886095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110301179731618766514793 82725884798714074886095)
    ·
      refine ⟨124088827198071112329143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82725884798714074886095 124088827198071112329143)
      ·
        refine ⟨186133240797106668493715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124088827198071112329143 186133240797106668493715)
        ·
          refine ⟨279199861195660002740573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186133240797106668493715 279199861195660002740573)
          ·
            refine ⟨104699947948372501027715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 279199861195660002740573 104699947948372501027715)
            ·
              refine ⟨157049921922558751541573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104699947948372501027715 157049921922558751541573)
              ·
                refine ⟨29446860360479765914045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 157049921922558751541573 29446860360479765914045)
                ·
                  rfl

theorem cell19_96774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 1, 4].length) (baseStart_96774 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_96774 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_96774 prefixEnd_96774 := by exact prefixLift 96774
  have htrace : WordTrace (prefixWord ++ tailWord_96774) baseStart_96774 baseEnd_96774 := by
    simpa [prefixWord, tailWord_96774, baseEnd_96774] using wordTrace_append hprefix tailTrace_96774
  have hstable : (prefixWord ++ tailWord_96774).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96774).length < 2 ^ (prefixWord ++ tailWord_96774).sum := by decide
  have hdescent : baseEnd_96774 < baseStart_96774 := by decide
  rcases family_descends (prefixWord ++ tailWord_96774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96780 : List Nat := [2, 2, 1, 2, 4, 3, 1, 4]
def baseStart_96780 : Nat := 118140960795 + 96780 * 2 ^ 59
def prefixEnd_96780 : Nat := 4983230072969 + 3 ^ 40 * 96780 * 2
def baseEnd_96780 : Nat := 29448686069473529780695

theorem tailTrace_96780 : CollatzResearch.WordTrace tailWord_96780 prefixEnd_96780 29448686069473529780695 := by
  unfold tailWord_96780
  simp only [CollatzResearch.WordTrace]
  refine ⟨1764928294695031776595897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2353237726260042368794529 1764928294695031776595897)
  ·
    refine ⟨1323696221021273832446923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1764928294695031776595897 1323696221021273832446923)
    ·
      refine ⟨1985544331531910748670385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1323696221021273832446923 1985544331531910748670385)
      ·
        refine ⟨1489158248648933061502789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1985544331531910748670385 1489158248648933061502789)
        ·
          refine ⟨279217171621674949031773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1489158248648933061502789 279217171621674949031773)
          ·
            refine ⟨104706439358128105886915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 279217171621674949031773 104706439358128105886915)
            ·
              refine ⟨157059659037192158830373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104706439358128105886915 157059659037192158830373)
              ·
                refine ⟨29448686069473529780695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 157059659037192158830373 29448686069473529780695)
                ·
                  rfl

theorem cell19_96780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 1, 4].length) (baseStart_96780 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_96780 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_96780 prefixEnd_96780 := by exact prefixLift 96780
  have htrace : WordTrace (prefixWord ++ tailWord_96780) baseStart_96780 baseEnd_96780 := by
    simpa [prefixWord, tailWord_96780, baseEnd_96780] using wordTrace_append hprefix tailTrace_96780
  have hstable : (prefixWord ++ tailWord_96780).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96780).length < 2 ^ (prefixWord ++ tailWord_96780).sum := by decide
  have hdescent : baseEnd_96780 < baseStart_96780 := by decide
  rcases family_descends (prefixWord ++ tailWord_96780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96877 : List Nat := [1, 5, 1, 1, 3, 1, 7]
def baseStart_96877 : Nat := 118140960795 + 96877 * 2 ^ 59
def prefixEnd_96877 : Nat := 4983230072969 + 3 ^ 40 * 96877 * 2
def baseEnd_96877 : Nat := 9826067232735348541625

theorem tailTrace_96877 : CollatzResearch.WordTrace tailWord_96877 prefixEnd_96877 9826067232735348541625 := by
  unfold tailWord_96877
  simp only [CollatzResearch.WordTrace]
  refine ⟨3533394470038649119472885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2355596313359099412981923 3533394470038649119472885)
  ·
    refine ⟨331255731566123354950583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3533394470038649119472885 331255731566123354950583)
    ·
      refine ⟨496883597349185032425875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 331255731566123354950583 496883597349185032425875)
      ·
        refine ⟨745325396023777548638813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 496883597349185032425875 745325396023777548638813)
        ·
          refine ⟨279497023508916580739555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 745325396023777548638813 279497023508916580739555)
          ·
            refine ⟨419245535263374871109333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 279497023508916580739555 419245535263374871109333)
            ·
              refine ⟨9826067232735348541625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 419245535263374871109333 9826067232735348541625)
              ·
                rfl

theorem cell19_96877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 7].length) (baseStart_96877 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_96877 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_96877 prefixEnd_96877 := by exact prefixLift 96877
  have htrace : WordTrace (prefixWord ++ tailWord_96877) baseStart_96877 baseEnd_96877 := by
    simpa [prefixWord, tailWord_96877, baseEnd_96877] using wordTrace_append hprefix tailTrace_96877
  have hstable : (prefixWord ++ tailWord_96877).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96877).length < 2 ^ (prefixWord ++ tailWord_96877).sum := by decide
  have hdescent : baseEnd_96877 < baseStart_96877 := by decide
  rcases family_descends (prefixWord ++ tailWord_96877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96879 : List Nat := [1, 1, 2, 1, 3, 2, 9]
def baseStart_96879 : Nat := 118140960795 + 96879 * 2 ^ 59
def prefixEnd_96879 : Nat := 4983230072969 + 3 ^ 40 * 96879 * 2
def baseEnd_96879 : Nat := 9826270089290211193475

theorem tailTrace_96879 : CollatzResearch.WordTrace tailWord_96879 prefixEnd_96879 9826270089290211193475 := by
  unfold tailWord_96879
  simp only [CollatzResearch.WordTrace]
  refine ⟨3533467416031403461045691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2355644944020935640697127 3533467416031403461045691)
  ·
    refine ⟨5300201124047105191568537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3533467416031403461045691 5300201124047105191568537)
    ·
      refine ⟨3975150843035328893676403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5300201124047105191568537 3975150843035328893676403)
      ·
        refine ⟨5962726264552993340514605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3975150843035328893676403 5962726264552993340514605)
        ·
          refine ⟨2236022349207372502692977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5962726264552993340514605 2236022349207372502692977)
          ·
            refine ⟨1677016761905529377019733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2236022349207372502692977 1677016761905529377019733)
            ·
              refine ⟨9826270089290211193475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1677016761905529377019733 9826270089290211193475)
              ·
                rfl

theorem cell19_96879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 9].length) (baseStart_96879 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_96879 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_96879 prefixEnd_96879 := by exact prefixLift 96879
  have htrace : WordTrace (prefixWord ++ tailWord_96879) baseStart_96879 baseEnd_96879 := by
    simpa [prefixWord, tailWord_96879, baseEnd_96879] using wordTrace_append hprefix tailTrace_96879
  have hstable : (prefixWord ++ tailWord_96879).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96879).length < 2 ^ (prefixWord ++ tailWord_96879).sum := by decide
  have hdescent : baseEnd_96879 < baseStart_96879 := by decide
  rcases family_descends (prefixWord ++ tailWord_96879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96896 : List Nat := [2, 1, 1, 2, 1, 6, 2, 4]
def baseStart_96896 : Nat := 118140960795 + 96896 * 2 ^ 59
def prefixEnd_96896 : Nat := 4983230072969 + 3 ^ 40 * 96896 * 2
def baseEnd_96896 : Nat := 29483983110019631202601

theorem tailTrace_96896 : CollatzResearch.WordTrace tailWord_96896 prefixEnd_96896 29483983110019631202601 := by
  unfold tailWord_96896
  simp only [CollatzResearch.WordTrace]
  refine ⟨1767043728484907682207271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2356058304646543576276361 1767043728484907682207271)
  ·
    refine ⟨2650565592727361523310907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1767043728484907682207271 2650565592727361523310907)
    ·
      refine ⟨3975848389091042284966361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2650565592727361523310907 3975848389091042284966361)
      ·
        refine ⟨2981886291818281713724771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3975848389091042284966361 2981886291818281713724771)
        ·
          refine ⟨4472829437727422570587157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2981886291818281713724771 4472829437727422570587157)
          ·
            refine ⟨209663879893472932996273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 4472829437727422570587157 209663879893472932996273)
            ·
              refine ⟨157247909920104699747205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 209663879893472932996273 157247909920104699747205)
              ·
                refine ⟨29483983110019631202601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 157247909920104699747205 29483983110019631202601)
                ·
                  rfl

theorem cell19_96896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 2, 4].length) (baseStart_96896 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_96896 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_96896 prefixEnd_96896 := by exact prefixLift 96896
  have htrace : WordTrace (prefixWord ++ tailWord_96896) baseStart_96896 baseEnd_96896 := by
    simpa [prefixWord, tailWord_96896, baseEnd_96896] using wordTrace_append hprefix tailTrace_96896
  have hstable : (prefixWord ++ tailWord_96896).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96896).length < 2 ^ (prefixWord ++ tailWord_96896).sum := by decide
  have hdescent : baseEnd_96896 < baseStart_96896 := by decide
  rcases family_descends (prefixWord ++ tailWord_96896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96951 : List Nat := [1, 1, 3, 1, 6, 2, 1, 4]
def baseStart_96951 : Nat := 118140960795 + 96951 * 2 ^ 59
def prefixEnd_96951 : Nat := 4983230072969 + 3 ^ 40 * 96951 * 2
def baseEnd_96951 : Nat := 29500718775795799980229

theorem tailTrace_96951 : CollatzResearch.WordTrace tailWord_96951 prefixEnd_96951 29500718775795799980229 := by
  unfold tailWord_96951
  simp only [CollatzResearch.WordTrace]
  refine ⟨3536093471770559757666707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2357395647847039838444471 3536093471770559757666707)
  ·
    refine ⟨5304140207655839636500061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3536093471770559757666707 5304140207655839636500061)
    ·
      refine ⟨1989052577870939863687523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5304140207655839636500061 1989052577870939863687523)
      ·
        refine ⟨2983578866806409795531285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1989052577870939863687523 2983578866806409795531285)
        ·
          refine ⟨139855259381550459165529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 2983578866806409795531285 139855259381550459165529)
          ·
            refine ⟨104891444536162844374147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 139855259381550459165529 104891444536162844374147)
            ·
              refine ⟨157337166804244266561221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104891444536162844374147 157337166804244266561221)
              ·
                refine ⟨29500718775795799980229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 157337166804244266561221 29500718775795799980229)
                ·
                  rfl

theorem cell19_96951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 1, 4].length) (baseStart_96951 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_96951 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_96951 prefixEnd_96951 := by exact prefixLift 96951
  have htrace : WordTrace (prefixWord ++ tailWord_96951) baseStart_96951 baseEnd_96951 := by
    simpa [prefixWord, tailWord_96951, baseEnd_96951] using wordTrace_append hprefix tailTrace_96951
  have hstable : (prefixWord ++ tailWord_96951).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96951).length < 2 ^ (prefixWord ++ tailWord_96951).sum := by decide
  have hdescent : baseEnd_96951 < baseStart_96951 := by decide
  rcases family_descends (prefixWord ++ tailWord_96951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96970 : List Nat := [3, 1, 2, 1, 4, 2, 3, 3]
def baseStart_96970 : Nat := 118140960795 + 96970 * 2 ^ 59
def prefixEnd_96970 : Nat := 4983230072969 + 3 ^ 40 * 96970 * 2
def baseEnd_96970 : Nat := 29506500187609385557955

theorem tailTrace_96970 : CollatzResearch.WordTrace tailWord_96970 prefixEnd_96970 29506500187609385557955 := by
  unfold tailWord_96970
  simp only [CollatzResearch.WordTrace]
  refine ⟨884196614675431500652091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2357857639134484001738909 884196614675431500652091)
  ·
    refine ⟨1326294922013147250978137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 884196614675431500652091 1326294922013147250978137)
    ·
      refine ⟨994721191509860438233603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1326294922013147250978137 994721191509860438233603)
      ·
        refine ⟨1492081787264790657350405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 994721191509860438233603 1492081787264790657350405)
        ·
          refine ⟨279765335112148248253201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1492081787264790657350405 279765335112148248253201)
          ·
            refine ⟨209824001334111186189901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 279765335112148248253201 209824001334111186189901)
            ·
              refine ⟨78684000500291694821213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 209824001334111186189901 78684000500291694821213)
              ·
                refine ⟨29506500187609385557955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78684000500291694821213 29506500187609385557955)
                ·
                  rfl

theorem cell19_96970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 3, 3].length) (baseStart_96970 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_96970 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_96970 prefixEnd_96970 := by exact prefixLift 96970
  have htrace : WordTrace (prefixWord ++ tailWord_96970) baseStart_96970 baseEnd_96970 := by
    simpa [prefixWord, tailWord_96970, baseEnd_96970] using wordTrace_append hprefix tailTrace_96970
  have hstable : (prefixWord ++ tailWord_96970).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96970).length < 2 ^ (prefixWord ++ tailWord_96970).sum := by decide
  have hdescent : baseEnd_96970 < baseStart_96970 := by decide
  rcases family_descends (prefixWord ++ tailWord_96970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97105 : List Nat := [1, 2, 2, 1, 7, 6]
def baseStart_97105 : Nat := 118140960795 + 97105 * 2 ^ 59
def prefixEnd_97105 : Nat := 4983230072969 + 3 ^ 40 * 97105 * 2
def baseEnd_97105 : Nat := 3283064293329896950843

theorem tailTrace_97105 : CollatzResearch.WordTrace tailWord_97105 prefixEnd_97105 3283064293329896950843 := by
  unfold tailWord_97105
  simp only [CollatzResearch.WordTrace]
  refine ⟨3541710313212644058772769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2361140208808429372515179 3541710313212644058772769)
  ·
    refine ⟨2656282734909483044079577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3541710313212644058772769 2656282734909483044079577)
    ·
      refine ⟨1992212051182112283059683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2656282734909483044079577 1992212051182112283059683)
      ·
        refine ⟨2988318076773168424589525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1992212051182112283059683 2988318076773168424589525)
        ·
          refine ⟨70038704924371134951317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 2988318076773168424589525 70038704924371134951317)
          ·
            refine ⟨3283064293329896950843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 70038704924371134951317 3283064293329896950843)
            ·
              rfl

theorem cell19_97105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 6].length) (baseStart_97105 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_97105 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_97105 prefixEnd_97105 := by exact prefixLift 97105
  have htrace : WordTrace (prefixWord ++ tailWord_97105) baseStart_97105 baseEnd_97105 := by
    simpa [prefixWord, tailWord_97105, baseEnd_97105] using wordTrace_append hprefix tailTrace_97105
  have hstable : (prefixWord ++ tailWord_97105).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97105).length < 2 ^ (prefixWord ++ tailWord_97105).sum := by decide
  have hdescent : baseEnd_97105 < baseStart_97105 := by decide
  rcases family_descends (prefixWord ++ tailWord_97105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97124 : List Nat := [2, 3, 1, 1, 4, 1, 3, 4]
def baseStart_97124 : Nat := 118140960795 + 97124 * 2 ^ 59
def prefixEnd_97124 : Nat := 4983230072969 + 3 ^ 40 * 97124 * 2
def baseEnd_97124 : Nat := 29553360051782658135313

theorem tailTrace_97124 : CollatzResearch.WordTrace tailWord_97124 prefixEnd_97124 29553360051782658135313 := by
  unfold tailWord_97124
  simp only [CollatzResearch.WordTrace]
  refine ⟨1771201650071905151857213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2361602200095873535809617 1771201650071905151857213)
  ·
    refine ⟨664200618776964431946455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1771201650071905151857213 664200618776964431946455)
    ·
      refine ⟨996300928165446647919683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 664200618776964431946455 996300928165446647919683)
      ·
        refine ⟨1494451392248169971879525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 996300928165446647919683 1494451392248169971879525)
        ·
          refine ⟨280209636046531869727411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1494451392248169971879525 280209636046531869727411)
          ·
            refine ⟨420314454069797804591117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 280209636046531869727411 420314454069797804591117)
            ·
              refine ⟨157617920276174176721669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 420314454069797804591117 157617920276174176721669)
              ·
                refine ⟨29553360051782658135313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 157617920276174176721669 29553360051782658135313)
                ·
                  rfl

theorem cell19_97124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 3, 4].length) (baseStart_97124 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_97124 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_97124 prefixEnd_97124 := by exact prefixLift 97124
  have htrace : WordTrace (prefixWord ++ tailWord_97124) baseStart_97124 baseEnd_97124 := by
    simpa [prefixWord, tailWord_97124, baseEnd_97124] using wordTrace_append hprefix tailTrace_97124
  have hstable : (prefixWord ++ tailWord_97124).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97124).length < 2 ^ (prefixWord ++ tailWord_97124).sum := by decide
  have hdescent : baseEnd_97124 < baseStart_97124 := by decide
  rcases family_descends (prefixWord ++ tailWord_97124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97141 : List Nat := [1, 3, 4, 1, 1, 3, 3, 3]
def baseStart_97141 : Nat := 118140960795 + 97141 * 2 ^ 59
def prefixEnd_97141 : Nat := 4983230072969 + 3 ^ 40 * 97141 * 2
def baseEnd_97141 : Nat := 29558532893931655757489

theorem tailTrace_97141 : CollatzResearch.WordTrace tailWord_97141 prefixEnd_97141 29558532893931655757489 := by
  unfold tailWord_97141
  simp only [CollatzResearch.WordTrace]
  refine ⟨3543023341082222207083277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2362015560721481471388851 3543023341082222207083277)
  ·
    refine ⟨1328633752905833327656229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3543023341082222207083277 1328633752905833327656229)
    ·
      refine ⟨249118828669843748935543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1328633752905833327656229 249118828669843748935543)
      ·
        refine ⟨373678243004765623403315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249118828669843748935543 373678243004765623403315)
        ·
          refine ⟨560517364507148435104973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 373678243004765623403315 560517364507148435104973)
          ·
            refine ⟨210194011690180663164365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 560517364507148435104973 210194011690180663164365)
            ·
              refine ⟨78822754383817748686637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 210194011690180663164365 78822754383817748686637)
              ·
                refine ⟨29558532893931655757489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78822754383817748686637 29558532893931655757489)
                ·
                  rfl

theorem cell19_97141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 3, 3].length) (baseStart_97141 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_97141 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_97141 prefixEnd_97141 := by exact prefixLift 97141
  have htrace : WordTrace (prefixWord ++ tailWord_97141) baseStart_97141 baseEnd_97141 := by
    simpa [prefixWord, tailWord_97141, baseEnd_97141] using wordTrace_append hprefix tailTrace_97141
  have hstable : (prefixWord ++ tailWord_97141).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97141).length < 2 ^ (prefixWord ++ tailWord_97141).sum := by decide
  have hdescent : baseEnd_97141 < baseStart_97141 := by decide
  rcases family_descends (prefixWord ++ tailWord_97141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97162 : List Nat := [3, 1, 2, 4, 1, 2, 6]
def baseStart_97162 : Nat := 118140960795 + 97162 * 2 ^ 59
def prefixEnd_97162 : Nat := 4983230072969 + 3 ^ 40 * 97162 * 2
def baseEnd_97162 : Nat := 9854974291803276430255

theorem tailTrace_97162 : CollatzResearch.WordTrace tailWord_97162 prefixEnd_97162 9854974291803276430255 := by
  unfold tailWord_97162
  simp only [CollatzResearch.WordTrace]
  refine ⟨885947318501535698399435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2362526182670761862398493 885947318501535698399435)
  ·
    refine ⟨1328920977752303547599153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 885947318501535698399435 1328920977752303547599153)
    ·
      refine ⟨996690733314227660699365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1328920977752303547599153 996690733314227660699365)
      ·
        refine ⟨186879512496417686381131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 996690733314227660699365 186879512496417686381131)
        ·
          refine ⟨280319268744626529571697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186879512496417686381131 280319268744626529571697)
          ·
            refine ⟨210239451558469897178773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 280319268744626529571697 210239451558469897178773)
            ·
              refine ⟨9854974291803276430255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 210239451558469897178773 9854974291803276430255)
              ·
                rfl

theorem cell19_97162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 6].length) (baseStart_97162 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_97162 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_97162 prefixEnd_97162 := by exact prefixLift 97162
  have htrace : WordTrace (prefixWord ++ tailWord_97162) baseStart_97162 baseEnd_97162 := by
    simpa [prefixWord, tailWord_97162, baseEnd_97162] using wordTrace_append hprefix tailTrace_97162
  have hstable : (prefixWord ++ tailWord_97162).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97162).length < 2 ^ (prefixWord ++ tailWord_97162).sum := by decide
  have hdescent : baseEnd_97162 < baseStart_97162 := by decide
  rcases family_descends (prefixWord ++ tailWord_97162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97240 : List Nat := [2, 1, 2, 2, 2, 3, 1, 6]
def baseStart_97240 : Nat := 118140960795 + 97240 * 2 ^ 59
def prefixEnd_97240 : Nat := 4983230072969 + 3 ^ 40 * 97240 * 2
def baseEnd_97240 : Nat := 29588657092328759557219

theorem tailTrace_97240 : CollatzResearch.WordTrace tailWord_97240 prefixEnd_97240 29588657092328759557219 := by
  unfold tailWord_97240
  simp only [CollatzResearch.WordTrace]
  refine ⟨1773317083861781057468587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2364422778482374743291449 1773317083861781057468587)
  ·
    refine ⟨2659975625792671586202881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1773317083861781057468587 2659975625792671586202881)
    ·
      refine ⟨1994981719344503689652161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2659975625792671586202881 1994981719344503689652161)
      ·
        refine ⟨1496236289508377767239121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1994981719344503689652161 1496236289508377767239121)
        ·
          refine ⟨1122177217131283325429341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1496236289508377767239121 1122177217131283325429341)
          ·
            refine ⟨420816456424231247036003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1122177217131283325429341 420816456424231247036003)
            ·
              refine ⟨631224684636346870554005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 420816456424231247036003 631224684636346870554005)
              ·
                refine ⟨29588657092328759557219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 631224684636346870554005 29588657092328759557219)
                ·
                  rfl

theorem cell19_97240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 6].length) (baseStart_97240 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_97240 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_97240 prefixEnd_97240 := by exact prefixLift 97240
  have htrace : WordTrace (prefixWord ++ tailWord_97240) baseStart_97240 baseEnd_97240 := by
    simpa [prefixWord, tailWord_97240, baseEnd_97240] using wordTrace_append hprefix tailTrace_97240
  have hstable : (prefixWord ++ tailWord_97240).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97240).length < 2 ^ (prefixWord ++ tailWord_97240).sum := by decide
  have hdescent : baseEnd_97240 < baseStart_97240 := by decide
  rcases family_descends (prefixWord ++ tailWord_97240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97390 : List Nat := [4, 1, 2, 2, 1, 4, 5]
def baseStart_97390 : Nat := 118140960795 + 97390 * 2 ^ 59
def prefixEnd_97390 : Nat := 4983230072969 + 3 ^ 40 * 97390 * 2
def baseEnd_97390 : Nat := 9878099939057618741159

theorem tailTrace_97390 : CollatzResearch.WordTrace tailWord_97390 prefixEnd_97390 9878099939057618741159 := by
  unfold tailWord_97390
  simp only [CollatzResearch.WordTrace]
  refine ⟨444013139647517216612203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2368070078120091821931749 444013139647517216612203)
  ·
    refine ⟨666019709471275824918305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 444013139647517216612203 666019709471275824918305)
    ·
      refine ⟨499514782103456868688729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 666019709471275824918305 499514782103456868688729)
      ·
        refine ⟨374636086577592651516547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 499514782103456868688729 374636086577592651516547)
        ·
          refine ⟨561954129866388977274821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 374636086577592651516547 561954129866388977274821)
          ·
            refine ⟨105366399349947933239029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 561954129866388977274821 105366399349947933239029)
            ·
              refine ⟨9878099939057618741159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 105366399349947933239029 9878099939057618741159)
              ·
                rfl

theorem cell19_97390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 5].length) (baseStart_97390 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_97390 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_97390 prefixEnd_97390 := by exact prefixLift 97390
  have htrace : WordTrace (prefixWord ++ tailWord_97390) baseStart_97390 baseEnd_97390 := by
    simpa [prefixWord, tailWord_97390, baseEnd_97390] using wordTrace_append hprefix tailTrace_97390
  have hstable : (prefixWord ++ tailWord_97390).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97390).length < 2 ^ (prefixWord ++ tailWord_97390).sum := by decide
  have hdescent : baseEnd_97390 < baseStart_97390 := by decide
  rcases family_descends (prefixWord ++ tailWord_97390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97409 : List Nat := [1, 2, 4, 2, 2, 2, 2, 4]
def baseStart_97409 : Nat := 118140960795 + 97409 * 2 ^ 59
def prefixEnd_97409 : Nat := 4983230072969 + 3 ^ 40 * 97409 * 2
def baseEnd_97409 : Nat := 29640081228986441801203

theorem tailTrace_97409 : CollatzResearch.WordTrace tailWord_97409 prefixEnd_97409 29640081228986441801203 := by
  unfold tailWord_97409
  simp only [CollatzResearch.WordTrace]
  refine ⟨3552798104111303977839281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2368532069407535985226187 3552798104111303977839281)
  ·
    refine ⟨2664598578083477983379461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3552798104111303977839281 2664598578083477983379461)
    ·
      refine ⟨499612233390652121883649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2664598578083477983379461 499612233390652121883649)
      ·
        refine ⟨374709175042989091412737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 499612233390652121883649 374709175042989091412737)
        ·
          refine ⟨281031881282241818559553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 374709175042989091412737 281031881282241818559553)
          ·
            refine ⟨210773910961681363919665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 281031881282241818559553 210773910961681363919665)
            ·
              refine ⟨158080433221261022939749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 210773910961681363919665 158080433221261022939749)
              ·
                refine ⟨29640081228986441801203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 158080433221261022939749 29640081228986441801203)
                ·
                  rfl

theorem cell19_97409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 2, 4].length) (baseStart_97409 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_97409 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_97409 prefixEnd_97409 := by exact prefixLift 97409
  have htrace : WordTrace (prefixWord ++ tailWord_97409) baseStart_97409 baseEnd_97409 := by
    simpa [prefixWord, tailWord_97409, baseEnd_97409] using wordTrace_append hprefix tailTrace_97409
  have hstable : (prefixWord ++ tailWord_97409).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97409).length < 2 ^ (prefixWord ++ tailWord_97409).sum := by decide
  have hdescent : baseEnd_97409 < baseStart_97409 := by decide
  rcases family_descends (prefixWord ++ tailWord_97409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97411 : List Nat := [1, 1, 1, 3, 3, 2, 4, 4]
def baseStart_97411 : Nat := 118140960795 + 97411 * 2 ^ 59
def prefixEnd_97411 : Nat := 4983230072969 + 3 ^ 40 * 97411 * 2
def baseEnd_97411 : Nat := 29640689798651029756753

theorem tailTrace_97411 : CollatzResearch.WordTrace tailWord_97411 prefixEnd_97411 29640689798651029756753 := by
  unfold tailWord_97411
  simp only [CollatzResearch.WordTrace]
  refine ⟨3552871050104058319412087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2368580700069372212941391 3552871050104058319412087)
  ·
    refine ⟨5329306575156087479118131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3552871050104058319412087 5329306575156087479118131)
    ·
      refine ⟨7993959862734131218677197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5329306575156087479118131 7993959862734131218677197)
      ·
        refine ⟨2997734948525299207003949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7993959862734131218677197 2997734948525299207003949)
        ·
          refine ⟨1124150605696987202626481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2997734948525299207003949 1124150605696987202626481)
          ·
            refine ⟨843112954272740401969861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1124150605696987202626481 843112954272740401969861)
            ·
              refine ⟨158083678926138825369349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 843112954272740401969861 158083678926138825369349)
              ·
                refine ⟨29640689798651029756753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 158083678926138825369349 29640689798651029756753)
                ·
                  rfl

theorem cell19_97411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 4, 4].length) (baseStart_97411 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_97411 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_97411 prefixEnd_97411 := by exact prefixLift 97411
  have htrace : WordTrace (prefixWord ++ tailWord_97411) baseStart_97411 baseEnd_97411 := by
    simpa [prefixWord, tailWord_97411, baseEnd_97411] using wordTrace_append hprefix tailTrace_97411
  have hstable : (prefixWord ++ tailWord_97411).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97411).length < 2 ^ (prefixWord ++ tailWord_97411).sum := by decide
  have hdescent : baseEnd_97411 < baseStart_97411 := by decide
  rcases family_descends (prefixWord ++ tailWord_97411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97538 : List Nat := [3, 4, 1, 1, 3, 2, 2, 3]
def baseStart_97538 : Nat := 118140960795 + 97538 * 2 ^ 59
def prefixEnd_97538 : Nat := 4983230072969 + 3 ^ 40 * 97538 * 2
def baseEnd_97538 : Nat := 29679333972352364934185

theorem tailTrace_97538 : CollatzResearch.WordTrace tailWord_97538 prefixEnd_97538 29679333972352364934185 := by
  unfold tailWord_97538
  simp only [CollatzResearch.WordTrace]
  refine ⟨889375780160989752321317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2371668747095972672856845 889375780160989752321317)
  ·
    refine ⟨166757958780185578560247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 889375780160989752321317 166757958780185578560247)
    ·
      refine ⟨250136938170278367840371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166757958780185578560247 250136938170278367840371)
      ·
        refine ⟨375205407255417551760557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250136938170278367840371 375205407255417551760557)
        ·
          refine ⟨140702027720781581910209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 375205407255417551760557 140702027720781581910209)
          ·
            refine ⟨105526520790586186432657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140702027720781581910209 105526520790586186432657)
            ·
              refine ⟨79144890592939639824493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105526520790586186432657 79144890592939639824493)
              ·
                refine ⟨29679333972352364934185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79144890592939639824493 29679333972352364934185)
                ·
                  rfl

theorem cell19_97538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 2, 3].length) (baseStart_97538 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_97538 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_97538 prefixEnd_97538 := by exact prefixLift 97538
  have htrace : WordTrace (prefixWord ++ tailWord_97538) baseStart_97538 baseEnd_97538 := by
    simpa [prefixWord, tailWord_97538, baseEnd_97538] using wordTrace_append hprefix tailTrace_97538
  have hstable : (prefixWord ++ tailWord_97538).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97538).length < 2 ^ (prefixWord ++ tailWord_97538).sum := by decide
  have hdescent : baseEnd_97538 < baseStart_97538 := by decide
  rcases family_descends (prefixWord ++ tailWord_97538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97540 : List Nat := [2, 3, 2, 2, 2, 3, 2, 3]
def baseStart_97540 : Nat := 118140960795 + 97540 * 2 ^ 59
def prefixEnd_97540 : Nat := 4983230072969 + 3 ^ 40 * 97540 * 2
def baseEnd_97540 : Nat := 29679942542016952889735

theorem tailTrace_97540 : CollatzResearch.WordTrace tailWord_97540 prefixEnd_97540 29679942542016952889735 := by
  unfold tailWord_97540
  simp only [CollatzResearch.WordTrace]
  refine ⟨1778788033318356675429037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2371717377757808900572049 1778788033318356675429037)
  ·
    refine ⟨667045512494383753285889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1778788033318356675429037 667045512494383753285889)
    ·
      refine ⟨500284134370787814964417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 667045512494383753285889 500284134370787814964417)
      ·
        refine ⟨375213100778090861223313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 500284134370787814964417 375213100778090861223313)
        ·
          refine ⟨281409825583568145917485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 375213100778090861223313 281409825583568145917485)
          ·
            refine ⟨105528684593838054719057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 281409825583568145917485 105528684593838054719057)
            ·
              refine ⟨79146513445378541039293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105528684593838054719057 79146513445378541039293)
              ·
                refine ⟨29679942542016952889735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79146513445378541039293 29679942542016952889735)
                ·
                  rfl

theorem cell19_97540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 2, 3].length) (baseStart_97540 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_97540 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_97540 prefixEnd_97540 := by exact prefixLift 97540
  have htrace : WordTrace (prefixWord ++ tailWord_97540) baseStart_97540 baseEnd_97540 := by
    simpa [prefixWord, tailWord_97540, baseEnd_97540] using wordTrace_append hprefix tailTrace_97540
  have hstable : (prefixWord ++ tailWord_97540).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97540).length < 2 ^ (prefixWord ++ tailWord_97540).sum := by decide
  have hdescent : baseEnd_97540 < baseStart_97540 := by decide
  rcases family_descends (prefixWord ++ tailWord_97540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97641 : List Nat := [1, 2, 1, 1, 1, 3, 2, 8]
def baseStart_97641 : Nat := 118140960795 + 97641 * 2 ^ 59
def prefixEnd_97641 : Nat := 4983230072969 + 3 ^ 40 * 97641 * 2
def baseEnd_97641 : Nat := 29710675310078644645015

theorem tailTrace_97641 : CollatzResearch.WordTrace tailWord_97641 prefixEnd_97641 29710675310078644645015 := by
  unfold tailWord_97641
  simp only [CollatzResearch.WordTrace]
  refine ⟨3561259839270807600284777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2374173226180538400189851 3561259839270807600284777)
  ·
    refine ⟨2670944879453105700213583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3561259839270807600284777 2670944879453105700213583)
    ·
      refine ⟨4006417319179658550320375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2670944879453105700213583 4006417319179658550320375)
      ·
        refine ⟨6009625978769487825480563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4006417319179658550320375 6009625978769487825480563)
        ·
          refine ⟨9014438968154231738220845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6009625978769487825480563 9014438968154231738220845)
          ·
            refine ⟨3380414613057836901832817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9014438968154231738220845 3380414613057836901832817)
            ·
              refine ⟨2535310959793377676374613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3380414613057836901832817 2535310959793377676374613)
              ·
                refine ⟨29710675310078644645015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2535310959793377676374613 29710675310078644645015)
                ·
                  rfl

theorem cell19_97641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 8].length) (baseStart_97641 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_97641 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_97641 prefixEnd_97641 := by exact prefixLift 97641
  have htrace : WordTrace (prefixWord ++ tailWord_97641) baseStart_97641 baseEnd_97641 := by
    simpa [prefixWord, tailWord_97641, baseEnd_97641] using wordTrace_append hprefix tailTrace_97641
  have hstable : (prefixWord ++ tailWord_97641).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97641).length < 2 ^ (prefixWord ++ tailWord_97641).sum := by decide
  have hdescent : baseEnd_97641 < baseStart_97641 := by decide
  rcases family_descends (prefixWord ++ tailWord_97641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97732 : List Nat := [2, 3, 3, 2, 1, 3, 5]
def baseStart_97732 : Nat := 118140960795 + 97732 * 2 ^ 59
def prefixEnd_97732 : Nat := 4983230072969 + 3 ^ 40 * 97732 * 2
def baseEnd_97732 : Nat := 9912788409939132207515

theorem tailTrace_97732 : CollatzResearch.WordTrace tailWord_97732 prefixEnd_97732 9912788409939132207515 := by
  unfold tailWord_97732
  simp only [CollatzResearch.WordTrace]
  refine ⟨1782289440970565070923725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2376385921294086761231633 1782289440970565070923725)
  ·
    refine ⟨668358540363961901596397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1782289440970565070923725 668358540363961901596397)
    ·
      refine ⟨250634452636485713098649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 668358540363961901596397 250634452636485713098649)
      ·
        refine ⟨187975839477364284823987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 250634452636485713098649 187975839477364284823987)
        ·
          refine ⟨281963759216046427235981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187975839477364284823987 281963759216046427235981)
          ·
            refine ⟨105736409706017410213493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 281963759216046427235981 105736409706017410213493)
            ·
              refine ⟨9912788409939132207515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 105736409706017410213493 9912788409939132207515)
              ·
                rfl

theorem cell19_97732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 5].length) (baseStart_97732 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_97732 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_97732 prefixEnd_97732 := by exact prefixLift 97732
  have htrace : WordTrace (prefixWord ++ tailWord_97732) baseStart_97732 baseEnd_97732 := by
    simpa [prefixWord, tailWord_97732, baseEnd_97732] using wordTrace_append hprefix tailTrace_97732
  have hstable : (prefixWord ++ tailWord_97732).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97732).length < 2 ^ (prefixWord ++ tailWord_97732).sum := by decide
  have hdescent : baseEnd_97732 < baseStart_97732 := by decide
  rcases family_descends (prefixWord ++ tailWord_97732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97753 : List Nat := [1, 2, 1, 2, 4, 3, 2, 4]
def baseStart_97753 : Nat := 118140960795 + 97753 * 2 ^ 59
def prefixEnd_97753 : Nat := 4983230072969 + 3 ^ 40 * 97753 * 2
def baseEnd_97753 : Nat := 29744755211295570155821

theorem tailTrace_97753 : CollatzResearch.WordTrace tailWord_97753 prefixEnd_97753 29744755211295570155821 := by
  unfold tailWord_97753
  simp only [CollatzResearch.WordTrace]
  refine ⟨3565344814865050728361913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2376896543243367152241275 3565344814865050728361913)
  ·
    refine ⟨2674008611148788046271435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3565344814865050728361913 2674008611148788046271435)
    ·
      refine ⟨4011012916723182069407153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2674008611148788046271435 4011012916723182069407153)
      ·
        refine ⟨3008259687542386552055365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4011012916723182069407153 3008259687542386552055365)
        ·
          refine ⟨564048691414197478510381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3008259687542386552055365 564048691414197478510381)
          ·
            refine ⟨211518259280324054441393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 564048691414197478510381 211518259280324054441393)
            ·
              refine ⟨158638694460243040831045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 211518259280324054441393 158638694460243040831045)
              ·
                refine ⟨29744755211295570155821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 158638694460243040831045 29744755211295570155821)
                ·
                  rfl

theorem cell19_97753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 2, 4].length) (baseStart_97753 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_97753 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_97753 prefixEnd_97753 := by exact prefixLift 97753
  have htrace : WordTrace (prefixWord ++ tailWord_97753) baseStart_97753 baseEnd_97753 := by
    simpa [prefixWord, tailWord_97753, baseEnd_97753] using wordTrace_append hprefix tailTrace_97753
  have hstable : (prefixWord ++ tailWord_97753).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97753).length < 2 ^ (prefixWord ++ tailWord_97753).sum := by decide
  have hdescent : baseEnd_97753 < baseStart_97753 := by decide
  rcases family_descends (prefixWord ++ tailWord_97753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97793 : List Nat := [1, 2, 4, 1, 11]
def baseStart_97793 : Nat := 118140960795 + 97793 * 2 ^ 59
def prefixEnd_97793 : Nat := 4983230072969 + 3 ^ 40 * 97793 * 2
def baseEnd_97793 : Nat := 1102108392762493676549

theorem tailTrace_97793 : CollatzResearch.WordTrace tailWord_97793 prefixEnd_97793 1102108392762493676549 := by
  unfold tailWord_97793
  simp only [CollatzResearch.WordTrace]
  refine ⟨3566803734720137559818033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2377869156480091706545355 3566803734720137559818033)
  ·
    refine ⟨2675102801040103169863525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3566803734720137559818033 2675102801040103169863525)
    ·
      refine ⟨501581775195019344349411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2675102801040103169863525 501581775195019344349411)
      ·
        refine ⟨752372662792529016524117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 501581775195019344349411 752372662792529016524117)
        ·
          refine ⟨1102108392762493676549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 752372662792529016524117 1102108392762493676549)
          ·
            rfl

theorem cell19_97793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 11].length) (baseStart_97793 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_97793 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_97793 prefixEnd_97793 := by exact prefixLift 97793
  have htrace : WordTrace (prefixWord ++ tailWord_97793) baseStart_97793 baseEnd_97793 := by
    simpa [prefixWord, tailWord_97793, baseEnd_97793] using wordTrace_append hprefix tailTrace_97793
  have hstable : (prefixWord ++ tailWord_97793).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97793).length < 2 ^ (prefixWord ++ tailWord_97793).sum := by decide
  have hdescent : baseEnd_97793 < baseStart_97793 := by decide
  rcases family_descends (prefixWord ++ tailWord_97793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97806 : List Nat := [4, 1, 1, 2, 5, 1, 1, 4]
def baseStart_97806 : Nat := 118140960795 + 97806 * 2 ^ 59
def prefixEnd_97806 : Nat := 4983230072969 + 3 ^ 40 * 97806 * 2
def baseEnd_97806 : Nat := 29760882307407150977899

theorem tailTrace_97806 : CollatzResearch.WordTrace tailWord_97806 prefixEnd_97806 29760882307407150977899 := by
  unfold tailWord_97806
  simp only [CollatzResearch.WordTrace]
  refine ⟨445909735459130097505159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2378185255782027186694181 445909735459130097505159)
  ·
    refine ⟨668864603188695146257739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 445909735459130097505159 668864603188695146257739)
    ·
      refine ⟨1003296904783042719386609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 668864603188695146257739 1003296904783042719386609)
      ·
        refine ⟨752472678587282039539957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1003296904783042719386609 752472678587282039539957)
        ·
          refine ⟨70544313617557691206871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 752472678587282039539957 70544313617557691206871)
          ·
            refine ⟨105816470426336536810307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70544313617557691206871 105816470426336536810307)
            ·
              refine ⟨158724705639504805215461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105816470426336536810307 158724705639504805215461)
              ·
                refine ⟨29760882307407150977899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 158724705639504805215461 29760882307407150977899)
                ·
                  rfl

theorem cell19_97806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 1, 4].length) (baseStart_97806 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_97806 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_97806 prefixEnd_97806 := by exact prefixLift 97806
  have htrace : WordTrace (prefixWord ++ tailWord_97806) baseStart_97806 baseEnd_97806 := by
    simpa [prefixWord, tailWord_97806, baseEnd_97806] using wordTrace_append hprefix tailTrace_97806
  have hstable : (prefixWord ++ tailWord_97806).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97806).length < 2 ^ (prefixWord ++ tailWord_97806).sum := by decide
  have hdescent : baseEnd_97806 < baseStart_97806 := by decide
  rcases family_descends (prefixWord ++ tailWord_97806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97827 : List Nat := [1, 1, 1, 4, 5, 1, 3, 3]
def baseStart_97827 : Nat := 118140960795 + 97827 * 2 ^ 59
def prefixEnd_97827 : Nat := 4983230072969 + 3 ^ 40 * 97827 * 2
def baseEnd_97827 : Nat := 29767272288885324511175

theorem tailTrace_97827 : CollatzResearch.WordTrace tailWord_97827 prefixEnd_97827 29767272288885324511175 := by
  unfold tailWord_97827
  simp only [CollatzResearch.WordTrace]
  refine ⟨3568043816596961366555735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2378695877731307577703823 3568043816596961366555735)
  ·
    refine ⟨5352065724895442049833603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3568043816596961366555735 5352065724895442049833603)
    ·
      refine ⟨8028098587343163074750405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5352065724895442049833603 8028098587343163074750405)
      ·
        refine ⟨1505268485126843076515701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8028098587343163074750405 1505268485126843076515701)
        ·
          refine ⟨141118920480641538423347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1505268485126843076515701 141118920480641538423347)
          ·
            refine ⟨211678380720962307635021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141118920480641538423347 211678380720962307635021)
            ·
              refine ⟨79379392770360865363133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 211678380720962307635021 79379392770360865363133)
              ·
                refine ⟨29767272288885324511175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79379392770360865363133 29767272288885324511175)
                ·
                  rfl

theorem cell19_97827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 3, 3].length) (baseStart_97827 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_97827 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_97827 prefixEnd_97827 := by exact prefixLift 97827
  have htrace : WordTrace (prefixWord ++ tailWord_97827) baseStart_97827 baseEnd_97827 := by
    simpa [prefixWord, tailWord_97827, baseEnd_97827] using wordTrace_append hprefix tailTrace_97827
  have hstable : (prefixWord ++ tailWord_97827).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97827).length < 2 ^ (prefixWord ++ tailWord_97827).sum := by decide
  have hdescent : baseEnd_97827 < baseStart_97827 := by decide
  rcases family_descends (prefixWord ++ tailWord_97827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97846 : List Nat := [5, 1, 2, 1, 3, 1, 6]
def baseStart_97846 : Nat := 118140960795 + 97846 * 2 ^ 59
def prefixEnd_97846 : Nat := 4983230072969 + 3 ^ 40 * 97846 * 2
def baseEnd_97846 : Nat := 9924351233566303362967

theorem tailTrace_97846 : CollatzResearch.WordTrace tailWord_97846 prefixEnd_97846 9924351233566303362967 := by
  unfold tailWord_97846
  simp only [CollatzResearch.WordTrace]
  refine ⟨223046050220507975718587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2379157869018751740998261 223046050220507975718587)
  ·
    refine ⟨334569075330761963577881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223046050220507975718587 334569075330761963577881)
    ·
      refine ⟨250926806498071472683411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 334569075330761963577881 250926806498071472683411)
      ·
        refine ⟨376390209747107209025117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250926806498071472683411 376390209747107209025117)
        ·
          refine ⟨141146328655165203384419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 376390209747107209025117 141146328655165203384419)
          ·
            refine ⟨211719492982747805076629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141146328655165203384419 211719492982747805076629)
            ·
              refine ⟨9924351233566303362967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 211719492982747805076629 9924351233566303362967)
              ·
                rfl

theorem cell19_97846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 6].length) (baseStart_97846 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_97846 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_97846 prefixEnd_97846 := by exact prefixLift 97846
  have htrace : WordTrace (prefixWord ++ tailWord_97846) baseStart_97846 baseEnd_97846 := by
    simpa [prefixWord, tailWord_97846, baseEnd_97846] using wordTrace_append hprefix tailTrace_97846
  have hstable : (prefixWord ++ tailWord_97846).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97846).length < 2 ^ (prefixWord ++ tailWord_97846).sum := by decide
  have hdescent : baseEnd_97846 < baseStart_97846 := by decide
  rcases family_descends (prefixWord ++ tailWord_97846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97850 : List Nat := [3, 1, 1, 1, 3, 2, 8]
def baseStart_97850 : Nat := 118140960795 + 97850 * 2 ^ 59
def prefixEnd_97850 : Nat := 4983230072969 + 3 ^ 40 * 97850 * 2
def baseEnd_97850 : Nat := 9924756946676028666667

theorem tailTrace_97850 : CollatzResearch.WordTrace tailWord_97850 prefixEnd_97850 9924756946676028666667 := by
  unfold tailWord_97850
  simp only [CollatzResearch.WordTrace]
  refine ⟨892220673878409073660751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2379255130342424196428669 892220673878409073660751)
  ·
    refine ⟨1338331010817613610491127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 892220673878409073660751 1338331010817613610491127)
    ·
      refine ⟨2007496516226420415736691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1338331010817613610491127 2007496516226420415736691)
      ·
        refine ⟨3011244774339630623605037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2007496516226420415736691 3011244774339630623605037)
        ·
          refine ⟨1129216790377361483851889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3011244774339630623605037 1129216790377361483851889)
          ·
            refine ⟨846912592783021112888917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1129216790377361483851889 846912592783021112888917)
            ·
              refine ⟨9924756946676028666667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 846912592783021112888917 9924756946676028666667)
              ·
                rfl

theorem cell19_97850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 8].length) (baseStart_97850 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_97850 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_97850 prefixEnd_97850 := by exact prefixLift 97850
  have htrace : WordTrace (prefixWord ++ tailWord_97850) baseStart_97850 baseEnd_97850 := by
    simpa [prefixWord, tailWord_97850, baseEnd_97850] using wordTrace_append hprefix tailTrace_97850
  have hstable : (prefixWord ++ tailWord_97850).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97850).length < 2 ^ (prefixWord ++ tailWord_97850).sum := by decide
  have hdescent : baseEnd_97850 < baseStart_97850 := by decide
  rcases family_descends (prefixWord ++ tailWord_97850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97878 : List Nat := [5, 2, 2, 2, 1, 2, 2, 3]
def baseStart_97878 : Nat := 118140960795 + 97878 * 2 ^ 59
def prefixEnd_97878 : Nat := 4983230072969 + 3 ^ 40 * 97878 * 2
def baseEnd_97878 : Nat := 29782790815332317377703

theorem tailTrace_97878 : CollatzResearch.WordTrace tailWord_97878 prefixEnd_97878 29782790815332317377703 := by
  unfold tailWord_97878
  simp only [CollatzResearch.WordTrace]
  refine ⟨223118996213262317291393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2379935959608131384441525 223118996213262317291393)
  ·
    refine ⟨167339247159946737968545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223118996213262317291393 167339247159946737968545)
    ·
      refine ⟨125504435369960053476409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167339247159946737968545 125504435369960053476409)
      ·
        refine ⟨94128326527470040107307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125504435369960053476409 94128326527470040107307)
        ·
          refine ⟨141192489791205060160961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94128326527470040107307 141192489791205060160961)
          ·
            refine ⟨105894367343403795120721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 141192489791205060160961 105894367343403795120721)
            ·
              refine ⟨79420775507552846340541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105894367343403795120721 79420775507552846340541)
              ·
                refine ⟨29782790815332317377703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79420775507552846340541 29782790815332317377703)
                ·
                  rfl

theorem cell19_97878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 2, 3].length) (baseStart_97878 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_97878 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_97878 prefixEnd_97878 := by exact prefixLift 97878
  have htrace : WordTrace (prefixWord ++ tailWord_97878) baseStart_97878 baseEnd_97878 := by
    simpa [prefixWord, tailWord_97878, baseEnd_97878] using wordTrace_append hprefix tailTrace_97878
  have hstable : (prefixWord ++ tailWord_97878).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97878).length < 2 ^ (prefixWord ++ tailWord_97878).sum := by decide
  have hdescent : baseEnd_97878 < baseStart_97878 := by decide
  rcases family_descends (prefixWord ++ tailWord_97878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97884 : List Nat := [2, 2, 4, 1, 2, 1, 4, 3]
def baseStart_97884 : Nat := 118140960795 + 97884 * 2 ^ 59
def prefixEnd_97884 : Nat := 4983230072969 + 3 ^ 40 * 97884 * 2
def baseEnd_97884 : Nat := 29784616524326081244353

theorem tailTrace_97884 : CollatzResearch.WordTrace tailWord_97884 prefixEnd_97884 29784616524326081244353 := by
  unfold tailWord_97884
  simp only [CollatzResearch.WordTrace]
  refine ⟨1785061388695230050690353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2380081851593640067587137 1785061388695230050690353)
  ·
    refine ⟨1338796041521422538017765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1785061388695230050690353 1338796041521422538017765)
    ·
      refine ⟨251024257785266725878331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1338796041521422538017765 251024257785266725878331)
      ·
        refine ⟨376536386677900088817497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 251024257785266725878331 376536386677900088817497)
        ·
          refine ⟨282402290008425066613123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 376536386677900088817497 282402290008425066613123)
          ·
            refine ⟨423603435012637599919685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 282402290008425066613123 423603435012637599919685)
            ·
              refine ⟨79425644064869549984941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 423603435012637599919685 79425644064869549984941)
              ·
                refine ⟨29784616524326081244353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79425644064869549984941 29784616524326081244353)
                ·
                  rfl

theorem cell19_97884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 4, 3].length) (baseStart_97884 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_97884 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_97884 prefixEnd_97884 := by exact prefixLift 97884
  have htrace : WordTrace (prefixWord ++ tailWord_97884) baseStart_97884 baseEnd_97884 := by
    simpa [prefixWord, tailWord_97884, baseEnd_97884] using wordTrace_append hprefix tailTrace_97884
  have hstable : (prefixWord ++ tailWord_97884).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97884).length < 2 ^ (prefixWord ++ tailWord_97884).sum := by decide
  have hdescent : baseEnd_97884 < baseStart_97884 := by decide
  rcases family_descends (prefixWord ++ tailWord_97884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97960 : List Nat := [2, 1, 7, 1, 8]
def baseStart_97960 : Nat := 118140960795 + 97960 * 2 ^ 59
def prefixEnd_97960 : Nat := 4983230072969 + 3 ^ 40 * 97960 * 2
def baseEnd_97960 : Nat := 1103990450799274946491

theorem tailTrace_97960 : CollatzResearch.WordTrace tailWord_97960 prefixEnd_97960 1103990450799274946491 := by
  unfold tailWord_97960
  simp only [CollatzResearch.WordTrace]
  refine ⟨1786447362557562540573667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2381929816743416720764889 1786447362557562540573667)
  ·
    refine ⟨2679671043836343810860501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1786447362557562540573667 2679671043836343810860501)
    ·
      refine ⟨62804790089914308067043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 2679671043836343810860501 62804790089914308067043)
      ·
        refine ⟨94207185134871462100565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62804790089914308067043 94207185134871462100565)
        ·
          refine ⟨1103990450799274946491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 94207185134871462100565 1103990450799274946491)
          ·
            rfl

theorem cell19_97960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 8].length) (baseStart_97960 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_97960 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_97960 prefixEnd_97960 := by exact prefixLift 97960
  have htrace : WordTrace (prefixWord ++ tailWord_97960) baseStart_97960 baseEnd_97960 := by
    simpa [prefixWord, tailWord_97960, baseEnd_97960] using wordTrace_append hprefix tailTrace_97960
  have hstable : (prefixWord ++ tailWord_97960).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97960).length < 2 ^ (prefixWord ++ tailWord_97960).sum := by decide
  have hdescent : baseEnd_97960 < baseStart_97960 := by decide
  rcases family_descends (prefixWord ++ tailWord_97960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98019 : List Nat := [1, 1, 1, 7, 2, 1, 6]
def baseStart_98019 : Nat := 118140960795 + 98019 * 2 ^ 59
def prefixEnd_98019 : Nat := 4983230072969 + 3 ^ 40 * 98019 * 2
def baseEnd_98019 : Nat := 9941898325561922747995

theorem tailTrace_98019 : CollatzResearch.WordTrace tailWord_98019 prefixEnd_98019 9941898325561922747995 := by
  unfold tailWord_98019
  simp only [CollatzResearch.WordTrace]
  refine ⟨3575046631901378157545111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2383364421267585438363407 3575046631901378157545111)
  ·
    refine ⟨5362569947852067236317667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3575046631901378157545111 5362569947852067236317667)
    ·
      refine ⟨8043854921778100854476501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5362569947852067236317667 8043854921778100854476501)
      ·
        refine ⟨188527849729174238776793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 8043854921778100854476501 188527849729174238776793)
        ·
          refine ⟨141395887296880679082595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 188527849729174238776793 141395887296880679082595)
          ·
            refine ⟨212093830945321018623893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141395887296880679082595 212093830945321018623893)
            ·
              refine ⟨9941898325561922747995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 212093830945321018623893 9941898325561922747995)
              ·
                rfl

theorem cell19_98019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 6].length) (baseStart_98019 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_98019 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_98019 prefixEnd_98019 := by exact prefixLift 98019
  have htrace : WordTrace (prefixWord ++ tailWord_98019) baseStart_98019 baseEnd_98019 := by
    simpa [prefixWord, tailWord_98019, baseEnd_98019] using wordTrace_append hprefix tailTrace_98019
  have hstable : (prefixWord ++ tailWord_98019).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98019).length < 2 ^ (prefixWord ++ tailWord_98019).sum := by decide
  have hdescent : baseEnd_98019 < baseStart_98019 := by decide
  rcases family_descends (prefixWord ++ tailWord_98019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98021 : List Nat := [1, 3, 1, 4, 1, 1, 8]
def baseStart_98021 : Nat := 118140960795 + 98021 * 2 ^ 59
def prefixEnd_98021 : Nat := 4983230072969 + 3 ^ 40 * 98021 * 2
def baseEnd_98021 : Nat := 9942101182116785399845

theorem tailTrace_98021 : CollatzResearch.WordTrace tailWord_98021 prefixEnd_98021 9942101182116785399845 := by
  unfold tailWord_98021
  simp only [CollatzResearch.WordTrace]
  refine ⟨3575119577894132499117917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2383413051929421666078611 3575119577894132499117917)
  ·
    refine ⟨1340669841710299687169219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3575119577894132499117917 1340669841710299687169219)
    ·
      refine ⟨2011004762565449530753829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1340669841710299687169219 2011004762565449530753829)
      ·
        refine ⟨377063392981021787016343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2011004762565449530753829 377063392981021787016343)
        ·
          refine ⟨565595089471532680524515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 377063392981021787016343 565595089471532680524515)
          ·
            refine ⟨848392634207299020786773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 565595089471532680524515 848392634207299020786773)
            ·
              refine ⟨9942101182116785399845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 848392634207299020786773 9942101182116785399845)
              ·
                rfl

theorem cell19_98021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 8].length) (baseStart_98021 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_98021 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_98021 prefixEnd_98021 := by exact prefixLift 98021
  have htrace : WordTrace (prefixWord ++ tailWord_98021) baseStart_98021 baseEnd_98021 := by
    simpa [prefixWord, tailWord_98021, baseEnd_98021] using wordTrace_append hprefix tailTrace_98021
  have hstable : (prefixWord ++ tailWord_98021).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98021).length < 2 ^ (prefixWord ++ tailWord_98021).sum := by decide
  have hdescent : baseEnd_98021 < baseStart_98021 := by decide
  rcases family_descends (prefixWord ++ tailWord_98021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98097 : List Nat := [1, 2, 2, 3, 2, 2, 1, 6]
def baseStart_98097 : Nat := 118140960795 + 98097 * 2 ^ 59
def prefixEnd_98097 : Nat := 4983230072969 + 3 ^ 40 * 98097 * 2
def baseEnd_98097 : Nat := 29849429193604698510439

theorem tailTrace_98097 : CollatzResearch.WordTrace tailWord_98097 prefixEnd_98097 29849429193604698510439 := by
  unfold tailWord_98097
  simp only [CollatzResearch.WordTrace]
  refine ⟨3577891525618797478884545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2385261017079198319256363 3577891525618797478884545)
  ·
    refine ⟨2683418644214098109163409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3577891525618797478884545 2683418644214098109163409)
    ·
      refine ⟨2012563983160573581872557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2683418644214098109163409 2012563983160573581872557)
      ·
        refine ⟨754711493685215093202209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2012563983160573581872557 754711493685215093202209)
        ·
          refine ⟨566033620263911319901657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 754711493685215093202209 566033620263911319901657)
          ·
            refine ⟨424525215197933489926243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 566033620263911319901657 424525215197933489926243)
            ·
              refine ⟨636787822796900234889365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 424525215197933489926243 636787822796900234889365)
              ·
                refine ⟨29849429193604698510439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 636787822796900234889365 29849429193604698510439)
                ·
                  rfl

theorem cell19_98097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 6].length) (baseStart_98097 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_98097 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_98097 prefixEnd_98097 := by exact prefixLift 98097
  have htrace : WordTrace (prefixWord ++ tailWord_98097) baseStart_98097 baseEnd_98097 := by
    simpa [prefixWord, tailWord_98097, baseEnd_98097] using wordTrace_append hprefix tailTrace_98097
  have hstable : (prefixWord ++ tailWord_98097).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98097).length < 2 ^ (prefixWord ++ tailWord_98097).sum := by decide
  have hdescent : baseEnd_98097 < baseStart_98097 := by decide
  rcases family_descends (prefixWord ++ tailWord_98097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98135 : List Nat := [1, 1, 3, 2, 5, 7]
def baseStart_98135 : Nat := 118140960795 + 98135 * 2 ^ 59
def prefixEnd_98135 : Nat := 4983230072969 + 3 ^ 40 * 98135 * 2
def baseEnd_98135 : Nat := 3317888001914652185099

theorem tailTrace_98135 : CollatzResearch.WordTrace tailWord_98135 prefixEnd_98135 3317888001914652185099 := by
  unfold tailWord_98135
  simp only [CollatzResearch.WordTrace]
  refine ⟨3579277499481129968767859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2386184999654086645845239 3579277499481129968767859)
  ·
    refine ⟨5368916249221694953151789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3579277499481129968767859 5368916249221694953151789)
    ·
      refine ⟨2013343593458135607431921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5368916249221694953151789 2013343593458135607431921)
      ·
        refine ⟨1510007695093601705573941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2013343593458135607431921 1510007695093601705573941)
        ·
          refine ⟨141563221415025159897557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1510007695093601705573941 141563221415025159897557)
          ·
            refine ⟨3317888001914652185099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 141563221415025159897557 3317888001914652185099)
            ·
              rfl

theorem cell19_98135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 7].length) (baseStart_98135 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_98135 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_98135 prefixEnd_98135 := by exact prefixLift 98135
  have htrace : WordTrace (prefixWord ++ tailWord_98135) baseStart_98135 baseEnd_98135 := by
    simpa [prefixWord, tailWord_98135, baseEnd_98135] using wordTrace_append hprefix tailTrace_98135
  have hstable : (prefixWord ++ tailWord_98135).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98135).length < 2 ^ (prefixWord ++ tailWord_98135).sum := by decide
  have hdescent : baseEnd_98135 < baseStart_98135 := by decide
  rcases family_descends (prefixWord ++ tailWord_98135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98266 : List Nat := [3, 1, 1, 2, 5, 1, 2, 4]
def baseStart_98266 : Nat := 118140960795 + 98266 * 2 ^ 59
def prefixEnd_98266 : Nat := 4983230072969 + 3 ^ 40 * 98266 * 2
def baseEnd_98266 : Nat := 29900853330262380754423

theorem tailTrace_98266 : CollatzResearch.WordTrace tailWord_98266 prefixEnd_98266 29900853330262380754423 := by
  unfold tailWord_98266
  simp only [CollatzResearch.WordTrace]
  refine ⟨896013865501634835446663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2389370308004359561191101 896013865501634835446663)
  ·
    refine ⟨1344020798252452253169995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 896013865501634835446663 1344020798252452253169995)
    ·
      refine ⟨2016031197378678379754993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1344020798252452253169995 2016031197378678379754993)
      ·
        refine ⟨1512023398034008784816245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2016031197378678379754993 1512023398034008784816245)
        ·
          refine ⟨141752193565688323576523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1512023398034008784816245 141752193565688323576523)
          ·
            refine ⟨212628290348532485364785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141752193565688323576523 212628290348532485364785)
            ·
              refine ⟨159471217761399364023589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 212628290348532485364785 159471217761399364023589)
              ·
                refine ⟨29900853330262380754423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 159471217761399364023589 29900853330262380754423)
                ·
                  rfl

theorem cell19_98266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 2, 4].length) (baseStart_98266 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_98266 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_98266 prefixEnd_98266 := by exact prefixLift 98266
  have htrace : WordTrace (prefixWord ++ tailWord_98266) baseStart_98266 baseEnd_98266 := by
    simpa [prefixWord, tailWord_98266, baseEnd_98266] using wordTrace_append hprefix tailTrace_98266
  have hstable : (prefixWord ++ tailWord_98266).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98266).length < 2 ^ (prefixWord ++ tailWord_98266).sum := by decide
  have hdescent : baseEnd_98266 < baseStart_98266 := by decide
  rcases family_descends (prefixWord ++ tailWord_98266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98306 : List Nat := [3, 4, 1, 11]
def baseStart_98306 : Nat := 118140960795 + 98306 * 2 ^ 59
def prefixEnd_98306 : Nat := 4983230072969 + 3 ^ 40 * 98306 * 2
def baseEnd_98306 : Nat := 369296601525359751425

theorem tailTrace_98306 : CollatzResearch.WordTrace tailWord_98306 prefixEnd_98306 369296601525359751425 := by
  unfold tailWord_98306
  simp only [CollatzResearch.WordTrace]
  refine ⟨896378595465406543310693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2390342921241084115495181 896378595465406543310693)
  ·
    refine ⟨168070986649763726870755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 896378595465406543310693 168070986649763726870755)
    ·
      refine ⟨252106479974645590306133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168070986649763726870755 252106479974645590306133)
      ·
        refine ⟨369296601525359751425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 11 252106479974645590306133 369296601525359751425)
        ·
          rfl

theorem cell19_98306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 11].length) (baseStart_98306 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_98306 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_98306 prefixEnd_98306 := by exact prefixLift 98306
  have htrace : WordTrace (prefixWord ++ tailWord_98306) baseStart_98306 baseEnd_98306 := by
    simpa [prefixWord, tailWord_98306, baseEnd_98306] using wordTrace_append hprefix tailTrace_98306
  have hstable : (prefixWord ++ tailWord_98306).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98306).length < 2 ^ (prefixWord ++ tailWord_98306).sum := by decide
  have hdescent : baseEnd_98306 < baseStart_98306 := by decide
  rcases family_descends (prefixWord ++ tailWord_98306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98317 : List Nat := [1, 7, 1, 2, 1, 2, 1, 4]
def baseStart_98317 : Nat := 118140960795 + 98317 * 2 ^ 59
def prefixEnd_98317 : Nat := 4983230072969 + 3 ^ 40 * 98317 * 2
def baseEnd_98317 : Nat := 29916371856709373620951

theorem tailTrace_98317 : CollatzResearch.WordTrace tailWord_98317 prefixEnd_98317 29916371856709373620951 := by
  unfold tailWord_98317
  simp only [CollatzResearch.WordTrace]
  refine ⟨3585915584821775051893205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2390610389881183367928803 3585915584821775051893205)
  ·
    refine ⟨84044896519260352778747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 3585915584821775051893205 84044896519260352778747)
    ·
      refine ⟨126067344778890529168121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84044896519260352778747 126067344778890529168121)
      ·
        refine ⟨94550508584167896876091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126067344778890529168121 94550508584167896876091)
        ·
          refine ⟨141825762876251845314137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94550508584167896876091 141825762876251845314137)
          ·
            refine ⟨106369322157188883985603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 141825762876251845314137 106369322157188883985603)
            ·
              refine ⟨159553983235783325978405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106369322157188883985603 159553983235783325978405)
              ·
                refine ⟨29916371856709373620951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 159553983235783325978405 29916371856709373620951)
                ·
                  rfl

theorem cell19_98317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 1, 4].length) (baseStart_98317 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_98317 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_98317 prefixEnd_98317 := by exact prefixLift 98317
  have htrace : WordTrace (prefixWord ++ tailWord_98317) baseStart_98317 baseEnd_98317 := by
    simpa [prefixWord, tailWord_98317, baseEnd_98317] using wordTrace_append hprefix tailTrace_98317
  have hstable : (prefixWord ++ tailWord_98317).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98317).length < 2 ^ (prefixWord ++ tailWord_98317).sum := by decide
  have hdescent : baseEnd_98317 < baseStart_98317 := by decide
  rcases family_descends (prefixWord ++ tailWord_98317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98340 : List Nat := [2, 3, 1, 4, 2, 1, 3, 3]
def baseStart_98340 : Nat := 118140960795 + 98340 * 2 ^ 59
def prefixEnd_98340 : Nat := 4983230072969 + 3 ^ 40 * 98340 * 2
def baseEnd_98340 : Nat := 29923370407852135109777

theorem tailTrace_98340 : CollatzResearch.WordTrace tailWord_98340 prefixEnd_98340 29923370407852135109777 := by
  unfold tailWord_98340
  simp only [CollatzResearch.WordTrace]
  refine ⟨1793377231869224989990237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2391169642492299986653649 1793377231869224989990237)
  ·
    refine ⟨672516461950959371246339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1793377231869224989990237 672516461950959371246339)
    ·
      refine ⟨1008774692926439056869509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 672516461950959371246339 1008774692926439056869509)
      ·
        refine ⟨189145254923707323163033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1008774692926439056869509 189145254923707323163033)
        ·
          refine ⟨141858941192780492372275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 189145254923707323163033 141858941192780492372275)
          ·
            refine ⟨212788411789170738558413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141858941192780492372275 212788411789170738558413)
            ·
              refine ⟨79795654420939026959405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 212788411789170738558413 79795654420939026959405)
              ·
                refine ⟨29923370407852135109777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79795654420939026959405 29923370407852135109777)
                ·
                  rfl

theorem cell19_98340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 3, 3].length) (baseStart_98340 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_98340 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_98340 prefixEnd_98340 := by exact prefixLift 98340
  have htrace : WordTrace (prefixWord ++ tailWord_98340) baseStart_98340 baseEnd_98340 := by
    simpa [prefixWord, tailWord_98340, baseEnd_98340] using wordTrace_append hprefix tailTrace_98340
  have hstable : (prefixWord ++ tailWord_98340).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98340).length < 2 ^ (prefixWord ++ tailWord_98340).sum := by decide
  have hdescent : baseEnd_98340 < baseStart_98340 := by decide
  rcases family_descends (prefixWord ++ tailWord_98340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98397 : List Nat := [1, 4, 4, 1, 1, 1, 4, 3]
def baseStart_98397 : Nat := 118140960795 + 98397 * 2 ^ 59
def prefixEnd_98397 : Nat := 4983230072969 + 3 ^ 40 * 98397 * 2
def baseEnd_98397 : Nat := 29940714643292891842955

theorem tailTrace_98397 : CollatzResearch.WordTrace tailWord_98397 prefixEnd_98397 29940714643292891842955 := by
  unfold tailWord_98397
  simp only [CollatzResearch.WordTrace]
  refine ⟨3588833424531948714805445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2392555616354632476536963 3588833424531948714805445)
  ·
    refine ⟨672906267099740384026021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3588833424531948714805445 672906267099740384026021)
    ·
      refine ⟨126169925081201322004879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 672906267099740384026021 126169925081201322004879)
      ·
        refine ⟨189254887621801983007319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126169925081201322004879 189254887621801983007319)
        ·
          refine ⟨283882331432702974510979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189254887621801983007319 283882331432702974510979)
          ·
            refine ⟨425823497149054461766469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 283882331432702974510979 425823497149054461766469)
            ·
              refine ⟨79841905715447711581213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 425823497149054461766469 79841905715447711581213)
              ·
                refine ⟨29940714643292891842955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79841905715447711581213 29940714643292891842955)
                ·
                  rfl

theorem cell19_98397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 4, 3].length) (baseStart_98397 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_98397 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_98397 prefixEnd_98397 := by exact prefixLift 98397
  have htrace : WordTrace (prefixWord ++ tailWord_98397) baseStart_98397 baseEnd_98397 := by
    simpa [prefixWord, tailWord_98397, baseEnd_98397] using wordTrace_append hprefix tailTrace_98397
  have hstable : (prefixWord ++ tailWord_98397).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98397).length < 2 ^ (prefixWord ++ tailWord_98397).sum := by decide
  have hdescent : baseEnd_98397 < baseStart_98397 := by decide
  rcases family_descends (prefixWord ++ tailWord_98397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98477 : List Nat := [1, 5, 2, 1, 2, 8]
def baseStart_98477 : Nat := 118140960795 + 98477 * 2 ^ 59
def prefixEnd_98477 : Nat := 4983230072969 + 3 ^ 40 * 98477 * 2
def baseEnd_98477 : Nat := 3329450825541823340551

theorem tailTrace_98477 : CollatzResearch.WordTrace tailWord_98477 prefixEnd_98477 3329450825541823340551 := by
  unfold tailWord_98477
  simp only [CollatzResearch.WordTrace]
  refine ⟨3591751264242122377717685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2394500842828081585145123 3591751264242122377717685)
  ·
    refine ⟨336726681022698972911033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3591751264242122377717685 336726681022698972911033)
    ·
      refine ⟨252545010767024229683275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 336726681022698972911033 252545010767024229683275)
      ·
        refine ⟨378817516150536344524913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 252545010767024229683275 378817516150536344524913)
        ·
          refine ⟨284113137112902258393685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 378817516150536344524913 284113137112902258393685)
          ·
            refine ⟨3329450825541823340551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 284113137112902258393685 3329450825541823340551)
            ·
              rfl

theorem cell19_98477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 8].length) (baseStart_98477 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_98477 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_98477 prefixEnd_98477 := by exact prefixLift 98477
  have htrace : WordTrace (prefixWord ++ tailWord_98477) baseStart_98477 baseEnd_98477 := by
    simpa [prefixWord, tailWord_98477, baseEnd_98477] using wordTrace_append hprefix tailTrace_98477
  have hstable : (prefixWord ++ tailWord_98477).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98477).length < 2 ^ (prefixWord ++ tailWord_98477).sum := by decide
  have hdescent : baseEnd_98477 < baseStart_98477 := by decide
  rcases family_descends (prefixWord ++ tailWord_98477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98492 : List Nat := [2, 2, 2, 3, 4, 1, 1, 4]
def baseStart_98492 : Nat := 118140960795 + 98492 * 2 ^ 59
def prefixEnd_98492 : Nat := 4983230072969 + 3 ^ 40 * 98492 * 2
def baseEnd_98492 : Nat := 29969621702360819731585

theorem tailTrace_98492 : CollatzResearch.WordTrace tailWord_98492 prefixEnd_98492 29969621702360819731585 := by
  unfold tailWord_98492
  simp only [CollatzResearch.WordTrace]
  refine ⟨1796149179593889969756865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2394865572791853293009153 1796149179593889969756865)
  ·
    refine ⟨1347111884695417477317649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1796149179593889969756865 1347111884695417477317649)
    ·
      refine ⟨1010333913521563107988237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1347111884695417477317649 1010333913521563107988237)
      ·
        refine ⟨378875217570586165495589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1010333913521563107988237 378875217570586165495589)
        ·
          refine ⟨71039103294484906030423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 378875217570586165495589 71039103294484906030423)
          ·
            refine ⟨106558654941727359045635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71039103294484906030423 106558654941727359045635)
            ·
              refine ⟨159837982412591038568453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106558654941727359045635 159837982412591038568453)
              ·
                refine ⟨29969621702360819731585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 159837982412591038568453 29969621702360819731585)
                ·
                  rfl

theorem cell19_98492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 1, 4].length) (baseStart_98492 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_98492 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_98492 prefixEnd_98492 := by exact prefixLift 98492
  have htrace : WordTrace (prefixWord ++ tailWord_98492) baseStart_98492 baseEnd_98492 := by
    simpa [prefixWord, tailWord_98492, baseEnd_98492] using wordTrace_append hprefix tailTrace_98492
  have hstable : (prefixWord ++ tailWord_98492).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98492).length < 2 ^ (prefixWord ++ tailWord_98492).sum := by decide
  have hdescent : baseEnd_98492 < baseStart_98492 := by decide
  rcases family_descends (prefixWord ++ tailWord_98492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98496 : List Nat := [2, 1, 1, 2, 5, 1, 3, 4]
def baseStart_98496 : Nat := 118140960795 + 98496 * 2 ^ 59
def prefixEnd_98496 : Nat := 4983230072969 + 3 ^ 40 * 98496 * 2
def baseEnd_98496 : Nat := 29970838841689995642685

theorem tailTrace_98496 : CollatzResearch.WordTrace tailWord_98496 prefixEnd_98496 29970838841689995642685 := by
  unfold tailWord_98496
  simp only [CollatzResearch.WordTrace]
  refine ⟨1796222125586644311329671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2394962834115525748439561 1796222125586644311329671)
  ·
    refine ⟨2694333188379966466994507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1796222125586644311329671 2694333188379966466994507)
    ·
      refine ⟨4041499782569949700491761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2694333188379966466994507 4041499782569949700491761)
      ·
        refine ⟨3031124836927462275368821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4041499782569949700491761 3031124836927462275368821)
        ·
          refine ⟨284167953461949588315827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3031124836927462275368821 284167953461949588315827)
          ·
            refine ⟨426251930192924382473741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 284167953461949588315827 426251930192924382473741)
            ·
              refine ⟨159844473822346643427653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 426251930192924382473741 159844473822346643427653)
              ·
                refine ⟨29970838841689995642685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 159844473822346643427653 29970838841689995642685)
                ·
                  rfl

theorem cell19_98496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 3, 4].length) (baseStart_98496 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_98496 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_98496 prefixEnd_98496 := by exact prefixLift 98496
  have htrace : WordTrace (prefixWord ++ tailWord_98496) baseStart_98496 baseEnd_98496 := by
    simpa [prefixWord, tailWord_98496, baseEnd_98496] using wordTrace_append hprefix tailTrace_98496
  have hstable : (prefixWord ++ tailWord_98496).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98496).length < 2 ^ (prefixWord ++ tailWord_98496).sum := by decide
  have hdescent : baseEnd_98496 < baseStart_98496 := by decide
  rcases family_descends (prefixWord ++ tailWord_98496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98589 : List Nat := [1, 4, 2, 3, 2, 2, 5]
def baseStart_98589 : Nat := 118140960795 + 98589 * 2 ^ 59
def prefixEnd_98589 : Nat := 4983230072969 + 3 ^ 40 * 98589 * 2
def baseEnd_98589 : Nat := 9999712443697778525255

theorem tailTrace_98589 : CollatzResearch.WordTrace tailWord_98589 prefixEnd_98589 9999712443697778525255 := by
  unfold tailWord_98589
  simp only [CollatzResearch.WordTrace]
  refine ⟨3595836239836365505794821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2397224159890910337196547 3595836239836365505794821)
  ·
    refine ⟨674219294969318532336529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3595836239836365505794821 674219294969318532336529)
    ·
      refine ⟨505664471226988899252397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 674219294969318532336529 505664471226988899252397)
      ·
        refine ⟨189624176710120837219649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 505664471226988899252397 189624176710120837219649)
        ·
          refine ⟨142218132532590627914737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 189624176710120837219649 142218132532590627914737)
          ·
            refine ⟨106663599399442970936053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142218132532590627914737 106663599399442970936053)
            ·
              refine ⟨9999712443697778525255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 106663599399442970936053 9999712443697778525255)
              ·
                rfl

theorem cell19_98589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 5].length) (baseStart_98589 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_98589 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_98589 prefixEnd_98589 := by exact prefixLift 98589
  have htrace : WordTrace (prefixWord ++ tailWord_98589) baseStart_98589 baseEnd_98589 := by
    simpa [prefixWord, tailWord_98589, baseEnd_98589] using wordTrace_append hprefix tailTrace_98589
  have hstable : (prefixWord ++ tailWord_98589).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98589).length < 2 ^ (prefixWord ++ tailWord_98589).sum := by decide
  have hdescent : baseEnd_98589 < baseStart_98589 := by decide
  rcases family_descends (prefixWord ++ tailWord_98589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98591 : List Nat := [1, 1, 2, 4, 3, 3, 5]
def baseStart_98591 : Nat := 118140960795 + 98591 * 2 ^ 59
def prefixEnd_98591 : Nat := 4983230072969 + 3 ^ 40 * 98591 * 2
def baseEnd_98591 : Nat := 9999915300252641177105

theorem tailTrace_98591 : CollatzResearch.WordTrace tailWord_98591 prefixEnd_98591 9999915300252641177105 := by
  unfold tailWord_98591
  simp only [CollatzResearch.WordTrace]
  refine ⟨3595909185829119847367627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2397272790552746564911751 3595909185829119847367627)
  ·
    refine ⟨5393863778743679771051441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3595909185829119847367627 5393863778743679771051441)
    ·
      refine ⟨4045397834057759828288581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5393863778743679771051441 4045397834057759828288581)
      ·
        refine ⟨758512093885829967804109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4045397834057759828288581 758512093885829967804109)
        ·
          refine ⟨284442035207186237926541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 758512093885829967804109 284442035207186237926541)
          ·
            refine ⟨106665763202694839222453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 284442035207186237926541 106665763202694839222453)
            ·
              refine ⟨9999915300252641177105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 106665763202694839222453 9999915300252641177105)
              ·
                rfl

theorem cell19_98591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 5].length) (baseStart_98591 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_98591 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_98591 prefixEnd_98591 := by exact prefixLift 98591
  have htrace : WordTrace (prefixWord ++ tailWord_98591) baseStart_98591 baseEnd_98591 := by
    simpa [prefixWord, tailWord_98591, baseEnd_98591] using wordTrace_append hprefix tailTrace_98591
  have hstable : (prefixWord ++ tailWord_98591).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98591).length < 2 ^ (prefixWord ++ tailWord_98591).sum := by decide
  have hdescent : baseEnd_98591 < baseStart_98591 := by decide
  rcases family_descends (prefixWord ++ tailWord_98591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98593 : List Nat := [1, 2, 3, 2, 1, 1, 9]
def baseStart_98593 : Nat := 118140960795 + 98593 * 2 ^ 59
def prefixEnd_98593 : Nat := 4983230072969 + 3 ^ 40 * 98593 * 2
def baseEnd_98593 : Nat := 10000118156807503828955

theorem tailTrace_98593 : CollatzResearch.WordTrace tailWord_98593 prefixEnd_98593 10000118156807503828955 := by
  unfold tailWord_98593
  simp only [CollatzResearch.WordTrace]
  refine ⟨3595982131821874188940433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2397321421214582792626955 3595982131821874188940433)
  ·
    refine ⟨2696986598866405641705325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3595982131821874188940433 2696986598866405641705325)
    ·
      refine ⟨1011369974574902115639497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2696986598866405641705325 1011369974574902115639497)
      ·
        refine ⟨758527480931176586729623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1011369974574902115639497 758527480931176586729623)
        ·
          refine ⟨1137791221396764880094435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 758527480931176586729623 1137791221396764880094435)
          ·
            refine ⟨1706686832095147320141653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1137791221396764880094435 1706686832095147320141653)
            ·
              refine ⟨10000118156807503828955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1706686832095147320141653 10000118156807503828955)
              ·
                rfl

theorem cell19_98593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 9].length) (baseStart_98593 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_98593 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_98593 prefixEnd_98593 := by exact prefixLift 98593
  have htrace : WordTrace (prefixWord ++ tailWord_98593) baseStart_98593 baseEnd_98593 := by
    simpa [prefixWord, tailWord_98593, baseEnd_98593] using wordTrace_append hprefix tailTrace_98593
  have hstable : (prefixWord ++ tailWord_98593).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98593).length < 2 ^ (prefixWord ++ tailWord_98593).sum := by decide
  have hdescent : baseEnd_98593 < baseStart_98593 := by decide
  rcases family_descends (prefixWord ++ tailWord_98593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98606 : List Nat := [4, 1, 3, 3, 1, 1, 2, 4]
def baseStart_98606 : Nat := 118140960795 + 98606 * 2 ^ 59
def prefixEnd_98606 : Nat := 4983230072969 + 3 ^ 40 * 98606 * 2
def baseEnd_98606 : Nat := 30004310173242333197941

theorem tailTrace_98606 : CollatzResearch.WordTrace tailWord_98606 prefixEnd_98606 30004310173242333197941 := by
  unfold tailWord_98606
  simp only [CollatzResearch.WordTrace]
  refine ⟨449557035096847176145459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2397637520516518272775781 449557035096847176145459)
  ·
    refine ⟨674335552645270764218189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 449557035096847176145459 674335552645270764218189)
    ·
      refine ⟨252875832241976536581821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 674335552645270764218189 252875832241976536581821)
      ·
        refine ⟨94828437090741201218183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 252875832241976536581821 94828437090741201218183)
        ·
          refine ⟨142242655636111801827275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94828437090741201218183 142242655636111801827275)
          ·
            refine ⟨213363983454167702740913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142242655636111801827275 213363983454167702740913)
            ·
              refine ⟨160022987590625777055685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 213363983454167702740913 160022987590625777055685)
              ·
                refine ⟨30004310173242333197941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 160022987590625777055685 30004310173242333197941)
                ·
                  rfl

theorem cell19_98606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 2, 4].length) (baseStart_98606 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_98606 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_98606 prefixEnd_98606 := by exact prefixLift 98606
  have htrace : WordTrace (prefixWord ++ tailWord_98606) baseStart_98606 baseEnd_98606 := by
    simpa [prefixWord, tailWord_98606, baseEnd_98606] using wordTrace_append hprefix tailTrace_98606
  have hstable : (prefixWord ++ tailWord_98606).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98606).length < 2 ^ (prefixWord ++ tailWord_98606).sum := by decide
  have hdescent : baseEnd_98606 < baseStart_98606 := by decide
  rcases family_descends (prefixWord ++ tailWord_98606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98631 : List Nat := [1, 1, 4, 1, 2, 2, 1, 7]
def baseStart_98631 : Nat := 118140960795 + 98631 * 2 ^ 59
def prefixEnd_98631 : Nat := 4983230072969 + 3 ^ 40 * 98631 * 2
def baseEnd_98631 : Nat := 30011917294049682642317

theorem tailTrace_98631 : CollatzResearch.WordTrace tailWord_98631 prefixEnd_98631 30011917294049682642317 := by
  unfold tailWord_98631
  simp only [CollatzResearch.WordTrace]
  refine ⟨3597368105684206678823747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2398245403789471119215831 3597368105684206678823747)
  ·
    refine ⟨5396052158526310018235621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3597368105684206678823747 5396052158526310018235621)
    ·
      refine ⟨1011759779723683128419179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5396052158526310018235621 1011759779723683128419179)
      ·
        refine ⟨1517639669585524692628769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1011759779723683128419179 1517639669585524692628769)
        ·
          refine ⟨1138229752189143519471577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1517639669585524692628769 1138229752189143519471577)
          ·
            refine ⟨853672314141857639603683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1138229752189143519471577 853672314141857639603683)
            ·
              refine ⟨1280508471212786459405525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 853672314141857639603683 1280508471212786459405525)
              ·
                refine ⟨30011917294049682642317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1280508471212786459405525 30011917294049682642317)
                ·
                  rfl

theorem cell19_98631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 7].length) (baseStart_98631 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_98631 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_98631 prefixEnd_98631 := by exact prefixLift 98631
  have htrace : WordTrace (prefixWord ++ tailWord_98631) baseStart_98631 baseEnd_98631 := by
    simpa [prefixWord, tailWord_98631, baseEnd_98631] using wordTrace_append hprefix tailTrace_98631
  have hstable : (prefixWord ++ tailWord_98631).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98631).length < 2 ^ (prefixWord ++ tailWord_98631).sum := by decide
  have hdescent : baseEnd_98631 < baseStart_98631 := by decide
  rcases family_descends (prefixWord ++ tailWord_98631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98646 : List Nat := [5, 2, 3, 9]
def baseStart_98646 : Nat := 118140960795 + 98646 * 2 ^ 59
def prefixEnd_98646 : Nat := 4983230072969 + 3 ^ 40 * 98646 * 2
def baseEnd_98646 : Nat := 370573846500420892703

theorem tailTrace_98646 : CollatzResearch.WordTrace tailWord_98646 prefixEnd_98646 370573846500420892703 := by
  unfold tailWord_98646
  simp only [CollatzResearch.WordTrace]
  refine ⟨224869700039366515038737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2398610133753242827079861 224869700039366515038737)
  ·
    refine ⟨168652275029524886279053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224869700039366515038737 168652275029524886279053)
    ·
      refine ⟨63244603136071832354645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 168652275029524886279053 63244603136071832354645)
      ·
        refine ⟨370573846500420892703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 9 63244603136071832354645 370573846500420892703)
        ·
          rfl

theorem cell19_98646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 9].length) (baseStart_98646 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_98646 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_98646 prefixEnd_98646 := by exact prefixLift 98646
  have htrace : WordTrace (prefixWord ++ tailWord_98646) baseStart_98646 baseEnd_98646 := by
    simpa [prefixWord, tailWord_98646, baseEnd_98646] using wordTrace_append hprefix tailTrace_98646
  have hstable : (prefixWord ++ tailWord_98646).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98646).length < 2 ^ (prefixWord ++ tailWord_98646).sum := by decide
  have hdescent : baseEnd_98646 < baseStart_98646 := by decide
  rcases family_descends (prefixWord ++ tailWord_98646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98743 : List Nat := [1, 1, 3, 1, 3, 3, 4, 3]
def baseStart_98743 : Nat := 118140960795 + 98743 * 2 ^ 59
def prefixEnd_98743 : Nat := 4983230072969 + 3 ^ 40 * 98743 * 2
def baseEnd_98743 : Nat := 30045997195266608153123

theorem tailTrace_98743 : CollatzResearch.WordTrace tailWord_98743 prefixEnd_98743 30045997195266608153123 := by
  unfold tailWord_98743
  simp only [CollatzResearch.WordTrace]
  refine ⟨3601453081278449806900883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2400968720852299871267255 3601453081278449806900883)
  ·
    refine ⟨5402179621917674710351325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3601453081278449806900883 5402179621917674710351325)
    ·
      refine ⟨2025817358219128016381747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5402179621917674710351325 2025817358219128016381747)
      ·
        refine ⟨3038726037328692024572621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2025817358219128016381747 3038726037328692024572621)
        ·
          refine ⟨1139522263998259509214733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3038726037328692024572621 1139522263998259509214733)
          ·
            refine ⟨427320848999347315955525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1139522263998259509214733 427320848999347315955525)
            ·
              refine ⟨80122659187377621741661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 427320848999347315955525 80122659187377621741661)
              ·
                refine ⟨30045997195266608153123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80122659187377621741661 30045997195266608153123)
                ·
                  rfl

theorem cell19_98743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 4, 3].length) (baseStart_98743 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_98743 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_98743 prefixEnd_98743 := by exact prefixLift 98743
  have htrace : WordTrace (prefixWord ++ tailWord_98743) baseStart_98743 baseEnd_98743 := by
    simpa [prefixWord, tailWord_98743, baseEnd_98743] using wordTrace_append hprefix tailTrace_98743
  have hstable : (prefixWord ++ tailWord_98743).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98743).length < 2 ^ (prefixWord ++ tailWord_98743).sum := by decide
  have hdescent : baseEnd_98743 < baseStart_98743 := by decide
  rcases family_descends (prefixWord ++ tailWord_98743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98781 : List Nat := [1, 4, 3, 1, 1, 1, 4, 4]
def baseStart_98781 : Nat := 118140960795 + 98781 * 2 ^ 59
def prefixEnd_98781 : Nat := 4983230072969 + 3 ^ 40 * 98781 * 2
def baseEnd_98781 : Nat := 30057560018893779308575

theorem tailTrace_98781 : CollatzResearch.WordTrace tailWord_98781 prefixEnd_98781 30057560018893779308575 := by
  unfold tailWord_98781
  simp only [CollatzResearch.WordTrace]
  refine ⟨3602839055140782296784197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2401892703427188197856131 3602839055140782296784197)
  ·
    refine ⟨675532322838896680647037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3602839055140782296784197 675532322838896680647037)
    ·
      refine ⟨253324621064586255242639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 675532322838896680647037 253324621064586255242639)
      ·
        refine ⟨379986931596879382863959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253324621064586255242639 379986931596879382863959)
        ·
          refine ⟨569980397395319074295939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 379986931596879382863959 569980397395319074295939)
          ·
            refine ⟨854970596092978611443909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 569980397395319074295939 854970596092978611443909)
            ·
              refine ⟨160306986767433489645733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 854970596092978611443909 160306986767433489645733)
              ·
                refine ⟨30057560018893779308575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 160306986767433489645733 30057560018893779308575)
                ·
                  rfl

theorem cell19_98781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 4, 4].length) (baseStart_98781 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_98781 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_98781 prefixEnd_98781 := by exact prefixLift 98781
  have htrace : WordTrace (prefixWord ++ tailWord_98781) baseStart_98781 baseEnd_98781 := by
    simpa [prefixWord, tailWord_98781, baseEnd_98781] using wordTrace_append hprefix tailTrace_98781
  have hstable : (prefixWord ++ tailWord_98781).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98781).length < 2 ^ (prefixWord ++ tailWord_98781).sum := by decide
  have hdescent : baseEnd_98781 < baseStart_98781 := by decide
  rcases family_descends (prefixWord ++ tailWord_98781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98783 : List Nat := [1, 1, 2, 3, 3, 2, 1, 6]
def baseStart_98783 : Nat := 118140960795 + 98783 * 2 ^ 59
def prefixEnd_98783 : Nat := 4983230072969 + 3 ^ 40 * 98783 * 2
def baseEnd_98783 : Nat := 30058168588558367264125

theorem tailTrace_98783 : CollatzResearch.WordTrace tailWord_98783 prefixEnd_98783 30058168588558367264125 := by
  unfold tailWord_98783
  simp only [CollatzResearch.WordTrace]
  refine ⟨3602912001133536638357003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2401941334089024425571335 3602912001133536638357003)
  ·
    refine ⟨5404368001700304957535505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3602912001133536638357003 5404368001700304957535505)
    ·
      refine ⟨4053276001275228718151629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5404368001700304957535505 4053276001275228718151629)
      ·
        refine ⟨1519978500478210769306861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4053276001275228718151629 1519978500478210769306861)
        ·
          refine ⟨569991937679329038490073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1519978500478210769306861 569991937679329038490073)
          ·
            refine ⟨427493953259496778867555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 569991937679329038490073 427493953259496778867555)
            ·
              refine ⟨641240929889245168301333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 427493953259496778867555 641240929889245168301333)
              ·
                refine ⟨30058168588558367264125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 641240929889245168301333 30058168588558367264125)
                ·
                  rfl

theorem cell19_98783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 6].length) (baseStart_98783 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_98783 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_98783 prefixEnd_98783 := by exact prefixLift 98783
  have htrace : WordTrace (prefixWord ++ tailWord_98783) baseStart_98783 baseEnd_98783 := by
    simpa [prefixWord, tailWord_98783, baseEnd_98783] using wordTrace_append hprefix tailTrace_98783
  have hstable : (prefixWord ++ tailWord_98783).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98783).length < 2 ^ (prefixWord ++ tailWord_98783).sum := by decide
  have hdescent : baseEnd_98783 < baseStart_98783 := by decide
  rcases family_descends (prefixWord ++ tailWord_98783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98836 : List Nat := [2, 4, 3, 1, 1, 1, 3, 4]
def baseStart_98836 : Nat := 118140960795 + 98836 * 2 ^ 59
def prefixEnd_98836 : Nat := 4983230072969 + 3 ^ 40 * 98836 * 2
def baseEnd_98836 : Nat := 30074295684669948086203

theorem tailTrace_98836 : CollatzResearch.WordTrace tailWord_98836 prefixEnd_98836 30074295684669948086203 := by
  unfold tailWord_98836
  simp only [CollatzResearch.WordTrace]
  refine ⟨1802422534970763345018181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2403230046627684460024241 1802422534970763345018181)
  ·
    refine ⟨337954225307018127190909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1802422534970763345018181 337954225307018127190909)
    ·
      refine ⟨126732834490131797696591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 337954225307018127190909 126732834490131797696591)
      ·
        refine ⟨190099251735197696544887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126732834490131797696591 190099251735197696544887)
        ·
          refine ⟨285148877602796544817331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190099251735197696544887 285148877602796544817331)
          ·
            refine ⟨427723316404194817225997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 285148877602796544817331 427723316404194817225997)
            ·
              refine ⟨160396243651573056459749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 427723316404194817225997 160396243651573056459749)
              ·
                refine ⟨30074295684669948086203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 160396243651573056459749 30074295684669948086203)
                ·
                  rfl

theorem cell19_98836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 3, 4].length) (baseStart_98836 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_98836 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_98836 prefixEnd_98836 := by exact prefixLift 98836
  have htrace : WordTrace (prefixWord ++ tailWord_98836) baseStart_98836 baseEnd_98836 := by
    simpa [prefixWord, tailWord_98836, baseEnd_98836] using wordTrace_append hprefix tailTrace_98836
  have hstable : (prefixWord ++ tailWord_98836).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98836).length < 2 ^ (prefixWord ++ tailWord_98836).sum := by decide
  have hdescent : baseEnd_98836 < baseStart_98836 := by decide
  rcases family_descends (prefixWord ++ tailWord_98836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98916 : List Nat := [2, 3, 1, 1, 2, 2, 3, 5]
def baseStart_98916 : Nat := 118140960795 + 98916 * 2 ^ 59
def prefixEnd_98916 : Nat := 4983230072969 + 3 ^ 40 * 98916 * 2
def baseEnd_98916 : Nat := 30098638471253466308207

theorem tailTrace_98916 : CollatzResearch.WordTrace tailWord_98916 prefixEnd_98916 30098638471253466308207 := by
  unfold tailWord_98916
  simp only [CollatzResearch.WordTrace]
  refine ⟨1803881454825850176474301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2405175273101133568632401 1803881454825850176474301)
  ·
    refine ⟨676455545559693816177863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1803881454825850176474301 676455545559693816177863)
    ·
      refine ⟨1014683318339540724266795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 676455545559693816177863 1014683318339540724266795)
      ·
        refine ⟨1522024977509311086400193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1014683318339540724266795 1522024977509311086400193)
        ·
          refine ⟨1141518733131983314800145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1522024977509311086400193 1141518733131983314800145)
          ·
            refine ⟨856139049848987486100109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1141518733131983314800145 856139049848987486100109)
            ·
              refine ⟨321052143693370307287541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 856139049848987486100109 321052143693370307287541)
              ·
                refine ⟨30098638471253466308207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 321052143693370307287541 30098638471253466308207)
                ·
                  rfl

theorem cell19_98916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 5].length) (baseStart_98916 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_98916 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_98916 prefixEnd_98916 := by exact prefixLift 98916
  have htrace : WordTrace (prefixWord ++ tailWord_98916) baseStart_98916 baseEnd_98916 := by
    simpa [prefixWord, tailWord_98916, baseEnd_98916] using wordTrace_append hprefix tailTrace_98916
  have hstable : (prefixWord ++ tailWord_98916).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98916).length < 2 ^ (prefixWord ++ tailWord_98916).sum := by decide
  have hdescent : baseEnd_98916 < baseStart_98916 := by decide
  rcases family_descends (prefixWord ++ tailWord_98916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98946 : List Nat := [3, 4, 3, 1, 1, 1, 2, 4]
def baseStart_98946 : Nat := 118140960795 + 98946 * 2 ^ 59
def prefixEnd_98946 : Nat := 4983230072969 + 3 ^ 40 * 98946 * 2
def baseEnd_98946 : Nat := 30107767016222285641459

theorem tailTrace_98946 : CollatzResearch.WordTrace tailWord_98946 prefixEnd_98946 30107767016222285641459 := by
  unfold tailWord_98946
  simp only [CollatzResearch.WordTrace]
  refine ⟨902214274885753869135173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2405904733028676984360461 902214274885753869135173)
  ·
    refine ⟨169165176541078850462845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 902214274885753869135173 169165176541078850462845)
    ·
      refine ⟨63436941202904568923567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 169165176541078850462845 63436941202904568923567)
      ·
        refine ⟨95155411804356853385351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63436941202904568923567 95155411804356853385351)
        ·
          refine ⟨142733117706535280078027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95155411804356853385351 142733117706535280078027)
          ·
            refine ⟨214099676559802920117041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142733117706535280078027 214099676559802920117041)
            ·
              refine ⟨160574757419852190087781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 214099676559802920117041 160574757419852190087781)
              ·
                refine ⟨30107767016222285641459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 160574757419852190087781 30107767016222285641459)
                ·
                  rfl

theorem cell19_98946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 2, 4].length) (baseStart_98946 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_98946 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_98946 prefixEnd_98946 := by exact prefixLift 98946
  have htrace : WordTrace (prefixWord ++ tailWord_98946) baseStart_98946 baseEnd_98946 := by
    simpa [prefixWord, tailWord_98946, baseEnd_98946] using wordTrace_append hprefix tailTrace_98946
  have hstable : (prefixWord ++ tailWord_98946).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98946).length < 2 ^ (prefixWord ++ tailWord_98946).sum := by decide
  have hdescent : baseEnd_98946 < baseStart_98946 := by decide
  rcases family_descends (prefixWord ++ tailWord_98946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98973 : List Nat := [1, 4, 2, 1, 1, 1, 4, 5]
def baseStart_98973 : Nat := 118140960795 + 98973 * 2 ^ 59
def prefixEnd_98973 : Nat := 4983230072969 + 3 ^ 40 * 98973 * 2
def baseEnd_98973 : Nat := 30115982706694223041385

theorem tailTrace_98973 : CollatzResearch.WordTrace tailWord_98973 prefixEnd_98973 30115982706694223041385 := by
  unfold tailWord_98973
  simp only [CollatzResearch.WordTrace]
  refine ⟨3609841870445199087773573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2406561246963466058515715 3609841870445199087773573)
  ·
    refine ⟨676845350708474828957545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3609841870445199087773573 676845350708474828957545)
    ·
      refine ⟨507634013031356121718159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 676845350708474828957545 507634013031356121718159)
      ·
        refine ⟨761451019547034182577239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 507634013031356121718159 761451019547034182577239)
        ·
          refine ⟨1142176529320551273865859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 761451019547034182577239 1142176529320551273865859)
          ·
            refine ⟨1713264793980826910798789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1142176529320551273865859 1713264793980826910798789)
            ·
              refine ⟨321237148871405045774773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1713264793980826910798789 321237148871405045774773)
              ·
                refine ⟨30115982706694223041385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 321237148871405045774773 30115982706694223041385)
                ·
                  rfl

theorem cell19_98973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 5].length) (baseStart_98973 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_98973 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_98973 prefixEnd_98973 := by exact prefixLift 98973
  have htrace : WordTrace (prefixWord ++ tailWord_98973) baseStart_98973 baseEnd_98973 := by
    simpa [prefixWord, tailWord_98973, baseEnd_98973] using wordTrace_append hprefix tailTrace_98973
  have hstable : (prefixWord ++ tailWord_98973).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98973).length < 2 ^ (prefixWord ++ tailWord_98973).sum := by decide
  have hdescent : baseEnd_98973 < baseStart_98973 := by decide
  rcases family_descends (prefixWord ++ tailWord_98973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98990 : List Nat := [4, 1, 4, 1, 1, 8]
def baseStart_98990 : Nat := 118140960795 + 98990 * 2 ^ 59
def prefixEnd_98990 : Nat := 4983230072969 + 3 ^ 40 * 98990 * 2
def baseEnd_98990 : Nat := 3346795060982580073729

theorem tailTrace_98990 : CollatzResearch.WordTrace tailWord_98990 prefixEnd_98990 3346795060982580073729 := by
  unfold tailWord_98990
  simp only [CollatzResearch.WordTrace]
  refine ⟨451307738922951373892803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2406974607589073994094949 451307738922951373892803)
  ·
    refine ⟨676961608384427060839205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 451307738922951373892803 676961608384427060839205)
    ·
      refine ⟨126930301572080073907351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 676961608384427060839205 126930301572080073907351)
      ·
        refine ⟨190395452358120110861027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126930301572080073907351 190395452358120110861027)
        ·
          refine ⟨285593178537180166291541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190395452358120110861027 285593178537180166291541)
          ·
            refine ⟨3346795060982580073729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 285593178537180166291541 3346795060982580073729)
            ·
              rfl

theorem cell19_98990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 8].length) (baseStart_98990 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_98990 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_98990 prefixEnd_98990 := by exact prefixLift 98990
  have htrace : WordTrace (prefixWord ++ tailWord_98990) baseStart_98990 baseEnd_98990 := by
    simpa [prefixWord, tailWord_98990, baseEnd_98990] using wordTrace_append hprefix tailTrace_98990
  have hstable : (prefixWord ++ tailWord_98990).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98990).length < 2 ^ (prefixWord ++ tailWord_98990).sum := by decide
  have hdescent : baseEnd_98990 < baseStart_98990 := by decide
  rcases family_descends (prefixWord ++ tailWord_98990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99026 : List Nat := [3, 2, 2, 2, 3, 1, 3, 3]
def baseStart_99026 : Nat := 118140960795 + 99026 * 2 ^ 59
def prefixEnd_99026 : Nat := 4983230072969 + 3 ^ 40 * 99026 * 2
def baseEnd_99026 : Nat := 30132109802805803863463

theorem tailTrace_99026 : CollatzResearch.WordTrace tailWord_99026 prefixEnd_99026 30132109802805803863463 := by
  unfold tailWord_99026
  simp only [CollatzResearch.WordTrace]
  refine ⟨902943734813297284863233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2407849959502126092968621 902943734813297284863233)
  ·
    refine ⟨677207801109972963647425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 902943734813297284863233 677207801109972963647425)
    ·
      refine ⟨507905850832479722735569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 677207801109972963647425 507905850832479722735569)
      ·
        refine ⟨380929388124359792051677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 507905850832479722735569 380929388124359792051677)
        ·
          refine ⟨142848520546634922019379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 380929388124359792051677 142848520546634922019379)
          ·
            refine ⟨214272780819952383029069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142848520546634922019379 214272780819952383029069)
            ·
              refine ⟨80352292807482143635901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 214272780819952383029069 80352292807482143635901)
              ·
                refine ⟨30132109802805803863463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80352292807482143635901 30132109802805803863463)
                ·
                  rfl

theorem cell19_99026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 3, 3].length) (baseStart_99026 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_99026 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_99026 prefixEnd_99026 := by exact prefixLift 99026
  have htrace : WordTrace (prefixWord ++ tailWord_99026) baseStart_99026 baseEnd_99026 := by
    simpa [prefixWord, tailWord_99026, baseEnd_99026] using wordTrace_append hprefix tailTrace_99026
  have hstable : (prefixWord ++ tailWord_99026).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99026).length < 2 ^ (prefixWord ++ tailWord_99026).sum := by decide
  have hdescent : baseEnd_99026 < baseStart_99026 := by decide
  rcases family_descends (prefixWord ++ tailWord_99026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99106 : List Nat := [3, 3, 1, 1, 2, 2, 7]
def baseStart_99106 : Nat := 118140960795 + 99106 * 2 ^ 59
def prefixEnd_99106 : Nat := 4983230072969 + 3 ^ 40 * 99106 * 2
def baseEnd_99106 : Nat := 10052150863129774028489

theorem tailTrace_99106 : CollatzResearch.WordTrace tailWord_99106 prefixEnd_99106 10052150863129774028489 := by
  unfold tailWord_99106
  simp only [CollatzResearch.WordTrace]
  refine ⟨903673194740840700591293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2409795185975575201576781 903673194740840700591293)
  ·
    refine ⟨338877448027815262721735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 903673194740840700591293 338877448027815262721735)
    ·
      refine ⟨508316172041722894082603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 338877448027815262721735 508316172041722894082603)
      ·
        refine ⟨762474258062584341123905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 508316172041722894082603 762474258062584341123905)
        ·
          refine ⟨571855693546938255842929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 762474258062584341123905 571855693546938255842929)
          ·
            refine ⟨428891770160203691882197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 571855693546938255842929 428891770160203691882197)
            ·
              refine ⟨10052150863129774028489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 428891770160203691882197 10052150863129774028489)
              ·
                rfl

theorem cell19_99106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 7].length) (baseStart_99106 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_99106 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_99106 prefixEnd_99106 := by exact prefixLift 99106
  have htrace : WordTrace (prefixWord ++ tailWord_99106) baseStart_99106 baseEnd_99106 := by
    simpa [prefixWord, tailWord_99106, baseEnd_99106] using wordTrace_append hprefix tailTrace_99106
  have hstable : (prefixWord ++ tailWord_99106).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99106).length < 2 ^ (prefixWord ++ tailWord_99106).sum := by decide
  have hdescent : baseEnd_99106 < baseStart_99106 := by decide
  rcases family_descends (prefixWord ++ tailWord_99106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99125 : List Nat := [1, 3, 3, 1, 3, 1, 1, 6]
def baseStart_99125 : Nat := 118140960795 + 99125 * 2 ^ 59
def prefixEnd_99125 : Nat := 4983230072969 + 3 ^ 40 * 99125 * 2
def baseEnd_99125 : Nat := 30162234001202907663193

theorem tailTrace_99125 : CollatzResearch.WordTrace tailWord_99125 prefixEnd_99125 30162234001202907663193 := by
  unfold tailWord_99125
  simp only [CollatzResearch.WordTrace]
  refine ⟨3615385765894529047306829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2410257177263019364871219 3615385765894529047306829)
  ·
    refine ⟨1355769662210448392740061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3615385765894529047306829 1355769662210448392740061)
    ·
      refine ⟨508413623328918147277523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1355769662210448392740061 508413623328918147277523)
      ·
        refine ⟨762620434993377220916285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 508413623328918147277523 762620434993377220916285)
        ·
          refine ⟨285982663122516457843607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 762620434993377220916285 285982663122516457843607)
          ·
            refine ⟨428973994683774686765411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 285982663122516457843607 428973994683774686765411)
            ·
              refine ⟨643460992025662030148117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 428973994683774686765411 643460992025662030148117)
              ·
                refine ⟨30162234001202907663193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 643460992025662030148117 30162234001202907663193)
                ·
                  rfl

theorem cell19_99125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 6].length) (baseStart_99125 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_99125 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_99125 prefixEnd_99125 := by exact prefixLift 99125
  have htrace : WordTrace (prefixWord ++ tailWord_99125) baseStart_99125 baseEnd_99125 := by
    simpa [prefixWord, tailWord_99125, baseEnd_99125] using wordTrace_append hprefix tailTrace_99125
  have hstable : (prefixWord ++ tailWord_99125).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99125).length < 2 ^ (prefixWord ++ tailWord_99125).sum := by decide
  have hdescent : baseEnd_99125 < baseStart_99125 := by decide
  rcases family_descends (prefixWord ++ tailWord_99125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99165 : List Nat := [1, 4, 14]
def baseStart_99165 : Nat := 118140960795 + 99165 * 2 ^ 59
def prefixEnd_99165 : Nat := 4983230072969 + 3 ^ 40 * 99165 * 2
def baseEnd_99165 : Nat := 124174507796274348865

theorem tailTrace_99165 : CollatzResearch.WordTrace tailWord_99165 prefixEnd_99165 124174507796274348865 := by
  unfold tailWord_99165
  simp only [CollatzResearch.WordTrace]
  refine ⟨3616844685749615878762949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2411229790499743919175299 3616844685749615878762949)
  ·
    refine ⟨678158378578052977268053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3616844685749615878762949 678158378578052977268053)
    ·
      refine ⟨124174507796274348865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 14 678158378578052977268053 124174507796274348865)
      ·
        rfl

theorem cell19_99165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 14].length) (baseStart_99165 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_99165 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_99165 prefixEnd_99165 := by exact prefixLift 99165
  have htrace : WordTrace (prefixWord ++ tailWord_99165) baseStart_99165 baseEnd_99165 := by
    simpa [prefixWord, tailWord_99165, baseEnd_99165] using wordTrace_append hprefix tailTrace_99165
  have hstable : (prefixWord ++ tailWord_99165).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99165).length < 2 ^ (prefixWord ++ tailWord_99165).sum := by decide
  have hdescent : baseEnd_99165 < baseStart_99165 := by decide
  rcases family_descends (prefixWord ++ tailWord_99165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99218 : List Nat := [3, 2, 3, 2, 2, 1, 6]
def baseStart_99218 : Nat := 118140960795 + 99218 * 2 ^ 59
def prefixEnd_99218 : Nat := 4983230072969 + 3 ^ 40 * 99218 * 2
def baseEnd_99218 : Nat := 10063510830202082532091

theorem tailTrace_99218 : CollatzResearch.WordTrace tailWord_99218 prefixEnd_99218 10063510830202082532091 := by
  unfold tailWord_99218
  simp only [CollatzResearch.WordTrace]
  refine ⟨904694438639401482610577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2412518503038403953628205 904694438639401482610577)
  ·
    refine ⟨678520828979551111957933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 904694438639401482610577 678520828979551111957933)
    ·
      refine ⟨254445310867331666984225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 678520828979551111957933 254445310867331666984225)
      ·
        refine ⟨190833983150498750238169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 254445310867331666984225 190833983150498750238169)
        ·
          refine ⟨143125487362874062678627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 190833983150498750238169 143125487362874062678627)
          ·
            refine ⟨214688231044311094017941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143125487362874062678627 214688231044311094017941)
            ·
              refine ⟨10063510830202082532091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 214688231044311094017941 10063510830202082532091)
              ·
                rfl

theorem cell19_99218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 6].length) (baseStart_99218 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_99218 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_99218 prefixEnd_99218 := by exact prefixLift 99218
  have htrace : WordTrace (prefixWord ++ tailWord_99218) baseStart_99218 baseEnd_99218 := by
    simpa [prefixWord, tailWord_99218, baseEnd_99218] using wordTrace_append hprefix tailTrace_99218
  have hstable : (prefixWord ++ tailWord_99218).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99218).length < 2 ^ (prefixWord ++ tailWord_99218).sum := by decide
  have hdescent : baseEnd_99218 < baseStart_99218 := by decide
  rcases family_descends (prefixWord ++ tailWord_99218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99220 : List Nat := [2, 4, 2, 1, 1, 1, 8]
def baseStart_99220 : Nat := 118140960795 + 99220 * 2 ^ 59
def prefixEnd_99220 : Nat := 4983230072969 + 3 ^ 40 * 99220 * 2
def baseEnd_99220 : Nat := 10063713686756945183941

theorem tailTrace_99220 : CollatzResearch.WordTrace tailWord_99220 prefixEnd_99220 10063713686756945183941 := by
  unfold tailWord_99220
  simp only [CollatzResearch.WordTrace]
  refine ⟨1809425350275180136007557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2412567133700240181343409 1809425350275180136007557)
  ·
    refine ⟨339267253176596275501417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1809425350275180136007557 339267253176596275501417)
    ·
      refine ⟨254450439882447206626063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 339267253176596275501417 254450439882447206626063)
      ·
        refine ⟨381675659823670809939095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254450439882447206626063 381675659823670809939095)
        ·
          refine ⟨572513489735506214908643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 381675659823670809939095 572513489735506214908643)
          ·
            refine ⟨858770234603259322362965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 572513489735506214908643 858770234603259322362965)
            ·
              refine ⟨10063713686756945183941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 858770234603259322362965 10063713686756945183941)
              ·
                rfl

theorem cell19_99220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 8].length) (baseStart_99220 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_99220 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_99220 prefixEnd_99220 := by exact prefixLift 99220
  have htrace : WordTrace (prefixWord ++ tailWord_99220) baseStart_99220 baseEnd_99220 := by
    simpa [prefixWord, tailWord_99220, baseEnd_99220] using wordTrace_append hprefix tailTrace_99220
  have hstable : (prefixWord ++ tailWord_99220).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99220).length < 2 ^ (prefixWord ++ tailWord_99220).sum := by decide
  have hdescent : baseEnd_99220 < baseStart_99220 := by decide
  rcases family_descends (prefixWord ++ tailWord_99220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99241 : List Nat := [1, 2, 1, 1, 1, 1, 6, 6]
def baseStart_99241 : Nat := 118140960795 + 99241 * 2 ^ 59
def prefixEnd_99241 : Nat := 4983230072969 + 3 ^ 40 * 99241 * 2
def baseEnd_99241 : Nat := 30197531041749009085099

theorem tailTrace_99241 : CollatzResearch.WordTrace tailWord_99241 prefixEnd_99241 30197531041749009085099 := by
  unfold tailWord_99241
  simp only [CollatzResearch.WordTrace]
  refine ⟨3619616633474280858529577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2413077755649520572353051 3619616633474280858529577)
  ·
    refine ⟨2714712475105710643897183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3619616633474280858529577 2714712475105710643897183)
    ·
      refine ⟨4072068712658565965845775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2714712475105710643897183 4072068712658565965845775)
      ·
        refine ⟨6108103068987848948768663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4072068712658565965845775 6108103068987848948768663)
        ·
          refine ⟨9162154603481773423152995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6108103068987848948768663 9162154603481773423152995)
          ·
            refine ⟨13743231905222660134729493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9162154603481773423152995 13743231905222660134729493)
            ·
              refine ⟨644213995557312193815445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 13743231905222660134729493 644213995557312193815445)
              ·
                refine ⟨30197531041749009085099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 644213995557312193815445 30197531041749009085099)
                ·
                  rfl

theorem cell19_99241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 6].length) (baseStart_99241 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_99241 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_99241 prefixEnd_99241 := by exact prefixLift 99241
  have htrace : WordTrace (prefixWord ++ tailWord_99241) baseStart_99241 baseEnd_99241 := by
    simpa [prefixWord, tailWord_99241, baseEnd_99241] using wordTrace_append hprefix tailTrace_99241
  have hstable : (prefixWord ++ tailWord_99241).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99241).length < 2 ^ (prefixWord ++ tailWord_99241).sum := by decide
  have hdescent : baseEnd_99241 < baseStart_99241 := by decide
  rcases family_descends (prefixWord ++ tailWord_99241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99252 : List Nat := [2, 5, 2, 1, 1, 3, 2, 3]
def baseStart_99252 : Nat := 118140960795 + 99252 * 2 ^ 59
def prefixEnd_99252 : Nat := 4983230072969 + 3 ^ 40 * 99252 * 2
def baseEnd_99252 : Nat := 30200878174904242840625

theorem tailTrace_99252 : CollatzResearch.WordTrace tailWord_99252 prefixEnd_99252 30200878174904242840625 := by
  unfold tailWord_99252
  simp only [CollatzResearch.WordTrace]
  refine ⟨1810008918217214868590005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2413345224289619824786673 1810008918217214868590005)
  ·
    refine ⟨169688336082863893930313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1810008918217214868590005 169688336082863893930313)
    ·
      refine ⟨127266252062147920447735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169688336082863893930313 127266252062147920447735)
      ·
        refine ⟨190899378093221880671603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127266252062147920447735 190899378093221880671603)
        ·
          refine ⟨286349067139832821007405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190899378093221880671603 286349067139832821007405)
          ·
            refine ⟨107380900177437307877777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 286349067139832821007405 107380900177437307877777)
            ·
              refine ⟨80535675133077980908333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107380900177437307877777 80535675133077980908333)
              ·
                refine ⟨30200878174904242840625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80535675133077980908333 30200878174904242840625)
                ·
                  rfl

theorem cell19_99252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 2, 3].length) (baseStart_99252 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_99252 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_99252 prefixEnd_99252 := by exact prefixLift 99252
  have htrace : WordTrace (prefixWord ++ tailWord_99252) baseStart_99252 baseEnd_99252 := by
    simpa [prefixWord, tailWord_99252, baseEnd_99252] using wordTrace_append hprefix tailTrace_99252
  have hstable : (prefixWord ++ tailWord_99252).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99252).length < 2 ^ (prefixWord ++ tailWord_99252).sum := by decide
  have hdescent : baseEnd_99252 < baseStart_99252 := by decide
  rcases family_descends (prefixWord ++ tailWord_99252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99256 : List Nat := [2, 1, 2, 1, 2, 6, 2, 3]
def baseStart_99256 : Nat := 118140960795 + 99256 * 2 ^ 59
def prefixEnd_99256 : Nat := 4983230072969 + 3 ^ 40 * 99256 * 2
def baseEnd_99256 : Nat := 30202095314233418751725

theorem tailTrace_99256 : CollatzResearch.WordTrace tailWord_99256 prefixEnd_99256 30202095314233418751725 := by
  unfold tailWord_99256
  simp only [CollatzResearch.WordTrace]
  refine ⟨1810081864209969210162811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2413442485613292280217081 1810081864209969210162811)
  ·
    refine ⟨2715122796314953815244217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1810081864209969210162811 2715122796314953815244217)
    ·
      refine ⟨2036342097236215361433163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2715122796314953815244217 2036342097236215361433163)
      ·
        refine ⟨3054513145854323042149745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2036342097236215361433163 3054513145854323042149745)
        ·
          refine ⟨2290884859390742281612309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3054513145854323042149745 2290884859390742281612309)
          ·
            refine ⟨107385227783941044450577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 2290884859390742281612309 107385227783941044450577)
            ·
              refine ⟨80538920837955783337933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107385227783941044450577 80538920837955783337933)
              ·
                refine ⟨30202095314233418751725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80538920837955783337933 30202095314233418751725)
                ·
                  rfl

theorem cell19_99256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 2, 3].length) (baseStart_99256 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_99256 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_99256 prefixEnd_99256 := by exact prefixLift 99256
  have htrace : WordTrace (prefixWord ++ tailWord_99256) baseStart_99256 baseEnd_99256 := by
    simpa [prefixWord, tailWord_99256, baseEnd_99256] using wordTrace_append hprefix tailTrace_99256
  have hstable : (prefixWord ++ tailWord_99256).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99256).length < 2 ^ (prefixWord ++ tailWord_99256).sum := by decide
  have hdescent : baseEnd_99256 < baseStart_99256 := by decide
  rcases family_descends (prefixWord ++ tailWord_99256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99279 : List Nat := [1, 1, 2, 1, 1, 6, 7]
def baseStart_99279 : Nat := 118140960795 + 99279 * 2 ^ 59
def prefixEnd_99279 : Nat := 4983230072969 + 3 ^ 40 * 99279 * 2
def baseEnd_99279 : Nat := 10069697955125393413517

theorem tailTrace_99279 : CollatzResearch.WordTrace tailWord_99279 prefixEnd_99279 10069697955125393413517 := by
  unfold tailWord_99279
  simp only [CollatzResearch.WordTrace]
  refine ⟨3621002607336613348412891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2414001738224408898941927 3621002607336613348412891)
  ·
    refine ⟨5431503911004920022619337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3621002607336613348412891 5431503911004920022619337)
    ·
      refine ⟨4073627933253690016964503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5431503911004920022619337 4073627933253690016964503)
      ·
        refine ⟨6110441899880535025446755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4073627933253690016964503 6110441899880535025446755)
        ·
          refine ⟨9165662849820802538170133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6110441899880535025446755 9165662849820802538170133)
          ·
            refine ⟨429640446085350118976725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 9165662849820802538170133 429640446085350118976725)
            ·
              refine ⟨10069697955125393413517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 429640446085350118976725 10069697955125393413517)
              ·
                rfl

theorem cell19_99279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 7].length) (baseStart_99279 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_99279 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_99279 prefixEnd_99279 := by exact prefixLift 99279
  have htrace : WordTrace (prefixWord ++ tailWord_99279) baseStart_99279 baseEnd_99279 := by
    simpa [prefixWord, tailWord_99279, baseEnd_99279] using wordTrace_append hprefix tailTrace_99279
  have hstable : (prefixWord ++ tailWord_99279).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99279).length < 2 ^ (prefixWord ++ tailWord_99279).sum := by decide
  have hdescent : baseEnd_99279 < baseStart_99279 := by decide
  rcases family_descends (prefixWord ++ tailWord_99279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99330 : List Nat := [3, 4, 1, 3, 2, 6]
def baseStart_99330 : Nat := 118140960795 + 99330 * 2 ^ 59
def prefixEnd_99330 : Nat := 4983230072969 + 3 ^ 40 * 99330 * 2
def baseEnd_99330 : Nat := 3358290265758130345231

theorem tailTrace_99330 : CollatzResearch.WordTrace tailWord_99330 prefixEnd_99330 3358290265758130345231 := by
  unfold tailWord_99330
  simp only [CollatzResearch.WordTrace]
  refine ⟨905715682537962264629861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2415241820101232705679629 905715682537962264629861)
  ·
    refine ⟨169821690475867924618099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 905715682537962264629861 169821690475867924618099)
    ·
      refine ⟨254732535713801886927149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169821690475867924618099 254732535713801886927149)
      ·
        refine ⟨95524700892675707597681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 254732535713801886927149 95524700892675707597681)
        ·
          refine ⟨71643525669506780698261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95524700892675707597681 71643525669506780698261)
          ·
            refine ⟨3358290265758130345231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 71643525669506780698261 3358290265758130345231)
            ·
              rfl

theorem cell19_99330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 6].length) (baseStart_99330 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_99330 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_99330 prefixEnd_99330 := by exact prefixLift 99330
  have htrace : WordTrace (prefixWord ++ tailWord_99330) baseStart_99330 baseEnd_99330 := by
    simpa [prefixWord, tailWord_99330, baseEnd_99330] using wordTrace_append hprefix tailTrace_99330
  have hstable : (prefixWord ++ tailWord_99330).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99330).length < 2 ^ (prefixWord ++ tailWord_99330).sum := by decide
  have hdescent : baseEnd_99330 < baseStart_99330 := by decide
  rcases family_descends (prefixWord ++ tailWord_99330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99336 : List Nat := [2, 1, 3, 2, 1, 10]
def baseStart_99336 : Nat := 118140960795 + 99336 * 2 ^ 59
def prefixEnd_99336 : Nat := 4983230072969 + 3 ^ 40 * 99336 * 2
def baseEnd_99336 : Nat := 3358493122312992997081

theorem tailTrace_99336 : CollatzResearch.WordTrace tailWord_99336 prefixEnd_99336 3358493122312992997081 := by
  unfold tailWord_99336
  simp only [CollatzResearch.WordTrace]
  refine ⟨1811540784065056041618931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2415387712086741388825241 1811540784065056041618931)
  ·
    refine ⟨2717311176097584062428397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1811540784065056041618931 2717311176097584062428397)
    ·
      refine ⟨1018991691036594023410649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2717311176097584062428397 1018991691036594023410649)
      ·
        refine ⟨764243768277445517557987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1018991691036594023410649 764243768277445517557987)
        ·
          refine ⟨1146365652416168276336981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 764243768277445517557987 1146365652416168276336981)
          ·
            refine ⟨3358493122312992997081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1146365652416168276336981 3358493122312992997081)
            ·
              rfl

theorem cell19_99336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 10].length) (baseStart_99336 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_99336 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_99336 prefixEnd_99336 := by exact prefixLift 99336
  have htrace : WordTrace (prefixWord ++ tailWord_99336) baseStart_99336 baseEnd_99336 := by
    simpa [prefixWord, tailWord_99336, baseEnd_99336] using wordTrace_append hprefix tailTrace_99336
  have hstable : (prefixWord ++ tailWord_99336).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99336).length < 2 ^ (prefixWord ++ tailWord_99336).sum := by decide
  have hdescent : baseEnd_99336 < baseStart_99336 := by decide
  rcases family_descends (prefixWord ++ tailWord_99336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99351 : List Nat := [1, 1, 3, 5, 1, 3, 1, 4]
def baseStart_99351 : Nat := 118140960795 + 99351 * 2 ^ 59
def prefixEnd_99351 : Nat := 4983230072969 + 3 ^ 40 * 99351 * 2
def baseEnd_99351 : Nat := 30231002373301346640355

theorem tailTrace_99351 : CollatzResearch.WordTrace tailWord_99351 prefixEnd_99351 30231002373301346640355 := by
  unfold tailWord_99351
  simp only [CollatzResearch.WordTrace]
  refine ⟨3623628663075769645033907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2415752442050513096689271 3623628663075769645033907)
  ·
    refine ⟨5435442994613654467550861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3623628663075769645033907 5435442994613654467550861)
    ·
      refine ⟨2038291122980120425331573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5435442994613654467550861 2038291122980120425331573)
      ·
        refine ⟨191089792779386289874835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2038291122980120425331573 191089792779386289874835)
        ·
          refine ⟨286634689169079434812253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191089792779386289874835 286634689169079434812253)
          ·
            refine ⟨107488008438404788054595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 286634689169079434812253 107488008438404788054595)
            ·
              refine ⟨161232012657607182081893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107488008438404788054595 161232012657607182081893)
              ·
                refine ⟨30231002373301346640355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 161232012657607182081893 30231002373301346640355)
                ·
                  rfl

theorem cell19_99351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 1, 4].length) (baseStart_99351 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_99351 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_99351 prefixEnd_99351 := by exact prefixLift 99351
  have htrace : WordTrace (prefixWord ++ tailWord_99351) baseStart_99351 baseEnd_99351 := by
    simpa [prefixWord, tailWord_99351, baseEnd_99351] using wordTrace_append hprefix tailTrace_99351
  have hstable : (prefixWord ++ tailWord_99351).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99351).length < 2 ^ (prefixWord ++ tailWord_99351).sum := by decide
  have hdescent : baseEnd_99351 < baseStart_99351 := by decide
  rcases family_descends (prefixWord ++ tailWord_99351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99372 : List Nat := [2, 2, 1, 1, 1, 2, 7, 3]
def baseStart_99372 : Nat := 118140960795 + 99372 * 2 ^ 59
def prefixEnd_99372 : Nat := 4983230072969 + 3 ^ 40 * 99372 * 2
def baseEnd_99372 : Nat := 30237392354779520173631

theorem tailTrace_99372 : CollatzResearch.WordTrace tailWord_99372 prefixEnd_99372 30237392354779520173631 := by
  unfold tailWord_99372
  simp only [CollatzResearch.WordTrace]
  refine ⟨1812197297999845115774185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2416263063999793487698913 1812197297999845115774185)
  ·
    refine ⟨1359147973499883836830639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1812197297999845115774185 1359147973499883836830639)
    ·
      refine ⟨2038721960249825755245959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1359147973499883836830639 2038721960249825755245959)
      ·
        refine ⟨3058082940374738632868939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2038721960249825755245959 3058082940374738632868939)
        ·
          refine ⟨4587124410562107949303409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3058082940374738632868939 4587124410562107949303409)
          ·
            refine ⟨3440343307921580961977557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4587124410562107949303409 3440343307921580961977557)
            ·
              refine ⟨80633046279412053796349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 3440343307921580961977557 80633046279412053796349)
              ·
                refine ⟨30237392354779520173631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80633046279412053796349 30237392354779520173631)
                ·
                  rfl

theorem cell19_99372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 7, 3].length) (baseStart_99372 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_99372 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_99372 prefixEnd_99372 := by exact prefixLift 99372
  have htrace : WordTrace (prefixWord ++ tailWord_99372) baseStart_99372 baseEnd_99372 := by
    simpa [prefixWord, tailWord_99372, baseEnd_99372] using wordTrace_append hprefix tailTrace_99372
  have hstable : (prefixWord ++ tailWord_99372).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99372).length < 2 ^ (prefixWord ++ tailWord_99372).sum := by decide
  have hdescent : baseEnd_99372 < baseStart_99372 := by decide
  rcases family_descends (prefixWord ++ tailWord_99372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99488 : List Nat := [2, 1, 1, 4, 2, 1, 1, 7]
def baseStart_99488 : Nat := 118140960795 + 99488 * 2 ^ 59
def prefixEnd_99488 : Nat := 4983230072969 + 3 ^ 40 * 99488 * 2
def baseEnd_99488 : Nat := 30272689395325621595537

theorem tailTrace_99488 : CollatzResearch.WordTrace tailWord_99488 prefixEnd_99488 30272689395325621595537 := by
  unfold tailWord_99488
  simp only [CollatzResearch.WordTrace]
  refine ⟨1814312731789721021385559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2419083642386294695180745 1814312731789721021385559)
  ·
    refine ⟨2721469097684581532078339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1814312731789721021385559 2721469097684581532078339)
    ·
      refine ⟨4082203646526872298117509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2721469097684581532078339 4082203646526872298117509)
      ·
        refine ⟨765413183723788555897033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4082203646526872298117509 765413183723788555897033)
        ·
          refine ⟨574059887792841416922775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 765413183723788555897033 574059887792841416922775)
          ·
            refine ⟨861089831689262125384163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 574059887792841416922775 861089831689262125384163)
            ·
              refine ⟨1291634747533893188076245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 861089831689262125384163 1291634747533893188076245)
              ·
                refine ⟨30272689395325621595537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1291634747533893188076245 30272689395325621595537)
                ·
                  rfl

theorem cell19_99488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 7].length) (baseStart_99488 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_99488 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_99488 prefixEnd_99488 := by exact prefixLift 99488
  have htrace : WordTrace (prefixWord ++ tailWord_99488) baseStart_99488 baseEnd_99488 := by
    simpa [prefixWord, tailWord_99488, baseEnd_99488] using wordTrace_append hprefix tailTrace_99488
  have hstable : (prefixWord ++ tailWord_99488).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99488).length < 2 ^ (prefixWord ++ tailWord_99488).sum := by decide
  have hdescent : baseEnd_99488 < baseStart_99488 := by decide
  rcases family_descends (prefixWord ++ tailWord_99488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99541 : List Nat := [1, 3, 2, 4, 1, 2, 3, 3]
def baseStart_99541 : Nat := 118140960795 + 99541 * 2 ^ 59
def prefixEnd_99541 : Nat := 4983230072969 + 3 ^ 40 * 99541 * 2
def baseEnd_99541 : Nat := 30288816491437202417615

theorem tailTrace_99541 : CollatzResearch.WordTrace tailWord_99541 prefixEnd_99541 30288816491437202417615 := by
  unfold tailWord_99541
  simp only [CollatzResearch.WordTrace]
  refine ⟨3630558532387432094450477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2420372354924954729633651 3630558532387432094450477)
  ·
    refine ⟨1361459449645287035418929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3630558532387432094450477 1361459449645287035418929)
    ·
      refine ⟨1021094587233965276564197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1361459449645287035418929 1021094587233965276564197)
      ·
        refine ⟨191455235106368489355787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1021094587233965276564197 191455235106368489355787)
        ·
          refine ⟨287182852659552734033681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191455235106368489355787 287182852659552734033681)
          ·
            refine ⟨215387139494664550525261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 287182852659552734033681 215387139494664550525261)
            ·
              refine ⟨80770177310499206446973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 215387139494664550525261 80770177310499206446973)
              ·
                refine ⟨30288816491437202417615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80770177310499206446973 30288816491437202417615)
                ·
                  rfl

theorem cell19_99541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 3, 3].length) (baseStart_99541 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_99541 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_99541 prefixEnd_99541 := by exact prefixLift 99541
  have htrace : WordTrace (prefixWord ++ tailWord_99541) baseStart_99541 baseEnd_99541 := by
    simpa [prefixWord, tailWord_99541, baseEnd_99541] using wordTrace_append hprefix tailTrace_99541
  have hstable : (prefixWord ++ tailWord_99541).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99541).length < 2 ^ (prefixWord ++ tailWord_99541).sum := by decide
  have hdescent : baseEnd_99541 < baseStart_99541 := by decide
  rcases family_descends (prefixWord ++ tailWord_99541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99564 : List Nat := [2, 2, 1, 1, 2, 5, 6]
def baseStart_99564 : Nat := 118140960795 + 99564 * 2 ^ 59
def prefixEnd_99564 : Nat := 4983230072969 + 3 ^ 40 * 99564 * 2
def baseEnd_99564 : Nat := 10098605014193321302147

theorem tailTrace_99564 : CollatzResearch.WordTrace tailWord_99564 prefixEnd_99564 10098605014193321302147 := by
  unfold tailWord_99564
  simp only [CollatzResearch.WordTrace]
  refine ⟨1815698705652053511268873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2420931607536071348358497 1815698705652053511268873)
  ·
    refine ⟨1361774029239040133451655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1815698705652053511268873 1361774029239040133451655)
    ·
      refine ⟨2042661043858560200177483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1361774029239040133451655 2042661043858560200177483)
      ·
        refine ⟨3063991565787840300266225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2042661043858560200177483 3063991565787840300266225)
        ·
          refine ⟨2297993674340880225199669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3063991565787840300266225 2297993674340880225199669)
          ·
            refine ⟨215436906969457521112469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2297993674340880225199669 215436906969457521112469)
            ·
              refine ⟨10098605014193321302147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 215436906969457521112469 10098605014193321302147)
              ·
                rfl

theorem cell19_99564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 6].length) (baseStart_99564 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_99564 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_99564 prefixEnd_99564 := by exact prefixLift 99564
  have htrace : WordTrace (prefixWord ++ tailWord_99564) baseStart_99564 baseEnd_99564 := by
    simpa [prefixWord, tailWord_99564, baseEnd_99564] using wordTrace_append hprefix tailTrace_99564
  have hstable : (prefixWord ++ tailWord_99564).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99564).length < 2 ^ (prefixWord ++ tailWord_99564).sum := by decide
  have hdescent : baseEnd_99564 < baseStart_99564 := by decide
  rcases family_descends (prefixWord ++ tailWord_99564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99598 : List Nat := [4, 1, 1, 2, 1, 5, 2, 3]
def baseStart_99598 : Nat := 118140960795 + 99598 * 2 ^ 59
def prefixEnd_99598 : Nat := 4983230072969 + 3 ^ 40 * 99598 * 2
def baseEnd_99598 : Nat := 30306160726877959150793

theorem tailTrace_99598 : CollatzResearch.WordTrace tailWord_99598 prefixEnd_99598 30306160726877959150793 := by
  unfold tailWord_99598
  simp only [CollatzResearch.WordTrace]
  refine ⟨454079686647616353659431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2421758328787287219516965 454079686647616353659431)
  ·
    refine ⟨681119529971424530489147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 454079686647616353659431 681119529971424530489147)
    ·
      refine ⟨1021679294957136795733721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 681119529971424530489147 1021679294957136795733721)
      ·
        refine ⟨766259471217852596800291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1021679294957136795733721 766259471217852596800291)
        ·
          refine ⟨1149389206826778895200437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 766259471217852596800291 1149389206826778895200437)
          ·
            refine ⟨107755238140010521425041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1149389206826778895200437 107755238140010521425041)
            ·
              refine ⟨80816428605007891068781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107755238140010521425041 80816428605007891068781)
              ·
                refine ⟨30306160726877959150793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80816428605007891068781 30306160726877959150793)
                ·
                  rfl

theorem cell19_99598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 2, 3].length) (baseStart_99598 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_99598 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_99598 prefixEnd_99598 := by exact prefixLift 99598
  have htrace : WordTrace (prefixWord ++ tailWord_99598) baseStart_99598 baseEnd_99598 := by
    simpa [prefixWord, tailWord_99598, baseEnd_99598] using wordTrace_append hprefix tailTrace_99598
  have hstable : (prefixWord ++ tailWord_99598).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99598).length < 2 ^ (prefixWord ++ tailWord_99598).sum := by decide
  have hdescent : baseEnd_99598 < baseStart_99598 := by decide
  rcases family_descends (prefixWord ++ tailWord_99598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99621 : List Nat := [1, 3, 1, 2, 4, 1, 7]
def baseStart_99621 : Nat := 118140960795 + 99621 * 2 ^ 59
def prefixEnd_99621 : Nat := 4983230072969 + 3 ^ 40 * 99621 * 2
def baseEnd_99621 : Nat := 10104386426006906879873

theorem tailTrace_99621 : CollatzResearch.WordTrace tailWord_99621 prefixEnd_99621 10104386426006906879873 := by
  unfold tailWord_99621
  simp only [CollatzResearch.WordTrace]
  refine ⟨3633476372097605757362717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2422317581398403838241811 3633476372097605757362717)
  ·
    refine ⟨1362553639536602159011019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3633476372097605757362717 1362553639536602159011019)
    ·
      refine ⟨2043830459304903238516529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1362553639536602159011019 2043830459304903238516529)
      ·
        refine ⟨1532872844478677428887397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2043830459304903238516529 1532872844478677428887397)
        ·
          refine ⟨287413658339752017916387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1532872844478677428887397 287413658339752017916387)
          ·
            refine ⟨431120487509628026874581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 287413658339752017916387 431120487509628026874581)
            ·
              refine ⟨10104386426006906879873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 431120487509628026874581 10104386426006906879873)
              ·
                rfl

theorem cell19_99621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 7].length) (baseStart_99621 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_99621 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_99621 prefixEnd_99621 := by exact prefixLift 99621
  have htrace : WordTrace (prefixWord ++ tailWord_99621) baseStart_99621 baseEnd_99621 := by
    simpa [prefixWord, tailWord_99621, baseEnd_99621] using wordTrace_append hprefix tailTrace_99621
  have hstable : (prefixWord ++ tailWord_99621).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99621).length < 2 ^ (prefixWord ++ tailWord_99621).sum := by decide
  have hdescent : baseEnd_99621 < baseStart_99621 := by decide
  rcases family_descends (prefixWord ++ tailWord_99621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99670 : List Nat := [5, 2, 3, 1, 2, 6]
def baseStart_99670 : Nat := 118140960795 + 99670 * 2 ^ 59
def prefixEnd_99670 : Nat := 4983230072969 + 3 ^ 40 * 99670 * 2
def baseEnd_99670 : Nat := 3369785470533680616733

theorem tailTrace_99670 : CollatzResearch.WordTrace tailWord_99670 prefixEnd_99670 3369785470533680616733 := by
  unfold tailWord_99670
  simp only [CollatzResearch.WordTrace]
  refine ⟨227203971807505445368529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2423509032613391417264309 227203971807505445368529)
  ·
    refine ⟨170402978855629084026397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227203971807505445368529 170402978855629084026397)
    ·
      refine ⟨63901117070860906509899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 170402978855629084026397 63901117070860906509899)
      ·
        refine ⟨95851675606291359764849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63901117070860906509899 95851675606291359764849)
        ·
          refine ⟨71888756704718519823637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95851675606291359764849 71888756704718519823637)
          ·
            refine ⟨3369785470533680616733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 71888756704718519823637 3369785470533680616733)
            ·
              rfl

theorem cell19_99670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 6].length) (baseStart_99670 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_99670 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_99670 prefixEnd_99670 := by exact prefixLift 99670
  have htrace : WordTrace (prefixWord ++ tailWord_99670) baseStart_99670 baseEnd_99670 := by
    simpa [prefixWord, tailWord_99670, baseEnd_99670] using wordTrace_append hprefix tailTrace_99670
  have hstable : (prefixWord ++ tailWord_99670).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99670).length < 2 ^ (prefixWord ++ tailWord_99670).sum := by decide
  have hdescent : baseEnd_99670 < baseStart_99670 := by decide
  rcases family_descends (prefixWord ++ tailWord_99670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99697 : List Nat := [1, 2, 2, 2, 1, 2, 5, 4]
def baseStart_99697 : Nat := 118140960795 + 99697 * 2 ^ 59
def prefixEnd_99697 : Nat := 4983230072969 + 3 ^ 40 * 99697 * 2
def baseEnd_99697 : Nat := 30336284925275062950523

theorem tailTrace_99697 : CollatzResearch.WordTrace tailWord_99697 prefixEnd_99697 30336284925275062950523 := by
  unfold tailWord_99697
  simp only [CollatzResearch.WordTrace]
  refine ⟨3636248319822270737129345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2424165546548180491419563 3636248319822270737129345)
  ·
    refine ⟨2727186239866703052847009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3636248319822270737129345 2727186239866703052847009)
    ·
      refine ⟨2045389679900027289635257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2727186239866703052847009 2045389679900027289635257)
      ·
        refine ⟨1534042259925020467226443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2045389679900027289635257 1534042259925020467226443)
        ·
          refine ⟨2301063389887530700839665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1534042259925020467226443 2301063389887530700839665)
          ·
            refine ⟨1725797542415648025629749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2301063389887530700839665 1725797542415648025629749)
            ·
              refine ⟨161793519601467002402789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1725797542415648025629749 161793519601467002402789)
              ·
                refine ⟨30336284925275062950523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 161793519601467002402789 30336284925275062950523)
                ·
                  rfl

theorem cell19_99697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 5, 4].length) (baseStart_99697 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_99697 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_99697 prefixEnd_99697 := by exact prefixLift 99697
  have htrace : WordTrace (prefixWord ++ tailWord_99697) baseStart_99697 baseEnd_99697 := by
    simpa [prefixWord, tailWord_99697, baseEnd_99697] using wordTrace_append hprefix tailTrace_99697
  have hstable : (prefixWord ++ tailWord_99697).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99697).length < 2 ^ (prefixWord ++ tailWord_99697).sum := by decide
  have hdescent : baseEnd_99697 < baseStart_99697 := by decide
  rcases family_descends (prefixWord ++ tailWord_99697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99769 : List Nat := [1, 2, 1, 4, 4, 2, 2, 3]
def baseStart_99769 : Nat := 118140960795 + 99769 * 2 ^ 59
def prefixEnd_99769 : Nat := 4983230072969 + 3 ^ 40 * 99769 * 2
def baseEnd_99769 : Nat := 30358193433200229350327

theorem tailTrace_99769 : CollatzResearch.WordTrace tailWord_99769 prefixEnd_99769 30358193433200229350327 := by
  unfold tailWord_99769
  simp only [CollatzResearch.WordTrace]
  refine ⟨3638874375561427033750361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2425916250374284689166907 3638874375561427033750361)
  ·
    refine ⟨2729155781671070275312771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3638874375561427033750361 2729155781671070275312771)
    ·
      refine ⟨4093733672506605412969157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2729155781671070275312771 4093733672506605412969157)
      ·
        refine ⟨767575063594988514931717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4093733672506605412969157 767575063594988514931717)
        ·
          refine ⟨143920324424060346549697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 767575063594988514931717 143920324424060346549697)
          ·
            refine ⟨107940243318045259912273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 143920324424060346549697 107940243318045259912273)
            ·
              refine ⟨80955182488533944934205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107940243318045259912273 80955182488533944934205)
              ·
                refine ⟨30358193433200229350327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80955182488533944934205 30358193433200229350327)
                ·
                  rfl

theorem cell19_99769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 2, 3].length) (baseStart_99769 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_99769 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_99769 prefixEnd_99769 := by exact prefixLift 99769
  have htrace : WordTrace (prefixWord ++ tailWord_99769) baseStart_99769 baseEnd_99769 := by
    simpa [prefixWord, tailWord_99769, baseEnd_99769] using wordTrace_append hprefix tailTrace_99769
  have hstable : (prefixWord ++ tailWord_99769).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99769).length < 2 ^ (prefixWord ++ tailWord_99769).sum := by decide
  have hdescent : baseEnd_99769 < baseStart_99769 := by decide
  rcases family_descends (prefixWord ++ tailWord_99769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99773 : List Nat := [1, 4, 1, 2, 2, 1, 3, 5]
def baseStart_99773 : Nat := 118140960795 + 99773 * 2 ^ 59
def prefixEnd_99773 : Nat := 4983230072969 + 3 ^ 40 * 99773 * 2
def baseEnd_99773 : Nat := 30359410572529405261427

theorem tailTrace_99773 : CollatzResearch.WordTrace tailWord_99773 prefixEnd_99773 30359410572529405261427 := by
  unfold tailWord_99773
  simp only [CollatzResearch.WordTrace]
  refine ⟨3639020267546935716895973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2426013511697957144597315 3639020267546935716895973)
  ·
    refine ⟨682316300165050446917995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3639020267546935716895973 682316300165050446917995)
    ·
      refine ⟨1023474450247575670376993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 682316300165050446917995 1023474450247575670376993)
      ·
        refine ⟨767605837685681752782745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1023474450247575670376993 767605837685681752782745)
        ·
          refine ⟨575704378264261314587059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 767605837685681752782745 575704378264261314587059)
          ·
            refine ⟨863556567396391971880589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 575704378264261314587059 863556567396391971880589)
            ·
              refine ⟨323833712773646989455221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 863556567396391971880589 323833712773646989455221)
              ·
                refine ⟨30359410572529405261427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 323833712773646989455221 30359410572529405261427)
                ·
                  rfl

theorem cell19_99773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 5].length) (baseStart_99773 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_99773 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_99773 prefixEnd_99773 := by exact prefixLift 99773
  have htrace : WordTrace (prefixWord ++ tailWord_99773) baseStart_99773 baseEnd_99773 := by
    simpa [prefixWord, tailWord_99773, baseEnd_99773] using wordTrace_append hprefix tailTrace_99773
  have hstable : (prefixWord ++ tailWord_99773).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99773).length < 2 ^ (prefixWord ++ tailWord_99773).sum := by decide
  have hdescent : baseEnd_99773 < baseStart_99773 := by decide
  rcases family_descends (prefixWord ++ tailWord_99773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99811 : List Nat := [1, 1, 1, 6, 2, 1, 1, 6]
def baseStart_99811 : Nat := 118140960795 + 99811 * 2 ^ 59
def prefixEnd_99811 : Nat := 4983230072969 + 3 ^ 40 * 99811 * 2
def baseEnd_99811 : Nat := 30370973396156576416879

theorem tailTrace_99811 : CollatzResearch.WordTrace tailWord_99811 prefixEnd_99811 30370973396156576416879 := by
  unfold tailWord_99811
  simp only [CollatzResearch.WordTrace]
  refine ⟨3640406241409268206779287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2426937494272845471186191 3640406241409268206779287)
  ·
    refine ⟨5460609362113902310168931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3640406241409268206779287 5460609362113902310168931)
    ·
      refine ⟨8190914043170853465253397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5460609362113902310168931 8190914043170853465253397)
      ·
        refine ⟨383949095773633756183753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 8190914043170853465253397 383949095773633756183753)
        ·
          refine ⟨287961821830225317137815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 383949095773633756183753 287961821830225317137815)
          ·
            refine ⟨431942732745337975706723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 287961821830225317137815 431942732745337975706723)
            ·
              refine ⟨647914099118006963560085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 431942732745337975706723 647914099118006963560085)
              ·
                refine ⟨30370973396156576416879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 647914099118006963560085 30370973396156576416879)
                ·
                  rfl

theorem cell19_99811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 6].length) (baseStart_99811 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_99811 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_99811 prefixEnd_99811 := by exact prefixLift 99811
  have htrace : WordTrace (prefixWord ++ tailWord_99811) baseStart_99811 baseEnd_99811 := by
    simpa [prefixWord, tailWord_99811, baseEnd_99811] using wordTrace_append hprefix tailTrace_99811
  have hstable : (prefixWord ++ tailWord_99811).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99811).length < 2 ^ (prefixWord ++ tailWord_99811).sum := by decide
  have hdescent : baseEnd_99811 < baseStart_99811 := by decide
  rcases family_descends (prefixWord ++ tailWord_99811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99851 : List Nat := [1, 1, 1, 1, 15]
def baseStart_99851 : Nat := 118140960795 + 99851 * 2 ^ 59
def prefixEnd_99851 : Nat := 4983230072969 + 3 ^ 40 * 99851 * 2
def baseEnd_99851 : Nat := 1125301658868456871403

theorem tailTrace_99851 : CollatzResearch.WordTrace tailWord_99851 prefixEnd_99851 1125301658868456871403 := by
  unfold tailWord_99851
  simp only [CollatzResearch.WordTrace]
  refine ⟨3641865161264355038235407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2427910107509570025490271 3641865161264355038235407)
  ·
    refine ⟨5462797741896532557353111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3641865161264355038235407 5462797741896532557353111)
    ·
      refine ⟨8194196612844798836029667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5462797741896532557353111 8194196612844798836029667)
      ·
        refine ⟨12291294919267198254044501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8194196612844798836029667 12291294919267198254044501)
        ·
          refine ⟨1125301658868456871403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 15 12291294919267198254044501 1125301658868456871403)
          ·
            rfl

theorem cell19_99851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 15].length) (baseStart_99851 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_99851 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_99851 prefixEnd_99851 := by exact prefixLift 99851
  have htrace : WordTrace (prefixWord ++ tailWord_99851) baseStart_99851 baseEnd_99851 := by
    simpa [prefixWord, tailWord_99851, baseEnd_99851] using wordTrace_append hprefix tailTrace_99851
  have hstable : (prefixWord ++ tailWord_99851).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99851).length < 2 ^ (prefixWord ++ tailWord_99851).sum := by decide
  have hdescent : baseEnd_99851 < baseStart_99851 := by decide
  rcases family_descends (prefixWord ++ tailWord_99851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99864 : List Nat := [2, 1, 2, 3, 5, 1, 1, 4]
def baseStart_99864 : Nat := 118140960795 + 99864 * 2 ^ 59
def prefixEnd_99864 : Nat := 4983230072969 + 3 ^ 40 * 99864 * 2
def baseEnd_99864 : Nat := 30387100492268157238957

theorem tailTrace_99864 : CollatzResearch.WordTrace tailWord_99864 prefixEnd_99864 30387100492268157238957 := by
  unfold tailWord_99864
  simp only [CollatzResearch.WordTrace]
  refine ⟨1821169655108629129229323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2428226206811505505639097 1821169655108629129229323)
  ·
    refine ⟨2731754482662943693843985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1821169655108629129229323 2731754482662943693843985)
    ·
      refine ⟨2048815861997207770382989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2731754482662943693843985 2048815861997207770382989)
      ·
        refine ⟨768305948248952913893621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2048815861997207770382989 768305948248952913893621)
        ·
          refine ⟨72028682648339335677527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 768305948248952913893621 72028682648339335677527)
          ·
            refine ⟨108043023972509003516291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72028682648339335677527 108043023972509003516291)
            ·
              refine ⟨162064535958763505274437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108043023972509003516291 162064535958763505274437)
              ·
                refine ⟨30387100492268157238957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 162064535958763505274437 30387100492268157238957)
                ·
                  rfl

theorem cell19_99864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 1, 4].length) (baseStart_99864 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_99864 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_99864 prefixEnd_99864 := by exact prefixLift 99864
  have htrace : WordTrace (prefixWord ++ tailWord_99864) baseStart_99864 baseEnd_99864 := by
    simpa [prefixWord, tailWord_99864, baseEnd_99864] using wordTrace_append hprefix tailTrace_99864
  have hstable : (prefixWord ++ tailWord_99864).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99864).length < 2 ^ (prefixWord ++ tailWord_99864).sum := by decide
  have hdescent : baseEnd_99864 < baseStart_99864 := by decide
  rcases family_descends (prefixWord ++ tailWord_99864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99982 : List Nat := [4, 1, 1, 3, 1, 2, 1, 6]
def baseStart_99982 : Nat := 118140960795 + 99982 * 2 ^ 59
def prefixEnd_99982 : Nat := 4983230072969 + 3 ^ 40 * 99982 * 2
def baseEnd_99982 : Nat := 30423006102478846616413

theorem tailTrace_99982 : CollatzResearch.WordTrace tailWord_99982 prefixEnd_99982 30423006102478846616413 := by
  unfold tailWord_99982
  simp only [CollatzResearch.WordTrace]
  refine ⟨455830390473720551406775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2431095415859842940836133 455830390473720551406775)
  ·
    refine ⟨683745585710580827110163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 455830390473720551406775 683745585710580827110163)
    ·
      refine ⟨1025618378565871240665245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 683745585710580827110163 1025618378565871240665245)
      ·
        refine ⟨384606891962201715249467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1025618378565871240665245 384606891962201715249467)
        ·
          refine ⟨576910337943302572874201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 384606891962201715249467 576910337943302572874201)
          ·
            refine ⟨432682753457476929655651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 576910337943302572874201 432682753457476929655651)
            ·
              refine ⟨649024130186215394483477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 432682753457476929655651 649024130186215394483477)
              ·
                refine ⟨30423006102478846616413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 649024130186215394483477 30423006102478846616413)
                ·
                  rfl

theorem cell19_99982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 6].length) (baseStart_99982 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_99982 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_99982 prefixEnd_99982 := by exact prefixLift 99982
  have htrace : WordTrace (prefixWord ++ tailWord_99982) baseStart_99982 baseEnd_99982 := by
    simpa [prefixWord, tailWord_99982, baseEnd_99982] using wordTrace_append hprefix tailTrace_99982
  have hstable : (prefixWord ++ tailWord_99982).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99982).length < 2 ^ (prefixWord ++ tailWord_99982).sum := by decide
  have hdescent : baseEnd_99982 < baseStart_99982 := by decide
  rcases family_descends (prefixWord ++ tailWord_99982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100001 : List Nat := [1, 2, 3, 3, 2, 1, 2, 5]
def baseStart_100001 : Nat := 118140960795 + 100001 * 2 ^ 59
def prefixEnd_100001 : Nat := 4983230072969 + 3 ^ 40 * 100001 * 2
def baseEnd_100001 : Nat := 30428787514292432194139

theorem tailTrace_100001 : CollatzResearch.WordTrace tailWord_100001 prefixEnd_100001 30428787514292432194139 := by
  unfold tailWord_100001
  simp only [CollatzResearch.WordTrace]
  refine ⟨3647336110720930656195857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2431557407147287104130571 3647336110720930656195857)
  ·
    refine ⟨2735502083040697992146893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3647336110720930656195857 2735502083040697992146893)
    ·
      refine ⟨1025813281140261747055085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2735502083040697992146893 1025813281140261747055085)
      ·
        refine ⟨384679980427598155145657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1025813281140261747055085 384679980427598155145657)
        ·
          refine ⟨288509985320698616359243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 384679980427598155145657 288509985320698616359243)
          ·
            refine ⟨432764977981047924538865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 288509985320698616359243 432764977981047924538865)
            ·
              refine ⟨324573733485785943404149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 432764977981047924538865 324573733485785943404149)
              ·
                refine ⟨30428787514292432194139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 324573733485785943404149 30428787514292432194139)
                ·
                  rfl

theorem cell19_100001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 5].length) (baseStart_100001 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_100001 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_100001 prefixEnd_100001 := by exact prefixLift 100001
  have htrace : WordTrace (prefixWord ++ tailWord_100001) baseStart_100001 baseEnd_100001 := by
    simpa [prefixWord, tailWord_100001, baseEnd_100001] using wordTrace_append hprefix tailTrace_100001
  have hstable : (prefixWord ++ tailWord_100001).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100001).length < 2 ^ (prefixWord ++ tailWord_100001).sum := by decide
  have hdescent : baseEnd_100001 < baseStart_100001 := by decide
  rcases family_descends (prefixWord ++ tailWord_100001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100003 : List Nat := [1, 1, 1, 4, 1, 1, 3, 7]
def baseStart_100003 : Nat := 118140960795 + 100003 * 2 ^ 59
def prefixEnd_100003 : Nat := 4983230072969 + 3 ^ 40 * 100003 * 2
def baseEnd_100003 : Nat := 30429396083957020149689

theorem tailTrace_100003 : CollatzResearch.WordTrace tailWord_100003 prefixEnd_100003 30429396083957020149689 := by
  unfold tailWord_100003
  simp only [CollatzResearch.WordTrace]
  refine ⟨3647409056713684997768663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2431606037809123331845775 3647409056713684997768663)
  ·
    refine ⟨5471113585070527496652995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3647409056713684997768663 5471113585070527496652995)
    ·
      refine ⟨8206670377605791244979493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5471113585070527496652995 8206670377605791244979493)
      ·
        refine ⟨1538750695801085858433655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8206670377605791244979493 1538750695801085858433655)
        ·
          refine ⟨2308126043701628787650483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1538750695801085858433655 2308126043701628787650483)
          ·
            refine ⟨3462189065552443181475725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2308126043701628787650483 3462189065552443181475725)
            ·
              refine ⟨1298320899582166193053397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3462189065552443181475725 1298320899582166193053397)
              ·
                refine ⟨30429396083957020149689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1298320899582166193053397 30429396083957020149689)
                ·
                  rfl

theorem cell19_100003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 7].length) (baseStart_100003 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_100003 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_100003 prefixEnd_100003 := by exact prefixLift 100003
  have htrace : WordTrace (prefixWord ++ tailWord_100003) baseStart_100003 baseEnd_100003 := by
    simpa [prefixWord, tailWord_100003, baseEnd_100003] using wordTrace_append hprefix tailTrace_100003
  have hstable : (prefixWord ++ tailWord_100003).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100003).length < 2 ^ (prefixWord ++ tailWord_100003).sum := by decide
  have hdescent : baseEnd_100003 < baseStart_100003 := by decide
  rcases family_descends (prefixWord ++ tailWord_100003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100077 : List Nat := [1, 5, 1, 2, 1, 3, 6]
def baseStart_100077 : Nat := 118140960795 + 100077 * 2 ^ 59
def prefixEnd_100077 : Nat := 4983230072969 + 3 ^ 40 * 100077 * 2
def baseEnd_100077 : Nat := 10150637720515591501681

theorem tailTrace_100077 : CollatzResearch.WordTrace tailWord_100077 prefixEnd_100077 10150637720515591501681 := by
  unfold tailWord_100077
  simp only [CollatzResearch.WordTrace]
  refine ⟨3650108058445595635962485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2433405372297063757308323 3650108058445595635962485)
  ·
    refine ⟨342197630479274590871483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3650108058445595635962485 342197630479274590871483)
    ·
      refine ⟨513296445718911886307225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 342197630479274590871483 513296445718911886307225)
      ·
        refine ⟨384972334289183914730419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 513296445718911886307225 384972334289183914730419)
        ·
          refine ⟨577458501433775872095629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 384972334289183914730419 577458501433775872095629)
          ·
            refine ⟨216546938037665952035861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 577458501433775872095629 216546938037665952035861)
            ·
              refine ⟨10150637720515591501681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 216546938037665952035861 10150637720515591501681)
              ·
                rfl

theorem cell19_100077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 6].length) (baseStart_100077 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_100077 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_100077 prefixEnd_100077 := by exact prefixLift 100077
  have htrace : WordTrace (prefixWord ++ tailWord_100077) baseStart_100077 baseEnd_100077 := by
    simpa [prefixWord, tailWord_100077, baseEnd_100077] using wordTrace_append hprefix tailTrace_100077
  have hstable : (prefixWord ++ tailWord_100077).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100077).length < 2 ^ (prefixWord ++ tailWord_100077).sum := by decide
  have hdescent : baseEnd_100077 < baseStart_100077 := by decide
  rcases family_descends (prefixWord ++ tailWord_100077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100079 : List Nat := [1, 1, 2, 1, 5, 1, 8]
def baseStart_100079 : Nat := 118140960795 + 100079 * 2 ^ 59
def prefixEnd_100079 : Nat := 4983230072969 + 3 ^ 40 * 100079 * 2
def baseEnd_100079 : Nat := 10150840577070454153531

theorem tailTrace_100079 : CollatzResearch.WordTrace tailWord_100079 prefixEnd_100079 10150840577070454153531 := by
  unfold tailWord_100079
  simp only [CollatzResearch.WordTrace]
  refine ⟨3650181004438349977535291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2433454002958899985023527 3650181004438349977535291)
  ·
    refine ⟨5475271506657524966302937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3650181004438349977535291 5475271506657524966302937)
    ·
      refine ⟨4106453629993143724727203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5475271506657524966302937 4106453629993143724727203)
      ·
        refine ⟨6159680444989715587090805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4106453629993143724727203 6159680444989715587090805)
        ·
          refine ⟨577470041717785836289763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6159680444989715587090805 577470041717785836289763)
          ·
            refine ⟨866205062576678754434645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 577470041717785836289763 866205062576678754434645)
            ·
              refine ⟨10150840577070454153531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 866205062576678754434645 10150840577070454153531)
              ·
                rfl

theorem cell19_100079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 8].length) (baseStart_100079 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_100079 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_100079 prefixEnd_100079 := by exact prefixLift 100079
  have htrace : WordTrace (prefixWord ++ tailWord_100079) baseStart_100079 baseEnd_100079 := by
    simpa [prefixWord, tailWord_100079, baseEnd_100079] using wordTrace_append hprefix tailTrace_100079
  have hstable : (prefixWord ++ tailWord_100079).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100079).length < 2 ^ (prefixWord ++ tailWord_100079).sum := by decide
  have hdescent : baseEnd_100079 < baseStart_100079 := by decide
  rcases family_descends (prefixWord ++ tailWord_100079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100225 : List Nat := [1, 2, 4, 4, 1, 1, 3, 3]
def baseStart_100225 : Nat := 118140960795 + 100225 * 2 ^ 59
def prefixEnd_100225 : Nat := 4983230072969 + 3 ^ 40 * 100225 * 2
def baseEnd_100225 : Nat := 30496947316726283215751

theorem tailTrace_100225 : CollatzResearch.WordTrace tailWord_100225 prefixEnd_100225 30496947316726283215751 := by
  unfold tailWord_100225
  simp only [CollatzResearch.WordTrace]
  refine ⟨3655506061909416912350129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2437004041272944608233419 3655506061909416912350129)
  ·
    refine ⟨2741629546432062684262597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3655506061909416912350129 2741629546432062684262597)
    ·
      refine ⟨514055539956011753299237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2741629546432062684262597 514055539956011753299237)
      ·
        refine ⟨96385413741752203743607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 514055539956011753299237 96385413741752203743607)
        ·
          refine ⟨144578120612628305615411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96385413741752203743607 144578120612628305615411)
          ·
            refine ⟨216867180918942458423117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144578120612628305615411 216867180918942458423117)
            ·
              refine ⟨81325192844603421908669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 216867180918942458423117 81325192844603421908669)
              ·
                refine ⟨30496947316726283215751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81325192844603421908669 30496947316726283215751)
                ·
                  rfl

theorem cell19_100225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 3, 3].length) (baseStart_100225 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_100225 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_100225 prefixEnd_100225 := by exact prefixLift 100225
  have htrace : WordTrace (prefixWord ++ tailWord_100225) baseStart_100225 baseEnd_100225 := by
    simpa [prefixWord, tailWord_100225, baseEnd_100225] using wordTrace_append hprefix tailTrace_100225
  have hstable : (prefixWord ++ tailWord_100225).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100225).length < 2 ^ (prefixWord ++ tailWord_100225).sum := by decide
  have hdescent : baseEnd_100225 < baseStart_100225 := by decide
  rcases family_descends (prefixWord ++ tailWord_100225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100229 : List Nat := [1, 3, 1, 1, 3, 2, 5, 3]
def baseStart_100229 : Nat := 118140960795 + 100229 * 2 ^ 59
def prefixEnd_100229 : Nat := 4983230072969 + 3 ^ 40 * 100229 * 2
def baseEnd_100229 : Nat := 30498164456055459126851

theorem tailTrace_100229 : CollatzResearch.WordTrace tailWord_100229 prefixEnd_100229 30498164456055459126851 := by
  unfold tailWord_100229
  simp only [CollatzResearch.WordTrace]
  refine ⟨3655651953894925595495741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2437101302596617063663827 3655651953894925595495741)
  ·
    refine ⟨1370869482710597098310903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3655651953894925595495741 1370869482710597098310903)
    ·
      refine ⟨2056304224065895647466355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1370869482710597098310903 2056304224065895647466355)
      ·
        refine ⟨3084456336098843471199533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2056304224065895647466355 3084456336098843471199533)
        ·
          refine ⟨1156671126037066301699825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3084456336098843471199533 1156671126037066301699825)
          ·
            refine ⟨867503344527799726274869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1156671126037066301699825 867503344527799726274869)
            ·
              refine ⟨81328438549481224338269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 867503344527799726274869 81328438549481224338269)
              ·
                refine ⟨30498164456055459126851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81328438549481224338269 30498164456055459126851)
                ·
                  rfl

theorem cell19_100229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 5, 3].length) (baseStart_100229 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_100229 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_100229 prefixEnd_100229 := by exact prefixLift 100229
  have htrace : WordTrace (prefixWord ++ tailWord_100229) baseStart_100229 baseEnd_100229 := by
    simpa [prefixWord, tailWord_100229, baseEnd_100229] using wordTrace_append hprefix tailTrace_100229
  have hstable : (prefixWord ++ tailWord_100229).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100229).length < 2 ^ (prefixWord ++ tailWord_100229).sum := by decide
  have hdescent : baseEnd_100229 < baseStart_100229 := by decide
  rcases family_descends (prefixWord ++ tailWord_100229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100284 : List Nat := [2, 2, 2, 5, 1, 1, 1, 5]
def baseStart_100284 : Nat := 118140960795 + 100284 * 2 ^ 59
def prefixEnd_100284 : Nat := 4983230072969 + 3 ^ 40 * 100284 * 2
def baseEnd_100284 : Nat := 30514900121831627904479

theorem tailTrace_100284 : CollatzResearch.WordTrace tailWord_100284 prefixEnd_100284 30514900121831627904479 := by
  unfold tailWord_100284
  simp only [CollatzResearch.WordTrace]
  refine ⟨1828828984347834994373953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2438438645797113325831937 1828828984347834994373953)
  ·
    refine ⟨1371621738260876245780465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1828828984347834994373953 1371621738260876245780465)
    ·
      refine ⟨1028716303695657184335349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1371621738260876245780465 1028716303695657184335349)
      ·
        refine ⟨96442153471467861031439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1028716303695657184335349 96442153471467861031439)
        ·
          refine ⟨144663230207201791547159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96442153471467861031439 144663230207201791547159)
          ·
            refine ⟨216994845310802687320739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144663230207201791547159 216994845310802687320739)
            ·
              refine ⟨325492267966204030981109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 216994845310802687320739 325492267966204030981109)
              ·
                refine ⟨30514900121831627904479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 325492267966204030981109 30514900121831627904479)
                ·
                  rfl

theorem cell19_100284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 5].length) (baseStart_100284 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_100284 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_100284 prefixEnd_100284 := by exact prefixLift 100284
  have htrace : WordTrace (prefixWord ++ tailWord_100284) baseStart_100284 baseEnd_100284 := by
    simpa [prefixWord, tailWord_100284, baseEnd_100284] using wordTrace_append hprefix tailTrace_100284
  have hstable : (prefixWord ++ tailWord_100284).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100284).length < 2 ^ (prefixWord ++ tailWord_100284).sum := by decide
  have hdescent : baseEnd_100284 < baseStart_100284 := by decide
  rcases family_descends (prefixWord ++ tailWord_100284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100286 : List Nat := [4, 2, 1, 1, 1, 4, 1, 5]
def baseStart_100286 : Nat := 118140960795 + 100286 * 2 ^ 59
def prefixEnd_100286 : Nat := 4983230072969 + 3 ^ 40 * 100286 * 2
def baseEnd_100286 : Nat := 30515508691496215860029

theorem tailTrace_100286 : CollatzResearch.WordTrace tailWord_100286 prefixEnd_100286 30515508691496215860029 := by
  unfold tailWord_100286
  simp only [CollatzResearch.WordTrace]
  refine ⟨457216364336053041290089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2438487276458949553547141 457216364336053041290089)
  ·
    refine ⟨342912273252039780967567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 457216364336053041290089 342912273252039780967567)
    ·
      refine ⟨514368409878059671451351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 342912273252039780967567 514368409878059671451351)
      ·
        refine ⟨771552614817089507177027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 514368409878059671451351 771552614817089507177027)
        ·
          refine ⟨1157328922225634260765541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 771552614817089507177027 1157328922225634260765541)
          ·
            refine ⟨216999172917306423893539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1157328922225634260765541 216999172917306423893539)
            ·
              refine ⟨325498759375959635840309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 216999172917306423893539 325498759375959635840309)
              ·
                refine ⟨30515508691496215860029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 325498759375959635840309 30515508691496215860029)
                ·
                  rfl

theorem cell19_100286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 5].length) (baseStart_100286 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_100286 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_100286 prefixEnd_100286 := by exact prefixLift 100286
  have htrace : WordTrace (prefixWord ++ tailWord_100286) baseStart_100286 baseEnd_100286 := by
    simpa [prefixWord, tailWord_100286, baseEnd_100286] using wordTrace_append hprefix tailTrace_100286
  have hstable : (prefixWord ++ tailWord_100286).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100286).length < 2 ^ (prefixWord ++ tailWord_100286).sum := by decide
  have hdescent : baseEnd_100286 < baseStart_100286 := by decide
  rcases family_descends (prefixWord ++ tailWord_100286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100288 : List Nat := [2, 1, 1, 2, 3, 2, 3, 5]
def baseStart_100288 : Nat := 118140960795 + 100288 * 2 ^ 59
def prefixEnd_100288 : Nat := 4983230072969 + 3 ^ 40 * 100288 * 2
def baseEnd_100288 : Nat := 30516117261160803815579

theorem tailTrace_100288 : CollatzResearch.WordTrace tailWord_100288 prefixEnd_100288 30516117261160803815579 := by
  unfold tailWord_100288
  simp only [CollatzResearch.WordTrace]
  refine ⟨1828901930340589335946759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2438535907120785781262345 1828901930340589335946759)
  ·
    refine ⟨2743352895510884003920139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1828901930340589335946759 2743352895510884003920139)
    ·
      refine ⟨4115029343266326005880209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2743352895510884003920139 4115029343266326005880209)
      ·
        refine ⟨3086272007449744504410157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4115029343266326005880209 3086272007449744504410157)
        ·
          refine ⟨1157352002793654189153809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3086272007449744504410157 1157352002793654189153809)
          ·
            refine ⟨868014002095240641865357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1157352002793654189153809 868014002095240641865357)
            ·
              refine ⟨325505250785715240699509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 868014002095240641865357 325505250785715240699509)
              ·
                refine ⟨30516117261160803815579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 325505250785715240699509 30516117261160803815579)
                ·
                  rfl

theorem cell19_100288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 5].length) (baseStart_100288 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_100288 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_100288 prefixEnd_100288 := by exact prefixLift 100288
  have htrace : WordTrace (prefixWord ++ tailWord_100288) baseStart_100288 baseEnd_100288 := by
    simpa [prefixWord, tailWord_100288, baseEnd_100288] using wordTrace_append hprefix tailTrace_100288
  have hstable : (prefixWord ++ tailWord_100288).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100288).length < 2 ^ (prefixWord ++ tailWord_100288).sum := by decide
  have hdescent : baseEnd_100288 < baseStart_100288 := by decide
  rcases family_descends (prefixWord ++ tailWord_100288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100345 : List Nat := [1, 2, 1, 3, 1, 4, 2, 5]
def baseStart_100345 : Nat := 118140960795 + 100345 * 2 ^ 59
def prefixEnd_100345 : Nat := 4983230072969 + 3 ^ 40 * 100345 * 2
def baseEnd_100345 : Nat := 30533461496601560548757

theorem tailTrace_100345 : CollatzResearch.WordTrace tailWord_100345 prefixEnd_100345 30533461496601560548757 := by
  unfold tailWord_100345
  simp only [CollatzResearch.WordTrace]
  refine ⟨3659882821474677406718489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2439921880983118271145659 3659882821474677406718489)
  ·
    refine ⟨2744912116106008055038867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3659882821474677406718489 2744912116106008055038867)
    ·
      refine ⟨4117368174159012082558301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2744912116106008055038867 4117368174159012082558301)
      ·
        refine ⟨1544013065309629530959363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4117368174159012082558301 1544013065309629530959363)
        ·
          refine ⟨2316019597964444296439045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1544013065309629530959363 2316019597964444296439045)
          ·
            refine ⟨434253674618333305582321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2316019597964444296439045 434253674618333305582321)
            ·
              refine ⟨325690255963749979186741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 434253674618333305582321 325690255963749979186741)
              ·
                refine ⟨30533461496601560548757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 325690255963749979186741 30533461496601560548757)
                ·
                  rfl

theorem cell19_100345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 5].length) (baseStart_100345 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_100345 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_100345 prefixEnd_100345 := by exact prefixLift 100345
  have htrace : WordTrace (prefixWord ++ tailWord_100345) baseStart_100345 baseEnd_100345 := by
    simpa [prefixWord, tailWord_100345, baseEnd_100345] using wordTrace_append hprefix tailTrace_100345
  have hstable : (prefixWord ++ tailWord_100345).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100345).length < 2 ^ (prefixWord ++ tailWord_100345).sum := by decide
  have hdescent : baseEnd_100345 < baseStart_100345 := by decide
  rcases family_descends (prefixWord ++ tailWord_100345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100358 : List Nat := [6, 2, 1, 2, 8]
def baseStart_100358 : Nat := 118140960795 + 100358 * 2 ^ 59
def prefixEnd_100358 : Nat := 4983230072969 + 3 ^ 40 * 100358 * 2
def baseEnd_100358 : Nat := 1131015451830421565179

theorem tailTrace_100358 : CollatzResearch.WordTrace tailWord_100358 prefixEnd_100358 1131015451830421565179 := by
  unfold tailWord_100358
  simp only [CollatzResearch.WordTrace]
  refine ⟨114386155325861894591929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 2440237980285053751294485 114386155325861894591929)
  ·
    refine ⟨85789616494396420943947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114386155325861894591929 85789616494396420943947)
    ·
      refine ⟨128684424741594631415921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85789616494396420943947 128684424741594631415921)
      ·
        refine ⟨96513318556195973561941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128684424741594631415921 96513318556195973561941)
        ·
          refine ⟨1131015451830421565179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 96513318556195973561941 1131015451830421565179)
          ·
            rfl

theorem cell19_100358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 8].length) (baseStart_100358 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_100358 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_100358 prefixEnd_100358 := by exact prefixLift 100358
  have htrace : WordTrace (prefixWord ++ tailWord_100358) baseStart_100358 baseEnd_100358 := by
    simpa [prefixWord, tailWord_100358, baseEnd_100358] using wordTrace_append hprefix tailTrace_100358
  have hstable : (prefixWord ++ tailWord_100358).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100358).length < 2 ^ (prefixWord ++ tailWord_100358).sum := by decide
  have hdescent : baseEnd_100358 < baseStart_100358 := by decide
  rcases family_descends (prefixWord ++ tailWord_100358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100362 : List Nat := [3, 1, 2, 2, 5, 6]
def baseStart_100362 : Nat := 118140960795 + 100362 * 2 ^ 59
def prefixEnd_100362 : Nat := 4983230072969 + 3 ^ 40 * 100362 * 2
def baseEnd_100362 : Nat := 3393181593194506463437

theorem tailTrace_100362 : CollatzResearch.WordTrace tailWord_100362 prefixEnd_100362 3393181593194506463437 := by
  unfold tailWord_100362
  simp only [CollatzResearch.WordTrace]
  refine ⟨915125715603272327521835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2440335241608726206724893 915125715603272327521835)
  ·
    refine ⟨1372688573404908491282753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 915125715603272327521835 1372688573404908491282753)
    ·
      refine ⟨1029516430053681368462065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1372688573404908491282753 1029516430053681368462065)
      ·
        refine ⟨772137322540261026346549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1029516430053681368462065 772137322540261026346549)
        ·
          refine ⟨72387873988149471219989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 772137322540261026346549 72387873988149471219989)
          ·
            refine ⟨3393181593194506463437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 72387873988149471219989 3393181593194506463437)
            ·
              rfl

theorem cell19_100362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 6].length) (baseStart_100362 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_100362 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_100362 prefixEnd_100362 := by exact prefixLift 100362
  have htrace : WordTrace (prefixWord ++ tailWord_100362) baseStart_100362 baseEnd_100362 := by
    simpa [prefixWord, tailWord_100362, baseEnd_100362] using wordTrace_append hprefix tailTrace_100362
  have hstable : (prefixWord ++ tailWord_100362).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100362).length < 2 ^ (prefixWord ++ tailWord_100362).sum := by decide
  have hdescent : baseEnd_100362 < baseStart_100362 := by decide
  rcases family_descends (prefixWord ++ tailWord_100362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100381 : List Nat := [1, 4, 2, 2, 2, 1, 3, 4]
def baseStart_100381 : Nat := 118140960795 + 100381 * 2 ^ 59
def prefixEnd_100381 : Nat := 4983230072969 + 3 ^ 40 * 100381 * 2
def baseEnd_100381 : Nat := 30544415750564143748659

theorem tailTrace_100381 : CollatzResearch.WordTrace tailWord_100381 prefixEnd_100381 30544415750564143748659 := by
  unfold tailWord_100381
  simp only [CollatzResearch.WordTrace]
  refine ⟨3661195849344255555028997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2440797232896170370019331 3661195849344255555028997)
  ·
    refine ⟨686474221752047916567937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3661195849344255555028997 686474221752047916567937)
    ·
      refine ⟨514855666314035937425953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 686474221752047916567937 514855666314035937425953)
      ·
        refine ⟨386141749735526953069465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 514855666314035937425953 386141749735526953069465)
        ·
          refine ⟨289606312301645214802099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 386141749735526953069465 289606312301645214802099)
          ·
            refine ⟨434409468452467822203149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 289606312301645214802099 434409468452467822203149)
            ·
              refine ⟨162903550669675433326181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 434409468452467822203149 162903550669675433326181)
              ·
                refine ⟨30544415750564143748659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 162903550669675433326181 30544415750564143748659)
                ·
                  rfl

theorem cell19_100381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 3, 4].length) (baseStart_100381 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_100381 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_100381 prefixEnd_100381 := by exact prefixLift 100381
  have htrace : WordTrace (prefixWord ++ tailWord_100381) baseStart_100381 baseEnd_100381 := by
    simpa [prefixWord, tailWord_100381, baseEnd_100381] using wordTrace_append hprefix tailTrace_100381
  have hstable : (prefixWord ++ tailWord_100381).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100381).length < 2 ^ (prefixWord ++ tailWord_100381).sum := by decide
  have hdescent : baseEnd_100381 < baseStart_100381 := by decide
  rcases family_descends (prefixWord ++ tailWord_100381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100398 : List Nat := [4, 1, 3, 1, 1, 3, 3, 3]
def baseStart_100398 : Nat := 118140960795 + 100398 * 2 ^ 59
def prefixEnd_100398 : Nat := 4983230072969 + 3 ^ 40 * 100398 * 2
def baseEnd_100398 : Nat := 30549588592713141370835

theorem tailTrace_100398 : CollatzResearch.WordTrace tailWord_100398 prefixEnd_100398 30549588592713141370835 := by
  unfold tailWord_100398
  simp only [CollatzResearch.WordTrace]
  refine ⟨457726986285333432299731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2441210593521778305598565 457726986285333432299731)
  ·
    refine ⟨686590479428000148449597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 457726986285333432299731 686590479428000148449597)
    ·
      refine ⟨257471429785500055668599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 686590479428000148449597 257471429785500055668599)
      ·
        refine ⟨386207144678250083502899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 257471429785500055668599 386207144678250083502899)
        ·
          refine ⟨579310717017375125254349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 386207144678250083502899 579310717017375125254349)
          ·
            refine ⟨217241518881515671970381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 579310717017375125254349 217241518881515671970381)
            ·
              refine ⟨81465569580568376988893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 217241518881515671970381 81465569580568376988893)
              ·
                refine ⟨30549588592713141370835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81465569580568376988893 30549588592713141370835)
                ·
                  rfl

theorem cell19_100398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 3, 3].length) (baseStart_100398 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_100398 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_100398 prefixEnd_100398 := by exact prefixLift 100398
  have htrace : WordTrace (prefixWord ++ tailWord_100398) baseStart_100398 baseEnd_100398 := by
    simpa [prefixWord, tailWord_100398, baseEnd_100398] using wordTrace_append hprefix tailTrace_100398
  have hstable : (prefixWord ++ tailWord_100398).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100398).length < 2 ^ (prefixWord ++ tailWord_100398).sum := by decide
  have hdescent : baseEnd_100398 < baseStart_100398 := by decide
  rcases family_descends (prefixWord ++ tailWord_100398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100400 : List Nat := [2, 1, 1, 1, 2, 6, 3, 3]
def baseStart_100400 : Nat := 118140960795 + 100400 * 2 ^ 59
def prefixEnd_100400 : Nat := 4983230072969 + 3 ^ 40 * 100400 * 2
def baseEnd_100400 : Nat := 30550197162377729326385

theorem tailTrace_100400 : CollatzResearch.WordTrace tailWord_100400 prefixEnd_100400 30550197162377729326385 := by
  unfold tailWord_100400
  simp only [CollatzResearch.WordTrace]
  refine ⟨1830944418137710899985327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2441259224183614533313769 1830944418137710899985327)
  ·
    refine ⟨2746416627206566349977991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1830944418137710899985327 2746416627206566349977991)
    ·
      refine ⟨4119624940809849524966987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2746416627206566349977991 4119624940809849524966987)
      ·
        refine ⟨6179437411214774287450481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4119624940809849524966987 6179437411214774287450481)
        ·
          refine ⟨4634578058411080715587861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6179437411214774287450481 4634578058411080715587861)
          ·
            refine ⟨217245846488019408543181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 4634578058411080715587861 217245846488019408543181)
            ·
              refine ⟨81467192433007278203693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 217245846488019408543181 81467192433007278203693)
              ·
                refine ⟨30550197162377729326385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81467192433007278203693 30550197162377729326385)
                ·
                  rfl

theorem cell19_100400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 3, 3].length) (baseStart_100400 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_100400 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_100400 prefixEnd_100400 := by exact prefixLift 100400
  have htrace : WordTrace (prefixWord ++ tailWord_100400) baseStart_100400 baseEnd_100400 := by
    simpa [prefixWord, tailWord_100400, baseEnd_100400] using wordTrace_append hprefix tailTrace_100400
  have hstable : (prefixWord ++ tailWord_100400).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100400).length < 2 ^ (prefixWord ++ tailWord_100400).sum := by decide
  have hdescent : baseEnd_100400 < baseStart_100400 := by decide
  rcases family_descends (prefixWord ++ tailWord_100400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100514 : List Nat := [3, 3, 1, 3, 1, 1, 2, 5]
def baseStart_100514 : Nat := 118140960795 + 100514 * 2 ^ 59
def prefixEnd_100514 : Nat := 4983230072969 + 3 ^ 40 * 100514 * 2
def baseEnd_100514 : Nat := 30584885633259242792741

theorem tailTrace_100514 : CollatzResearch.WordTrace tailWord_100514 prefixEnd_100514 30584885633259242792741 := by
  unfold tailWord_100514
  simp only [CollatzResearch.WordTrace]
  refine ⟨916511689465604817405149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2444031171908279513080397 916511689465604817405149)
  ·
    refine ⟨343691883549601806526931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 916511689465604817405149 343691883549601806526931)
    ·
      refine ⟨515537825324402709790397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 343691883549601806526931 515537825324402709790397)
      ·
        refine ⟨193326684496651016171399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 515537825324402709790397 193326684496651016171399)
        ·
          refine ⟨289990026744976524257099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193326684496651016171399 289990026744976524257099)
          ·
            refine ⟨434985040117464786385649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 289990026744976524257099 434985040117464786385649)
            ·
              refine ⟨326238780088098589789237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 434985040117464786385649 326238780088098589789237)
              ·
                refine ⟨30584885633259242792741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 326238780088098589789237 30584885633259242792741)
                ·
                  rfl

theorem cell19_100514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 5].length) (baseStart_100514 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_100514 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_100514 prefixEnd_100514 := by exact prefixLift 100514
  have htrace : WordTrace (prefixWord ++ tailWord_100514) baseStart_100514 baseEnd_100514 := by
    simpa [prefixWord, tailWord_100514, baseEnd_100514] using wordTrace_append hprefix tailTrace_100514
  have hstable : (prefixWord ++ tailWord_100514).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100514).length < 2 ^ (prefixWord ++ tailWord_100514).sum := by decide
  have hdescent : baseEnd_100514 < baseStart_100514 := by decide
  rcases family_descends (prefixWord ++ tailWord_100514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100533 : List Nat := [1, 3, 3, 4, 1, 7]
def baseStart_100533 : Nat := 118140960795 + 100533 * 2 ^ 59
def prefixEnd_100533 : Nat := 4983230072969 + 3 ^ 40 * 100533 * 2
def baseEnd_100533 : Nat := 3398963005008092041163

theorem tailTrace_100533 : CollatzResearch.WordTrace tailWord_100533 prefixEnd_100533 3398963005008092041163 := by
  unfold tailWord_100533
  simp only [CollatzResearch.WordTrace]
  refine ⟨3666739744793585514562253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2444493163195723676374835 3666739744793585514562253)
  ·
    refine ⟨1375027404297594567960845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3666739744793585514562253 1375027404297594567960845)
    ·
      refine ⟨515635276611597962985317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1375027404297594567960845 515635276611597962985317)
      ·
        refine ⟨96681614364674618059747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 515635276611597962985317 96681614364674618059747)
        ·
          refine ⟨145022421547011927089621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96681614364674618059747 145022421547011927089621)
          ·
            refine ⟨3398963005008092041163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 145022421547011927089621 3398963005008092041163)
            ·
              rfl

theorem cell19_100533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 7].length) (baseStart_100533 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_100533 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_100533 prefixEnd_100533 := by exact prefixLift 100533
  have htrace : WordTrace (prefixWord ++ tailWord_100533) baseStart_100533 baseEnd_100533 := by
    simpa [prefixWord, tailWord_100533, baseEnd_100533] using wordTrace_append hprefix tailTrace_100533
  have hstable : (prefixWord ++ tailWord_100533).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100533).length < 2 ^ (prefixWord ++ tailWord_100533).sum := by decide
  have hdescent : baseEnd_100533 < baseStart_100533 := by decide
  rcases family_descends (prefixWord ++ tailWord_100533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100668 : List Nat := [2, 2, 2, 2, 1, 2, 4, 4]
def baseStart_100668 : Nat := 118140960795 + 100668 * 2 ^ 59
def prefixEnd_100668 : Nat := 4983230072969 + 3 ^ 40 * 100668 * 2
def baseEnd_100668 : Nat := 30631745497432515370099

theorem tailTrace_100668 : CollatzResearch.WordTrace tailWord_100668 prefixEnd_100668 30631745497432515370099 := by
  unfold tailWord_100668
  simp only [CollatzResearch.WordTrace]
  refine ⟨1835831799652251785363329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2447775732869669047151105 1835831799652251785363329)
  ·
    refine ⟨1376873849739188839022497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1835831799652251785363329 1376873849739188839022497)
    ·
      refine ⟨1032655387304391629266873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1376873849739188839022497 1032655387304391629266873)
      ·
        refine ⟨774491540478293721950155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1032655387304391629266873 774491540478293721950155)
        ·
          refine ⟨1161737310717440582925233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 774491540478293721950155 1161737310717440582925233)
          ·
            refine ⟨871302983038080437193925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1161737310717440582925233 871302983038080437193925)
            ·
              refine ⟨163369309319640081973861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 871302983038080437193925 163369309319640081973861)
              ·
                refine ⟨30631745497432515370099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 163369309319640081973861 30631745497432515370099)
                ·
                  rfl

theorem cell19_100668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 4, 4].length) (baseStart_100668 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_100668 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_100668 prefixEnd_100668 := by exact prefixLift 100668
  have htrace : WordTrace (prefixWord ++ tailWord_100668) baseStart_100668 baseEnd_100668 := by
    simpa [prefixWord, tailWord_100668, baseEnd_100668] using wordTrace_append hprefix tailTrace_100668
  have hstable : (prefixWord ++ tailWord_100668).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100668).length < 2 ^ (prefixWord ++ tailWord_100668).sum := by decide
  have hdescent : baseEnd_100668 < baseStart_100668 := by decide
  rcases family_descends (prefixWord ++ tailWord_100668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100706 : List Nat := [3, 3, 2, 1, 1, 9]
def baseStart_100706 : Nat := 118140960795 + 100706 * 2 ^ 59
def prefixEnd_100706 : Nat := 4983230072969 + 3 ^ 40 * 100706 * 2
def baseEnd_100706 : Nat := 3404812035673298502839

theorem tailTrace_100706 : CollatzResearch.WordTrace tailWord_100706 prefixEnd_100706 3404812035673298502839 := by
  unfold tailWord_100706
  simp only [CollatzResearch.WordTrace]
  refine ⟨918262393291709015152493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2448699715444557373739981 918262393291709015152493)
  ·
    refine ⟨344348397484390880682185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 918262393291709015152493 344348397484390880682185)
    ·
      refine ⟨258261298113293160511639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 344348397484390880682185 258261298113293160511639)
      ·
        refine ⟨387391947169939740767459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258261298113293160511639 387391947169939740767459)
        ·
          refine ⟨581087920754909611151189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 387391947169939740767459 581087920754909611151189)
          ·
            refine ⟨3404812035673298502839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 581087920754909611151189 3404812035673298502839)
            ·
              rfl

theorem cell19_100706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 9].length) (baseStart_100706 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_100706 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_100706 prefixEnd_100706 := by exact prefixLift 100706
  have htrace : WordTrace (prefixWord ++ tailWord_100706) baseStart_100706 baseEnd_100706 := by
    simpa [prefixWord, tailWord_100706, baseEnd_100706] using wordTrace_append hprefix tailTrace_100706
  have hstable : (prefixWord ++ tailWord_100706).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100706).length < 2 ^ (prefixWord ++ tailWord_100706).sum := by decide
  have hdescent : baseEnd_100706 < baseStart_100706 := by decide
  rcases family_descends (prefixWord ++ tailWord_100706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100727 : List Nat := [1, 1, 3, 1, 1, 2, 2, 8]
def baseStart_100727 : Nat := 118140960795 + 100727 * 2 ^ 59
def prefixEnd_100727 : Nat := 4983230072969 + 3 ^ 40 * 100727 * 2
def baseEnd_100727 : Nat := 30649698302537860058827

theorem tailTrace_100727 : CollatzResearch.WordTrace tailWord_100727 prefixEnd_100727 30649698302537860058827 := by
  unfold tailWord_100727
  simp only [CollatzResearch.WordTrace]
  refine ⟨3673815506090756647124435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2449210337393837764749623 3673815506090756647124435)
  ·
    refine ⟨5510723259136134970686653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3673815506090756647124435 5510723259136134970686653)
    ·
      refine ⟨2066521222176050614007495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5510723259136134970686653 2066521222176050614007495)
      ·
        refine ⟨3099781833264075921011243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2066521222176050614007495 3099781833264075921011243)
        ·
          refine ⟨4649672749896113881516865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3099781833264075921011243 4649672749896113881516865)
          ·
            refine ⟨3487254562422085411137649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4649672749896113881516865 3487254562422085411137649)
            ·
              refine ⟨2615440921816564058353237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3487254562422085411137649 2615440921816564058353237)
              ·
                refine ⟨30649698302537860058827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2615440921816564058353237 30649698302537860058827)
                ·
                  rfl

theorem cell19_100727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 8].length) (baseStart_100727 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_100727 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_100727 prefixEnd_100727 := by exact prefixLift 100727
  have htrace : WordTrace (prefixWord ++ tailWord_100727) baseStart_100727 baseEnd_100727 := by
    simpa [prefixWord, tailWord_100727, baseEnd_100727] using wordTrace_append hprefix tailTrace_100727
  have hstable : (prefixWord ++ tailWord_100727).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100727).length < 2 ^ (prefixWord ++ tailWord_100727).sum := by decide
  have hdescent : baseEnd_100727 < baseStart_100727 := by decide
  rcases family_descends (prefixWord ++ tailWord_100727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100738 : List Nat := [3, 4, 2, 1, 2, 1, 3, 3]
def baseStart_100738 : Nat := 118140960795 + 100738 * 2 ^ 59
def prefixEnd_100738 : Nat := 4983230072969 + 3 ^ 40 * 100738 * 2
def baseEnd_100738 : Nat := 30653045435693093814353

theorem tailTrace_100738 : CollatzResearch.WordTrace tailWord_100738 prefixEnd_100738 30653045435693093814353 := by
  unfold tailWord_100738
  simp only [CollatzResearch.WordTrace]
  refine ⟨918554177262726381443717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2449477806033937017183245 918554177262726381443717)
  ·
    refine ⟨172228908236761196520697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 918554177262726381443717 172228908236761196520697)
    ·
      refine ⟨129171681177570897390523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172228908236761196520697 129171681177570897390523)
      ·
        refine ⟨193757521766356346085785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129171681177570897390523 193757521766356346085785)
        ·
          refine ⟨145318141324767259564339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 193757521766356346085785 145318141324767259564339)
          ·
            refine ⟨217977211987150889346509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145318141324767259564339 217977211987150889346509)
            ·
              refine ⟨81741454495181583504941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 217977211987150889346509 81741454495181583504941)
              ·
                refine ⟨30653045435693093814353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81741454495181583504941 30653045435693093814353)
                ·
                  rfl

theorem cell19_100738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 3, 3].length) (baseStart_100738 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_100738 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_100738 prefixEnd_100738 := by exact prefixLift 100738
  have htrace : WordTrace (prefixWord ++ tailWord_100738) baseStart_100738 baseEnd_100738 := by
    simpa [prefixWord, tailWord_100738, baseEnd_100738] using wordTrace_append hprefix tailTrace_100738
  have hstable : (prefixWord ++ tailWord_100738).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100738).length < 2 ^ (prefixWord ++ tailWord_100738).sum := by decide
  have hdescent : baseEnd_100738 < baseStart_100738 := by decide
  rcases family_descends (prefixWord ++ tailWord_100738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100820 : List Nat := [2, 4, 1, 2, 2, 1, 7]
def baseStart_100820 : Nat := 118140960795 + 100820 * 2 ^ 59
def prefixEnd_100820 : Nat := 4983230072969 + 3 ^ 40 * 100820 * 2
def baseEnd_100820 : Nat := 10225998930647066663969

theorem tailTrace_100820 : CollatzResearch.WordTrace tailWord_100820 prefixEnd_100820 10225998930647066663969 := by
  unfold tailWord_100820
  simp only [CollatzResearch.WordTrace]
  refine ⟨1838603747376916765129957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2451471663169222353506609 1838603747376916765129957)
  ·
    refine ⟨344738202633171893461867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1838603747376916765129957 344738202633171893461867)
    ·
      refine ⟨517107303949757840192801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 344738202633171893461867 517107303949757840192801)
      ·
        refine ⟨387830477962318380144601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 517107303949757840192801 387830477962318380144601)
        ·
          refine ⟨290872858471738785108451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 387830477962318380144601 290872858471738785108451)
          ·
            refine ⟨436309287707608177662677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 290872858471738785108451 436309287707608177662677)
            ·
              refine ⟨10225998930647066663969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 436309287707608177662677 10225998930647066663969)
              ·
                rfl

theorem cell19_100820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 7].length) (baseStart_100820 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_100820 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_100820 prefixEnd_100820 := by exact prefixLift 100820
  have htrace : WordTrace (prefixWord ++ tailWord_100820) baseStart_100820 baseEnd_100820 := by
    simpa [prefixWord, tailWord_100820, baseEnd_100820] using wordTrace_append hprefix tailTrace_100820
  have hstable : (prefixWord ++ tailWord_100820).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100820).length < 2 ^ (prefixWord ++ tailWord_100820).sum := by decide
  have hdescent : baseEnd_100820 < baseStart_100820 := by decide
  rcases family_descends (prefixWord ++ tailWord_100820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100837 : List Nat := [1, 3, 1, 5, 2, 1, 2, 4]
def baseStart_100837 : Nat := 118140960795 + 100837 * 2 ^ 59
def prefixEnd_100837 : Nat := 4983230072969 + 3 ^ 40 * 100837 * 2
def baseEnd_100837 : Nat := 30683169634090197614083

theorem tailTrace_100837 : CollatzResearch.WordTrace tailWord_100837 prefixEnd_100837 30683169634090197614083 := by
  unfold tailWord_100837
  simp only [CollatzResearch.WordTrace]
  refine ⟨3677827535692245433628765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2451885023794830289085843 3677827535692245433628765)
  ·
    refine ⟨1379185325884592037610787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3677827535692245433628765 1379185325884592037610787)
    ·
      refine ⟨2068777988826888056416181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1379185325884592037610787 2068777988826888056416181)
      ·
        refine ⟨193947936452520755289017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2068777988826888056416181 193947936452520755289017)
        ·
          refine ⟨145460952339390566466763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 193947936452520755289017 145460952339390566466763)
          ·
            refine ⟨218191428509085849700145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145460952339390566466763 218191428509085849700145)
            ·
              refine ⟨163643571381814387275109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 218191428509085849700145 163643571381814387275109)
              ·
                refine ⟨30683169634090197614083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 163643571381814387275109 30683169634090197614083)
                ·
                  rfl

theorem cell19_100837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 2, 4].length) (baseStart_100837 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_100837 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_100837 prefixEnd_100837 := by exact prefixLift 100837
  have htrace : WordTrace (prefixWord ++ tailWord_100837) baseStart_100837 baseEnd_100837 := by
    simpa [prefixWord, tailWord_100837, baseEnd_100837] using wordTrace_append hprefix tailTrace_100837
  have hstable : (prefixWord ++ tailWord_100837).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100837).length < 2 ^ (prefixWord ++ tailWord_100837).sum := by decide
  have hdescent : baseEnd_100837 < baseStart_100837 := by decide
  rcases family_descends (prefixWord ++ tailWord_100837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100839 : List Nat := [1, 1, 5, 2, 1, 1, 4, 4]
def baseStart_100839 : Nat := 118140960795 + 100839 * 2 ^ 59
def prefixEnd_100839 : Nat := 4983230072969 + 3 ^ 40 * 100839 * 2
def baseEnd_100839 : Nat := 30683778203754785569633

theorem tailTrace_100839 : CollatzResearch.WordTrace tailWord_100839 prefixEnd_100839 30683778203754785569633 := by
  unfold tailWord_100839
  simp only [CollatzResearch.WordTrace]
  refine ⟨3677900481684999775201571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2451933654456666516801047 3677900481684999775201571)
  ·
    refine ⟨5516850722527499662802357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3677900481684999775201571 5516850722527499662802357)
    ·
      refine ⟨517204755236953093387721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5516850722527499662802357 517204755236953093387721)
      ·
        refine ⟨387903566427714820040791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 517204755236953093387721 387903566427714820040791)
        ·
          refine ⟨581855349641572230061187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 387903566427714820040791 581855349641572230061187)
          ·
            refine ⟨872783024462358345091781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 581855349641572230061187 872783024462358345091781)
            ·
              refine ⟨163646817086692189704709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 872783024462358345091781 163646817086692189704709)
              ·
                refine ⟨30683778203754785569633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 163646817086692189704709 30683778203754785569633)
                ·
                  rfl

theorem cell19_100839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 4, 4].length) (baseStart_100839 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_100839 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_100839 prefixEnd_100839 := by exact prefixLift 100839
  have htrace : WordTrace (prefixWord ++ tailWord_100839) baseStart_100839 baseEnd_100839 := by
    simpa [prefixWord, tailWord_100839, baseEnd_100839] using wordTrace_append hprefix tailTrace_100839
  have hstable : (prefixWord ++ tailWord_100839).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100839).length < 2 ^ (prefixWord ++ tailWord_100839).sum := by decide
  have hdescent : baseEnd_100839 < baseStart_100839 := by decide
  rcases family_descends (prefixWord ++ tailWord_100839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100915 : List Nat := [1, 1, 1, 2, 4, 2, 5, 3]
def baseStart_100915 : Nat := 118140960795 + 100915 * 2 ^ 59
def prefixEnd_100915 : Nat := 4983230072969 + 3 ^ 40 * 100915 * 2
def baseEnd_100915 : Nat := 30706903851009127880537

theorem tailTrace_100915 : CollatzResearch.WordTrace tailWord_100915 prefixEnd_100915 30706903851009127880537 := by
  unfold tailWord_100915
  simp only [CollatzResearch.WordTrace]
  refine ⟨3680672429409664754968199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2453781619606443169978799 3680672429409664754968199)
  ·
    refine ⟨5521008644114497132452299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3680672429409664754968199 5521008644114497132452299)
    ·
      refine ⟨8281512966171745698678449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5521008644114497132452299 8281512966171745698678449)
      ·
        refine ⟨6211134724628809274008837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8281512966171745698678449 6211134724628809274008837)
        ·
          refine ⟨1164587760867901738876657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6211134724628809274008837 1164587760867901738876657)
          ·
            refine ⟨873440820650926304157493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1164587760867901738876657 873440820650926304157493)
            ·
              refine ⟨81885076936024341014765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 873440820650926304157493 81885076936024341014765)
              ·
                refine ⟨30706903851009127880537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81885076936024341014765 30706903851009127880537)
                ·
                  rfl

theorem cell19_100915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 5, 3].length) (baseStart_100915 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_100915 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_100915 prefixEnd_100915 := by exact prefixLift 100915
  have htrace : WordTrace (prefixWord ++ tailWord_100915) baseStart_100915 baseEnd_100915 := by
    simpa [prefixWord, tailWord_100915, baseEnd_100915] using wordTrace_append hprefix tailTrace_100915
  have hstable : (prefixWord ++ tailWord_100915).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100915).length < 2 ^ (prefixWord ++ tailWord_100915).sum := by decide
  have hdescent : baseEnd_100915 < baseStart_100915 := by decide
  rcases family_descends (prefixWord ++ tailWord_100915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100968 : List Nat := [2, 1, 4, 3, 2, 2, 2, 3]
def baseStart_100968 : Nat := 118140960795 + 100968 * 2 ^ 59
def prefixEnd_100968 : Nat := 4983230072969 + 3 ^ 40 * 100968 * 2
def baseEnd_100968 : Nat := 30723030947120708702615

theorem tailTrace_100968 : CollatzResearch.WordTrace tailWord_100968 prefixEnd_100968 30723030947120708702615 := by
  unfold tailWord_100968
  simp only [CollatzResearch.WordTrace]
  refine ⟨1841302749108827403323779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2455070332145103204431705 1841302749108827403323779)
  ·
    refine ⟨2761954123663241104985669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1841302749108827403323779 2761954123663241104985669)
    ·
      refine ⟨517866398186857707184813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2761954123663241104985669 517866398186857707184813)
      ·
        refine ⟨194199899320071640194305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 517866398186857707184813 194199899320071640194305)
        ·
          refine ⟨145649924490053730145729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 194199899320071640194305 145649924490053730145729)
          ·
            refine ⟨109237443367540297609297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 145649924490053730145729 109237443367540297609297)
            ·
              refine ⟨81928082525655223206973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109237443367540297609297 81928082525655223206973)
              ·
                refine ⟨30723030947120708702615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81928082525655223206973 30723030947120708702615)
                ·
                  rfl

theorem cell19_100968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 2, 3].length) (baseStart_100968 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_100968 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_100968 prefixEnd_100968 := by exact prefixLift 100968
  have htrace : WordTrace (prefixWord ++ tailWord_100968) baseStart_100968 baseEnd_100968 := by
    simpa [prefixWord, tailWord_100968, baseEnd_100968] using wordTrace_append hprefix tailTrace_100968
  have hstable : (prefixWord ++ tailWord_100968).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100968).length < 2 ^ (prefixWord ++ tailWord_100968).sum := by decide
  have hdescent : baseEnd_100968 < baseStart_100968 := by decide
  rcases family_descends (prefixWord ++ tailWord_100968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100972 : List Nat := [2, 2, 1, 1, 3, 1, 6, 3]
def baseStart_100972 : Nat := 118140960795 + 100972 * 2 ^ 59
def prefixEnd_100972 : Nat := 4983230072969 + 3 ^ 40 * 100972 * 2
def baseEnd_100972 : Nat := 30724248086449884613715

theorem tailTrace_100972 : CollatzResearch.WordTrace tailWord_100972 prefixEnd_100972 30724248086449884613715 := by
  unfold tailWord_100972
  simp only [CollatzResearch.WordTrace]
  refine ⟨1841375695101581744896585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2455167593468775659862113 1841375695101581744896585)
  ·
    refine ⟨1381031771326186308672439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1841375695101581744896585 1381031771326186308672439)
    ·
      refine ⟨2071547656989279463008659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1381031771326186308672439 2071547656989279463008659)
      ·
        refine ⟨3107321485483919194512989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2071547656989279463008659 3107321485483919194512989)
        ·
          refine ⟨1165245557056469697942371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3107321485483919194512989 1165245557056469697942371)
          ·
            refine ⟨1747868335584704546913557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1165245557056469697942371 1747868335584704546913557)
            ·
              refine ⟨81931328230533025636573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1747868335584704546913557 81931328230533025636573)
              ·
                refine ⟨30724248086449884613715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81931328230533025636573 30724248086449884613715)
                ·
                  rfl

theorem cell19_100972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 6, 3].length) (baseStart_100972 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_100972 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_100972 prefixEnd_100972 := by exact prefixLift 100972
  have htrace : WordTrace (prefixWord ++ tailWord_100972) baseStart_100972 baseEnd_100972 := by
    simpa [prefixWord, tailWord_100972, baseEnd_100972] using wordTrace_append hprefix tailTrace_100972
  have hstable : (prefixWord ++ tailWord_100972).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100972).length < 2 ^ (prefixWord ++ tailWord_100972).sum := by decide
  have hdescent : baseEnd_100972 < baseStart_100972 := by decide
  rcases family_descends (prefixWord ++ tailWord_100972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100989 : List Nat := [1, 4, 1, 1, 6, 1, 5]
def baseStart_100989 : Nat := 118140960795 + 100989 * 2 ^ 59
def prefixEnd_100989 : Nat := 4983230072969 + 3 ^ 40 * 100989 * 2
def baseEnd_100989 : Nat := 10243140309532960745297

theorem tailTrace_100989 : CollatzResearch.WordTrace tailWord_100989 prefixEnd_100989 10243140309532960745297 := by
  unfold tailWord_100989
  simp only [CollatzResearch.WordTrace]
  refine ⟨3683371431141575393162021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2455580954094383595441347 3683371431141575393162021)
  ·
    refine ⟨690632143339045386217879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3683371431141575393162021 690632143339045386217879)
    ·
      refine ⟨1035948215008568079326819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 690632143339045386217879 1035948215008568079326819)
      ·
        refine ⟨1553922322512852118990229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1035948215008568079326819 1553922322512852118990229)
        ·
          refine ⟨72840108867789943077667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 1553922322512852118990229 72840108867789943077667)
          ·
            refine ⟨109260163301684914616501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72840108867789943077667 109260163301684914616501)
            ·
              refine ⟨10243140309532960745297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 109260163301684914616501 10243140309532960745297)
              ·
                rfl

theorem cell19_100989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 5].length) (baseStart_100989 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_100989 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_100989 prefixEnd_100989 := by exact prefixLift 100989
  have htrace : WordTrace (prefixWord ++ tailWord_100989) baseStart_100989 baseEnd_100989 := by
    simpa [prefixWord, tailWord_100989, baseEnd_100989] using wordTrace_append hprefix tailTrace_100989
  have hstable : (prefixWord ++ tailWord_100989).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100989).length < 2 ^ (prefixWord ++ tailWord_100989).sum := by decide
  have hdescent : baseEnd_100989 < baseStart_100989 := by decide
  rcases family_descends (prefixWord ++ tailWord_100989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101010 : List Nat := [3, 2, 3, 1, 2, 1, 1, 6]
def baseStart_101010 : Nat := 118140960795 + 101010 * 2 ^ 59
def prefixEnd_101010 : Nat := 4983230072969 + 3 ^ 40 * 101010 * 2
def baseEnd_101010 : Nat := 30735810910077055769167

theorem tailTrace_101010 : CollatzResearch.WordTrace tailWord_101010 prefixEnd_101010 30735810910077055769167 := by
  unfold tailWord_101010
  simp only [CollatzResearch.WordTrace]
  refine ⟨921034341016373994919121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2456091576043663986450989 921034341016373994919121)
  ·
    refine ⟨690775755762280496189341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 921034341016373994919121 690775755762280496189341)
    ·
      refine ⟨259040908410855186071003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 690775755762280496189341 259040908410855186071003)
      ·
        refine ⟨388561362616282779106505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259040908410855186071003 388561362616282779106505)
        ·
          refine ⟨291421021962212084329879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 388561362616282779106505 291421021962212084329879)
          ·
            refine ⟨437131532943318126494819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 291421021962212084329879 437131532943318126494819)
            ·
              refine ⟨655697299414977189742229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 437131532943318126494819 655697299414977189742229)
              ·
                refine ⟨30735810910077055769167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 655697299414977189742229 30735810910077055769167)
                ·
                  rfl

theorem cell19_101010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 6].length) (baseStart_101010 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_101010 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_101010 prefixEnd_101010 := by exact prefixLift 101010
  have htrace : WordTrace (prefixWord ++ tailWord_101010) baseStart_101010 baseEnd_101010 := by
    simpa [prefixWord, tailWord_101010, baseEnd_101010] using wordTrace_append hprefix tailTrace_101010
  have hstable : (prefixWord ++ tailWord_101010).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101010).length < 2 ^ (prefixWord ++ tailWord_101010).sum := by decide
  have hdescent : baseEnd_101010 < baseStart_101010 := by decide
  rcases family_descends (prefixWord ++ tailWord_101010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101046 : List Nat := [5, 1, 3, 1, 2, 7]
def baseStart_101046 : Nat := 118140960795 + 101046 * 2 ^ 59
def prefixEnd_101046 : Nat := 4983230072969 + 3 ^ 40 * 101046 * 2
def baseEnd_101046 : Nat := 3416307240448848774341

theorem tailTrace_101046 : CollatzResearch.WordTrace tailWord_101046 prefixEnd_101046 3416307240448848774341 := by
  unfold tailWord_101046
  simp only [CollatzResearch.WordTrace]
  refine ⟨230340649495942132999187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2456966927956716085324661 230340649495942132999187)
  ·
    refine ⟨345510974243913199498781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230340649495942132999187 345510974243913199498781)
    ·
      refine ⟨129566615341467449812043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 345510974243913199498781 129566615341467449812043)
      ·
        refine ⟨194349923012201174718065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129566615341467449812043 194349923012201174718065)
        ·
          refine ⟨145762442259150881038549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 194349923012201174718065 145762442259150881038549)
          ·
            refine ⟨3416307240448848774341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 145762442259150881038549 3416307240448848774341)
            ·
              rfl

theorem cell19_101046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 7].length) (baseStart_101046 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_101046 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_101046 prefixEnd_101046 := by exact prefixLift 101046
  have htrace : WordTrace (prefixWord ++ tailWord_101046) baseStart_101046 baseEnd_101046 := by
    simpa [prefixWord, tailWord_101046, baseEnd_101046] using wordTrace_append hprefix tailTrace_101046
  have hstable : (prefixWord ++ tailWord_101046).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101046).length < 2 ^ (prefixWord ++ tailWord_101046).sum := by decide
  have hdescent : baseEnd_101046 < baseStart_101046 := by decide
  rcases family_descends (prefixWord ++ tailWord_101046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101143 : List Nat := [1, 1, 3, 4, 3, 1, 1, 5]
def baseStart_101143 : Nat := 118140960795 + 101143 * 2 ^ 59
def prefixEnd_101143 : Nat := 4983230072969 + 3 ^ 40 * 101143 * 2
def baseEnd_101143 : Nat := 30776280792772154813249

theorem tailTrace_101143 : CollatzResearch.WordTrace tailWord_101143 prefixEnd_101143 30776280792772154813249 := by
  unfold tailWord_101143
  simp only [CollatzResearch.WordTrace]
  refine ⟨3688988272583659694268083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2459325515055773129512055 3688988272583659694268083)
  ·
    refine ⟨5533482408875489541402125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3688988272583659694268083 5533482408875489541402125)
    ·
      refine ⟨2075055903328308578025797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5533482408875489541402125 2075055903328308578025797)
      ·
        refine ⟨389072981874057858379837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2075055903328308578025797 389072981874057858379837)
        ·
          refine ⟨145902368202771696892439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 389072981874057858379837 145902368202771696892439)
          ·
            refine ⟨218853552304157545338659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145902368202771696892439 218853552304157545338659)
            ·
              refine ⟨328280328456236318007989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 218853552304157545338659 328280328456236318007989)
              ·
                refine ⟨30776280792772154813249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 328280328456236318007989 30776280792772154813249)
                ·
                  rfl

theorem cell19_101143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 5].length) (baseStart_101143 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_101143 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_101143 prefixEnd_101143 := by exact prefixLift 101143
  have htrace : WordTrace (prefixWord ++ tailWord_101143) baseStart_101143 baseEnd_101143 := by
    simpa [prefixWord, tailWord_101143, baseEnd_101143] using wordTrace_append hprefix tailTrace_101143
  have hstable : (prefixWord ++ tailWord_101143).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101143).length < 2 ^ (prefixWord ++ tailWord_101143).sum := by decide
  have hdescent : baseEnd_101143 < baseStart_101143 := by decide
  rcases family_descends (prefixWord ++ tailWord_101143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101183 : List Nat := [1, 1, 2, 2, 5, 1, 1, 6]
def baseStart_101183 : Nat := 118140960795 + 101183 * 2 ^ 59
def prefixEnd_101183 : Nat := 4983230072969 + 3 ^ 40 * 101183 * 2
def baseEnd_101183 : Nat := 30788452186063913924251

theorem tailTrace_101183 : CollatzResearch.WordTrace tailWord_101183 prefixEnd_101183 30788452186063913924251 := by
  unfold tailWord_101183
  simp only [CollatzResearch.WordTrace]
  refine ⟨3690447192438746525724203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2460298128292497683816135 3690447192438746525724203)
  ·
    refine ⟨5535670788658119788586305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3690447192438746525724203 5535670788658119788586305)
    ·
      refine ⟨4151753091493589841439729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5535670788658119788586305 4151753091493589841439729)
      ·
        refine ⟨3113814818620192381079797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4151753091493589841439729 3113814818620192381079797)
        ·
          refine ⟨291920139245643035726231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3113814818620192381079797 291920139245643035726231)
          ·
            refine ⟨437880208868464553589347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 291920139245643035726231 437880208868464553589347)
            ·
              refine ⟨656820313302696830384021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 437880208868464553589347 656820313302696830384021)
              ·
                refine ⟨30788452186063913924251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 656820313302696830384021 30788452186063913924251)
                ·
                  rfl

theorem cell19_101183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 6].length) (baseStart_101183 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_101183 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_101183 prefixEnd_101183 := by exact prefixLift 101183
  have htrace : WordTrace (prefixWord ++ tailWord_101183) baseStart_101183 baseEnd_101183 := by
    simpa [prefixWord, tailWord_101183, baseEnd_101183] using wordTrace_append hprefix tailTrace_101183
  have hstable : (prefixWord ++ tailWord_101183).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101183).length < 2 ^ (prefixWord ++ tailWord_101183).sum := by decide
  have hdescent : baseEnd_101183 < baseStart_101183 := by decide
  rcases family_descends (prefixWord ++ tailWord_101183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan19Incremental
